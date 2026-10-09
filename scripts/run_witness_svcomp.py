#!/usr/bin/env python3
"""Run an auditable, bounded unreach-call witness batch on original SV-COMP tasks.

Requires PyYAML for SV-COMP task files. Sources are never rewritten. Selection
uses the smallest inputs in each requested family and is recorded before runs.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

import yaml

from c2btor_solver import ric3_command
from c2btor_model_contract import unsat_status, property_model, boundary_status


ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts/c2btor_witness.py"
DEFAULT_FAMILIES = ["loops", "loop-acceleration", "loops-crafted-1",
                    "loop-invariants", "loop-invgen", "loop-crafted",
                    "bitvector", "bitvector-regression", "array-fpi",
                    "array-industry-pattern", "array-examples", "ldv-regression",
                    "recursive-simple", "floats-cdfpl"]


def process_tree(pid):
    table = subprocess.run(["ps", "-axo", "pid=,ppid=,rss="], capture_output=True,
                           text=True, check=True).stdout
    rows = [tuple(map(int, row.split())) for row in table.splitlines() if row.strip()]
    descendants = {pid}
    while True:
        expanded = descendants | {p for p, parent, _ in rows if parent in descendants}
        if expanded == descendants:
            break
        descendants = expanded
    return descendants, sum(rss for p, _, rss in rows if p in descendants)


def run(command, directory, name, timeout, memory_gib):
    command = [str(arg) for arg in command]
    (directory / (name + ".command.json")).write_text(json.dumps(command, indent=2))
    start = time.monotonic()
    peak = 0
    status = "finished"
    with (directory / (name + ".stdout")).open("w") as out, \
            (directory / (name + ".stderr")).open("w") as err:
        process = subprocess.Popen(command, stdout=out, stderr=err, cwd=ROOT,
                                   start_new_session=True)
        while process.poll() is None:
            descendants, rss = process_tree(process.pid)
            peak = max(peak, rss)
            if rss > memory_gib * 1024 * 1024:
                status = "memory_limit"
            elif time.monotonic() - start > timeout:
                status = "timeout"
            if status != "finished":
                # Tool wrappers start separate sessions; stop all descendants,
                # including the Java validator and model-checker workers.
                for pid in sorted(descendants, reverse=True):
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                break
            time.sleep(0.2)
        code = process.wait()
    return {"status": status, "returncode": code,
            "seconds": round(time.monotonic() - start, 3), "peak_rss_kib": peak}


def select_tasks(args):
    root = args.benchmarks.resolve()
    if args.tasks_file:
        paths = [root / line.strip() for line in args.tasks_file.read_text().splitlines()
                 if line.strip() and not line.lstrip().startswith("#")]
        groups = [paths]
    else:
        groups = [sorted((root / family).glob("*.yml")) for family in args.families]
    tasks = []
    for paths in groups:
        candidates = []
        for path in paths:
            task = yaml.safe_load(path.read_text())
            properties = [p for p in task["properties"]
                          if p["property_file"].endswith("unreach-call.prp")
                          and p.get("expected_verdict") is (args.expected_verdict == "true")]
            inputs = task["input_files"]
            inputs = [inputs] if isinstance(inputs, str) else inputs
            if not properties or len(inputs) != 1:
                continue
            source = (path.parent / inputs[0]).resolve()
            if not source.is_file():
                continue
            candidates.append({"task": str(path.relative_to(root)),
                               "source": str(source), "bytes": source.stat().st_size,
                               "property": str((path.parent / properties[0]["property_file"]).resolve()),
                               "data_model": task.get("options", {}).get("data_model", task.get("data_model")),
                               "expected_verdict": properties[0]["expected_verdict"]})
        candidates.sort(key=lambda task: (task["bytes"], task["task"]))
        tasks.extend(candidates if args.tasks_file else candidates[:args.per_family])
    return tasks


def execute(task, args):
    directory = args.output_dir / Path(task["task"]).with_suffix("")
    directory.mkdir(parents=True)
    result = dict(task, directory=str(directory), backend=args.backend, stages={})

    def stage(name, command, timeout):
        outcome = run(command, directory, name, timeout, args.memory_gib)
        result["stages"][name] = outcome
        if outcome["status"] != "finished":
            result["status"] = name + "_" + outcome["status"]
            return False
        if outcome["returncode"]:
            result["status"] = name + "_error"
            return False
        return True

    model = directory / "export"
    command = [sys.executable, TOOL, "export", "--c2btor", args.cbmc,
               "--program", task["source"], "--spec", task["property"],
               "--output-dir", model, "--timeout", str(args.conversion_timeout),
               "--", "--32" if task["data_model"] == "ILP32" else "--64",
               *args.cbmc_arg]
    if not stage("conversion", command, args.conversion_timeout + 5):
        return result
    if args.backend == "btormc":
        command = [args.btormc, "--bound-max=" + str(args.max_bound),
                   "--trace-gen-full", model / "model.btor2"]
    else:
        command = ric3_command(args.ric3, model / "model.btor2", args.engine,
                               args.solver_timeout, args.max_bound)
    if not stage("solver", command, args.solver_timeout + 5):
        return result
    solver_output = (directory / "solver.stdout").read_text()
    if re.search(r"^unsat$", solver_output, re.M | re.I):
        classification = unsat_status(model / "model.btor2", args.engine if args.backend == "ric3" else "bmc", all_properties=args.backend == "ric3" and args.engine != "portfolio")
        if classification == "full_check_required":
            complete = directory / "complete.btor2"
            indices = property_model(model / "model.btor2", complete)
            query = [str(complete) if str(value) == str(model / "model.btor2") else value for value in command]
            if not stage("complete_solver", query, args.solver_timeout + 5):
                return result
            classification = boundary_status((directory / "complete_solver.stdout").read_text(), indices,
                                             args.engine if args.backend == "ric3" else "bmc")
            if classification == "complete_model":
                # The merged query has no original property numbering. Probe
                # auxiliary faults separately; otherwise retain the additional
                # source violation as a candidate, not a confirmed witness.
                classification = "boundary_check_required"
        if classification == "boundary_check_required":
            probe = directory / "boundary.btor2"
            indices = property_model(model / "model.btor2", probe, boundaries_only=True)
            query = [str(probe) if str(value) == str(model / "model.btor2") else value for value in command]
            if not stage("boundary_solver", query, args.solver_timeout + 5):
                return result
            classification = boundary_status((directory / "boundary_solver.stdout").read_text(), indices,
                                            args.engine if args.backend == "ric3" else "bmc")
            if "complete_solver" in result["stages"] and classification in {"model_unsat", "bounded_no_violation"}:
                classification = "additional_property_violation"
        result["status"] = classification
        return result
    if not re.search(r"^sat$", solver_output, re.M | re.I):
        result["status"] = "solver_unknown"
        return result
    translation = directory / "translation"
    if not stage("translation", [sys.executable, TOOL, "translate", "--model", model / "model.btor2",
                 "--map", model / "model.map.json", "--witness", directory / "solver.stdout",
                 "--btorsim", args.btorsim, "--output-dir", translation,
                 "--timeout", "20"], 25):
        classification = translation / "result.json"
        if classification.is_file():
            details = json.loads(classification.read_text())
            if details.get("status") in {"model_limit", "memory_validity"}:
                result["status"] = details["status"]
        return result
    command = [sys.executable, TOOL, "validate", "--witness", translation / "witness.yml",
               "--cpachecker", args.cpachecker, "--output-dir", directory / "validation",
               "--solver", args.validator_solver, "--no-floats",
               "--timeout", str(args.validation_timeout)]
    if not stage("validation", command, args.validation_timeout + 20):
        outcome_file = directory / "validation/result.json"
        if outcome_file.is_file():
            verdict = json.loads(outcome_file.read_text()).get("validator_verdict")
            result["status"] = {"TRUE": "validation_rejected",
                                "UNKNOWN": "validation_unknown",
                                "TIMEOUT": "validation_timeout"}.get(verdict, result["status"])
        return result
    validation = json.loads((directory / "validation/result.json").read_text())
    result["status"] = "confirmed" if validation["status"] == "confirmed" else "not_confirmed"
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmarks", type=Path, required=True, help="sv-benchmarks/c directory")
    parser.add_argument("--c2btor", "--cbmc", dest="cbmc", metavar="C2BTOR", type=Path, required=True)
    for tool in ("ric3", "btorsim", "cpachecker"):
        parser.add_argument("--" + tool, type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--families", nargs="+", default=DEFAULT_FAMILIES)
    parser.add_argument("--per-family", type=int, default=5)
    parser.add_argument("--tasks-file", type=Path)
    parser.add_argument("--expected-verdict", choices=("true", "false"), default="false",
                        help="select safe tasks for false-alarm witness audits, or unsafe tasks (default)")
    parser.add_argument("--c2btor-arg", "--cbmc-arg", dest="cbmc_arg", metavar="ARG", action="append", default=[],
                        help="extra C2BTOR argument; use --c2btor-arg=-I/path for local include paths")
    parser.add_argument("--workers", type=int, default=2, choices=(1, 2))
    parser.add_argument("--memory-gib", type=float, default=4)
    parser.add_argument("--conversion-timeout", type=int, default=20)
    parser.add_argument("--solver-timeout", type=int, default=15)
    parser.add_argument("--validation-timeout", type=int, default=25)
    parser.add_argument("--max-bound", type=int, default=400)
    parser.add_argument("--engine", choices=("bmc", "ic3", "kind", "wl-bmc", "wl-kind", "portfolio"), default="bmc")
    parser.add_argument("--backend", choices=("ric3", "btormc"), default="ric3")
    parser.add_argument("--btormc", type=Path)
    parser.add_argument("--validator-solver", default="PRINCESS")
    args = parser.parse_args()
    if args.backend == "btormc" and args.btormc is None:
        parser.error("--backend btormc requires --btormc")
    # Fail before launching children if this environment forbids process-table
    # access, rather than losing memory supervision halfway through a run.
    process_tree(os.getpid())
    args.output_dir = args.output_dir.resolve()
    args.output_dir.mkdir(parents=True, exist_ok=False)
    for tool in ("cbmc", "ric3", "btorsim", "cpachecker"):
        setattr(args, tool, getattr(args, tool).resolve())
    if args.btormc:
        args.btormc = args.btormc.resolve()
    tasks = select_tasks(args)
    (args.output_dir / "run.json").write_text(json.dumps(
        {key: str(value) if isinstance(value, Path) else value
         for key, value in vars(args).items()}, indent=2))
    (args.output_dir / "manifest.json").write_text(json.dumps(tasks, indent=2))
    results = []
    print(f"Selected {len(tasks)} original tasks; artifacts: {args.output_dir}", flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(execute, task, args): task for task in tasks}
        for future in as_completed(futures):
            task = futures[future]
            try:
                result = future.result()
            except Exception as error:
                result = dict(task, status="runner_error", error=str(error))
            results.append(result)
            results.sort(key=lambda result: result["task"])
            (args.output_dir / "results.json").write_text(json.dumps(results, indent=2))
            print(f"[{len(results)}/{len(tasks)}] {result['task']}: {result['status']}", flush=True)
    with (args.output_dir / "summary.csv").open("w") as out:
        writer = csv.DictWriter(out, fieldnames=["task", "data_model", "expected_verdict", "status"])
        writer.writeheader()
        writer.writerows({key: r[key] for key in writer.fieldnames} for r in results)
    counts = {status: sum(r["status"] == status for r in results)
              for status in sorted({r["status"] for r in results})}
    print(json.dumps(counts, indent=2))


if __name__ == "__main__":
    main()
