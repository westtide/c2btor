#!/usr/bin/env python3
"""Record bounded conversion/parser evidence; never invoke a solver or checker."""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def save(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def bounded_command(command, data_gib):
    if not data_gib:
        return command
    # The sandbox disallows `ps`, so use an inherited per-process data limit.
    wrapper = ("import os,resource,sys; n=int(sys.argv[1]); "
               "resource.setrlimit(resource.RLIMIT_DATA,(n,n)); "
               "os.execv(sys.argv[2],sys.argv[2:])")
    return [sys.executable, "-c", wrapper, str(int(data_gib * 1024 ** 3)), *command]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c2btor", type=Path, default=ROOT / "build/bin/c2btor")
    parser.add_argument("--catbtor", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=HERE / "baseline/off")
    parser.add_argument("--architectures", default="32,64")
    parser.add_argument("--arrays", default="array")
    parser.add_argument("--case-filter", action="append", default=[])
    parser.add_argument("--feature-flag", action="append", default=[])
    parser.add_argument("--freeze-binary", action="store_true")
    parser.add_argument("--conversion-timeout", type=float, default=20)
    parser.add_argument("--parser-timeout", type=float, default=10)
    parser.add_argument("--memory-gib", type=float, default=0,
                        help="optional RLIMIT_DATA limit (0 disables; unsupported in this macOS sandbox)")
    parser.add_argument("--file-limit-mib", type=int, default=64)
    args = parser.parse_args()
    output = args.output.resolve()
    if not output.is_relative_to(HERE):
        parser.error("all output must be within test/c2btor_symbolic_heap")
    if output.exists():
        parser.error("output exists; choose a fresh output directory")
    if any(architecture not in {"32", "64"}
           for architecture in args.architectures.split(",")):
        parser.error("architectures must be 32 and/or 64")
    if any(array not in {"bv", "array", "mixed"}
           for array in args.arrays.split(",")):
        parser.error("arrays must be bv, array and/or mixed")
    output.mkdir(parents=True)
    binary = args.c2btor.resolve()
    if args.freeze_binary:
        frozen = output / "c2btor.frozen"
        shutil.copy2(binary, frozen)
        binary = frozen
    # Importing existing helpers must not write __pycache__ outside this folder.
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location(
        "c2btor_existing_regression_helpers", ROOT / "scripts/check_c2btor_optimizations.py")
    helpers = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helpers)
    manifest = json.loads((HERE / "cases.json").read_text())
    save(output / "run.json", {
        "scope": "conversion/parser/structural evidence only; no simulation, model checking or safety verdicts",
        "original_binary": str(args.c2btor.resolve()),
        "executed_binary": str(binary), "binary_sha256": helpers.digest(binary),
        "catbtor": str(args.catbtor.resolve()), "feature_flags": args.feature_flag,
        "architectures": args.architectures.split(","), "arrays": args.arrays.split(","),
        "memory_limit": {"kind": "RLIMIT_DATA" if args.memory_gib else "none",
                         "bytes": int(args.memory_gib * 1024 ** 3),
                         "rss_sampling": False},
        "manifest_sha256": helpers.digest(HERE / "cases.json")})
    version = helpers.run([binary, "--version"], output, "version", 5, 0)
    records = []
    for case in manifest["cases"]:
        if args.case_filter and not any(pattern in case["name"] for pattern in args.case_filter):
            continue
        for architecture in args.architectures.split(","):
            if architecture not in case["architectures"]:
                continue
            for array in args.arrays.split(","):
                directory = output / (case["name"] + "_" + architecture + "_" + array)
                directory.mkdir()
                model = directory / "model.btor2"
                mapping_path = directory / "model.map.json"
                source = (HERE / case["source"]).resolve()
                command = [binary, source, "--" + architecture,
                           *manifest["common_options"], "--array", array,
                           *args.feature_flag, "--goto-btor2-out", model,
                           "--goto-btor2-map-out", mapping_path]
                conversion = helpers.run(
                    bounded_command([str(value) for value in command], args.memory_gib),
                    directory, "conversion", args.conversion_timeout,
                    0, file_limit_mib=args.file_limit_mib)
                log = ((directory / "conversion.stdout").read_text() +
                       (directory / "conversion.stderr").read_text())
                record = {"case": case["name"], "architecture": architecture,
                          "array": array, "source": str(source),
                          "source_sha256": helpers.digest(source),
                          "conversion": conversion,
                          "model_exists": model.exists(),
                          "model_bytes": model.stat().st_size if model.exists() else 0,
                          "planned_final_expectation": case["expected_on"]}
                if conversion["status"] != "finished":
                    record["status"] = conversion["status"]
                elif conversion["returncode"]:
                    record["status"] = ("unsupported" if "Unsupported" in log or "unsupported" in log
                                        else "conversion_error")
                    record["diagnostic_tail"] = log.splitlines()[-12:]
                    record["failed_conversion_has_no_nonempty_model"] = not record["model_bytes"]
                elif not model.exists() or not model.stat().st_size:
                    record["status"] = "missing_model"
                else:
                    parsed = helpers.run(bounded_command(
                        [str(args.catbtor.resolve()), str(model)], args.memory_gib), directory,
                                         "parser", args.parser_timeout, 0,
                                         discard_stdout=True)
                    record["parser"] = parsed
                    record["status"] = ("convert_parse" if parsed["status"] == "finished" and
                                        parsed["returncode"] == 0 else "parser_failure")
                    mapping = json.loads(mapping_path.read_text()) if mapping_path.exists() else None
                    record["metrics"] = helpers.structural_metrics(model, log, mapping)
                    nodes = helpers.nodes_from(model)
                    record["bad_count"] = sum(node[0] == "bad" for node in nodes.values())
                    record["constraint_count"] = sum(node[0] == "constraint" for node in nodes.values())
                    record["source_property_count"] = (len(mapping.get("source_properties", []))
                                                        if mapping is not None else None)
                    record["source_only_bad_count_matches"] = (
                        record["bad_count"] == 1 and
                        record["source_property_count"] == case["expected_source_properties"])
                save(directory / "case.result.json", record)
                records.append(record)
                print(f"{case['name']} --{architecture} {array}: {record['status']}", flush=True)
                save(output / "results.json", records)
    save(output / "summary.json", {
        "scope": "conversion/parser/structural evidence only; no model checking or safety verdicts",
        "version_result": version, "case_runs": len(records),
        "status_counts": {status: sum(record["status"] == status for record in records)
                          for status in sorted({record["status"] for record in records})},
        "successful_property_count_mismatches": [
            {"case": record["case"], "architecture": record["architecture"], "array": record["array"]}
            for record in records if record["status"] == "convert_parse" and
            not record["source_only_bad_count_matches"]]})


if __name__ == "__main__":
    main()
