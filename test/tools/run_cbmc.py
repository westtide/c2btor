#!/usr/bin/env python3
"""
Run CBMC on a fixed list of C cases and write CSV results with label comparison.

Example:
  python3 test/tools/run_cbmc.py \
    --cases-file test/sv_runs/baseline_0_299_cases.txt \
    --src-root test/sv_c \
    --yaml-root /path/to/sv-benchmarks/c \
    --cbmc-args "--pointer-check --bounds-check --pointer-primitive-check --pointer-overflow-check --built-in-assertions" \
    --timeout 30 \
    --output cbmc_0_299.csv
"""

import argparse
import concurrent.futures
import csv
import datetime
import os
import pathlib
import re
import shlex
import subprocess
import sys
import time


SUCCESS_RE = re.compile(r"\bVERIFICATION SUCCESSFUL\b", re.IGNORECASE)
FAILED_RE = re.compile(r"\bVERIFICATION FAILED\b", re.IGNORECASE)
UNKNOWN_PLACEHOLDER = "[Unknown]"


def normalize_subprocess_output(value):
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value


def resolve_repo_or_test_path(path, *, repo_root, test_dir):
    if os.path.isabs(path):
        return path
    cand_test = os.path.join(test_dir, path)
    if os.path.isdir(cand_test) or os.path.isfile(cand_test):
        return cand_test
    return os.path.join(repo_root, path)


def add_timestamp(path, stamp):
    base, ext = os.path.splitext(path)
    if ext:
        return f"{base}_{stamp}{ext}"
    return f"{path}_{stamp}"


def expected_result_from_label(label):
    if label == "true":
        return "unsat"
    if label == "false":
        return "sat"
    return ""


def compare_label_and_result(label, result):
    if label not in ("true", "false"):
        return "n/a"
    if result not in ("sat", "unsat"):
        return "n/a"
    return "match" if expected_result_from_label(label) == result else "mismatch"


def parse_expected_verdict_fallback(yml_path):
    try:
        current_property = None
        fallback_verdict = None
        with open(yml_path, "r", encoding="utf-8") as f:
            for line in f:
                line_s = line.strip()
                if "property_file:" in line_s:
                    _, value = line_s.split("property_file:", 1)
                    current_property = value.strip().strip("'\"")
                    continue
                if line_s.startswith("expected_verdict:"):
                    _, value = line_s.split(":", 1)
                    verdict_l = value.strip().lower()
                    if verdict_l in ("true", "false"):
                        if (
                            isinstance(current_property, str)
                            and current_property.endswith("unreach-call.prp")
                        ):
                            return verdict_l
                        if fallback_verdict is None:
                            fallback_verdict = verdict_l
    except Exception:
        return None
    return fallback_verdict


def load_expected_verdict(yml_path):
    if not os.path.exists(yml_path):
        return None
    try:
        import yaml  # type: ignore
    except Exception:
        return parse_expected_verdict_fallback(yml_path)
    try:
        with open(yml_path, "r", encoding="utf-8") as f:
            data = yaml.safe_load(f)
    except Exception:
        return parse_expected_verdict_fallback(yml_path)
    if not isinstance(data, dict):
        return None

    props = data.get("properties")
    if isinstance(props, list):
        for prop in props:
            if not isinstance(prop, dict):
                continue
            prop_file = prop.get("property_file", "")
            if isinstance(prop_file, str) and prop_file.endswith("unreach-call.prp"):
                verdict = prop.get("expected_verdict")
                if isinstance(verdict, bool):
                    return "true" if verdict else "false"
                if isinstance(verdict, str):
                    verdict_l = verdict.strip().lower()
                    if verdict_l in ("true", "false"):
                        return verdict_l
        for prop in props:
            if not isinstance(prop, dict):
                continue
            verdict = prop.get("expected_verdict")
            if isinstance(verdict, bool):
                return "true" if verdict else "false"
            if isinstance(verdict, str):
                verdict_l = verdict.strip().lower()
                if verdict_l in ("true", "false"):
                    return verdict_l

    verdict = data.get("expected_verdict")
    if isinstance(verdict, bool):
        return "true" if verdict else "false"
    if isinstance(verdict, str):
        verdict_l = verdict.strip().lower()
        if verdict_l in ("true", "false"):
            return verdict_l
    return None


def _normalize_case_to_c(rel_case):
    rel = rel_case.strip().replace("\\", "/")
    if not rel or rel.startswith("#"):
        return ""
    suffix = pathlib.PurePosixPath(rel).suffix.lower()
    if suffix == ".btor2":
        return str(pathlib.PurePosixPath(rel).with_suffix(".c"))
    if suffix not in (".c", ".i"):
        return rel + ".c"
    return rel


def load_c_files_from_cases(cases_file, src_root):
    files = []
    seen = set()
    missing = []
    with open(cases_file, "r", encoding="utf-8") as f:
        for raw in f:
            rel = _normalize_case_to_c(raw)
            if not rel:
                continue
            if rel in seen:
                continue
            seen.add(rel)
            full = os.path.join(src_root, rel)
            if os.path.isfile(full):
                files.append((rel, full))
            else:
                missing.append(rel)
    return files, missing


def parse_result_from_output(output_text):
    saw_success = False
    saw_failed = False
    for line in output_text.splitlines():
        if SUCCESS_RE.search(line):
            saw_success = True
        if FAILED_RE.search(line):
            saw_failed = True
    if saw_failed:
        return "sat"
    if saw_success:
        return "unsat"
    return "unknown"


def run_cbmc_capture(cmd, timeout_sec):
    start = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout_sec,
        )
        output = proc.stdout or ""
        result = parse_result_from_output(output)
        return result, proc.returncode, time.monotonic() - start, output
    except subprocess.TimeoutExpired as exc:
        output = (
            normalize_subprocess_output(exc.stdout)
            + normalize_subprocess_output(exc.stderr)
        ).rstrip() + "\n<TIMEOUT>\n"
        return "OOT", 124, time.monotonic() - start, output


def run_one_case(case):
    idx = case["idx"]
    rel_path = case["rel_path"]
    src_path = case["src_path"]
    label = case["label"]
    expected_result = case["expected_result"]
    timeout_sec = case["timeout"]
    cbmc_bin = case["cbmc_bin"]
    cbmc_args = list(case["cbmc_args"])
    cmd = [cbmc_bin, src_path]
    if case["no_standard_checks"]:
        cmd.append("--no-standard-checks")
    cmd.extend(cbmc_args)
    cmd_str = " ".join(shlex.quote(c) for c in cmd)
    result, exit_code, elapsed, output = run_cbmc_capture(cmd, timeout_sec)
    comparison = compare_label_and_result(label, result)
    return {
        "idx": idx,
        "rel_path": rel_path,
        "label": label,
        "expected_result": expected_result,
        "result": result,
        "comparison": comparison,
        "exit_code": exit_code,
        "elapsed": elapsed,
        "cmd_str": cmd_str,
        "output": output,
    }


def resolve_cbmc_binary(cbmc_arg, repo_root):
    if cbmc_arg:
        return cbmc_arg
    cand = os.path.join(repo_root, "build", "bin", "cbmc")
    if os.path.isfile(cand):
        return cand
    return "cbmc"


def main():
    parser = argparse.ArgumentParser(
        description="Run CBMC on a fixed case list and compare with YAML labels."
    )
    parser.add_argument("--cases-file", required=True, help="Case list file (relative C paths).")
    parser.add_argument(
        "--src-root",
        default="test/sv_c",
        help="Root directory containing C files (default: test/sv_c).",
    )
    parser.add_argument(
        "--yaml-root",
        default="/path/to/sv-benchmarks/c",
        help="Root directory containing expected verdict .yml files.",
    )
    parser.add_argument("--cbmc", default=None, help="Path/command for cbmc.")
    parser.add_argument(
        "--cbmc-args",
        default="",
        help="Extra CBMC args passed to every case, for example: "
        '"--pointer-check --bounds-check --pointer-primitive-check --pointer-overflow-check --built-in-assertions"',
    )
    parser.add_argument(
        "--no-standard-checks",
        action="store_true",
        help="Disable CBMC standard checks (default: keep standard checks enabled).",
    )
    parser.add_argument("--timeout", type=int, default=30, help="Timeout per file (seconds).")
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="Number of parallel CBMC workers (default: 1).",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=-1,
        help="Run at most N files (-1 means all selected files).",
    )
    parser.add_argument(
        "--output",
        default="cbmc_svcomp_results.csv",
        help="Output CSV name or path.",
    )
    parser.add_argument(
        "--log",
        default=None,
        help="Output log path. Defaults to CSV base name with .log.",
    )
    args = parser.parse_args()

    script_dir = os.path.dirname(os.path.abspath(__file__))
    test_dir = os.path.dirname(script_dir)
    repo_root = os.path.dirname(test_dir)

    src_root = os.path.abspath(
        resolve_repo_or_test_path(args.src_root, repo_root=repo_root, test_dir=test_dir)
    )
    yaml_root = os.path.abspath(args.yaml_root)
    cases_file = os.path.abspath(
        resolve_repo_or_test_path(args.cases_file, repo_root=repo_root, test_dir=test_dir)
    )
    cbmc_bin = resolve_cbmc_binary(args.cbmc, repo_root)
    cbmc_args = shlex.split(args.cbmc_args)

    if not os.path.isdir(src_root):
        print(f"Missing src root: {src_root}", file=sys.stderr)
        return 2
    if not os.path.isfile(cases_file):
        print(f"Missing cases file: {cases_file}", file=sys.stderr)
        return 2
    if not os.path.isdir(yaml_root):
        print(f"Missing yaml root: {yaml_root}", file=sys.stderr)
        return 2

    files, missing = load_c_files_from_cases(cases_file, src_root)
    if not files:
        print("No C files selected from cases file.", file=sys.stderr)
        return 2
    if args.limit >= 0:
        files = files[: args.limit]
    total = len(files)

    stamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    data_dir = os.path.join(test_dir, "cbmc_data")
    log_dir = os.path.join(test_dir, "cbmc_log")
    os.makedirs(data_dir, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    if os.path.isabs(args.output):
        output_base = args.output
    else:
        output_base = os.path.join(data_dir, args.output)
    output_path = add_timestamp(os.path.abspath(output_base), stamp)

    if args.log:
        log_base = args.log if os.path.isabs(args.log) else os.path.join(log_dir, args.log)
        log_path = add_timestamp(os.path.abspath(log_base), stamp)
    else:
        log_name = os.path.splitext(os.path.basename(output_base))[0] + ".log"
        log_path = add_timestamp(os.path.join(log_dir, log_name), stamp)

    jobs = max(1, int(args.jobs))
    cases = []
    for idx, (rel_path, src_path) in enumerate(files, start=1):
        yml_rel = os.path.splitext(rel_path)[0] + ".yml"
        yml_path = os.path.join(yaml_root, yml_rel)
        label = load_expected_verdict(yml_path) or UNKNOWN_PLACEHOLDER
        cases.append(
            {
                "idx": idx,
                "rel_path": rel_path,
                "src_path": src_path,
                "label": label,
                "expected_result": expected_result_from_label(label),
                "timeout": args.timeout,
                "cbmc_bin": cbmc_bin,
                "cbmc_args": cbmc_args,
                "no_standard_checks": bool(args.no_standard_checks),
            }
        )

    results = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        future_map = {pool.submit(run_one_case, case): case for case in cases}
        done = 0
        for fut in concurrent.futures.as_completed(future_map):
            case = future_map[fut]
            done += 1
            try:
                res = fut.result()
            except Exception as exc:  # pragma: no cover (defensive)
                res = {
                    "idx": case["idx"],
                    "rel_path": case["rel_path"],
                    "label": case["label"],
                    "expected_result": case["expected_result"],
                    "result": "unknown",
                    "comparison": "n/a",
                    "exit_code": -1,
                    "elapsed": 0.0,
                    "cmd_str": " ".join(
                        shlex.quote(c)
                        for c in (
                            [cbmc_bin, case["src_path"]]
                            + (
                                ["--no-standard-checks"]
                                if case["no_standard_checks"]
                                else []
                            )
                            + list(case["cbmc_args"])
                        )
                    ),
                    "output": f"<runner_exception> {exc}",
                }
            results[res["idx"]] = res
            print(f"[{done}/{total}] {res['rel_path']}: {res['result']}", flush=True)

    compared = 0
    match = 0
    mismatch = 0
    timeouts = 0
    unknown = 0

    with open(output_path, "w", newline="", encoding="utf-8") as csvfile, open(
        log_path, "a", encoding="utf-8"
    ) as logfile:
        writer = csv.writer(csvfile)
        writer.writerow(
            [
                "filename",
                "label",
                "expected_result",
                "result",
                "comparison",
                "exit_code",
                "elapsed_sec",
                "command",
            ]
        )
        if missing:
            logfile.write(f"[warn] missing_sources={len(missing)}\n")
            for rel in missing:
                logfile.write(f"[warn] missing source: {rel}\n")

        for idx in sorted(results):
            res = results[idx]
            if res["comparison"] != "n/a":
                compared += 1
                if res["comparison"] == "match":
                    match += 1
                else:
                    mismatch += 1
            if res["result"] == "OOT":
                timeouts += 1
            elif res["result"] == "unknown":
                unknown += 1

            writer.writerow(
                [
                    res["rel_path"],
                    res["label"],
                    res["expected_result"],
                    res["result"],
                    res["comparison"],
                    res["exit_code"],
                    f"{res['elapsed']:.2f}",
                    res["cmd_str"],
                ]
            )

            logfile.write(f"=== {res['rel_path']} ===\n")
            logfile.write(f"label: {res['label']}\n")
            logfile.write(f"command: {res['cmd_str']}\n")
            logfile.write("STDOUT/STDERR:\n")
            logfile.write((res["output"] or "").rstrip() + "\n")
            logfile.write(f"\nresult: {res['result']}\n")
            logfile.write(
                f"expected_result: {res['expected_result'] or UNKNOWN_PLACEHOLDER}\n"
            )
            logfile.write(f"comparison: {res['comparison']}\n")
            logfile.write(f"exit_code: {res['exit_code']}\n")
            logfile.write(f"elapsed: {res['elapsed']:.2f}s\n\n")

        csvfile.flush()
        logfile.flush()

    print(f"Saved CSV: {output_path}")
    print(f"Saved log: {log_path}")
    print(f"Compared: {compared}  Match: {match}  Mismatch: {mismatch}")
    print(f"Timeouts: {timeouts}  Unknown: {unknown}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
