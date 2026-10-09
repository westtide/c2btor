#!/usr/bin/env python3
'''
python3 test/tools/run_pono.py \
  --pono /path/to/pono \
  --btor2-root test/sv_btor2 \
  --yaml-root /path/to/sv-benchmarks/c \
  --limit 100 \
  --timeout 30

python test/tools/run_pono.py --limit 100 --timeout 30
'''

import argparse
import csv
import hashlib
import os
import pathlib
import shutil
import signal
import subprocess
import sys
import tempfile
from datetime import datetime


sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "scripts"))
from c2btor_model_contract import property_model, read_contract


def parse_expected_verdict(yaml_path):
    try:
        import yaml  # type: ignore

        with open(yaml_path, "r", encoding="utf-8") as f:
            data = yaml.safe_load(f)
        if not isinstance(data, dict):
            return None
        props = data.get("properties")
        if not isinstance(props, list):
            return None
        for item in props:
            if isinstance(item, dict) and "expected_verdict" in item:
                val = item["expected_verdict"]
                if isinstance(val, bool):
                    return "true" if val else "false"
                if isinstance(val, str):
                    v = val.strip().lower()
                    if v in ("true", "false"):
                        return v
        return None
    except Exception:
        pass

    try:
        with open(yaml_path, "r", encoding="utf-8") as f:
            for line in f:
                if "expected_verdict" in line:
                    _, _, tail = line.partition(":")
                    v = tail.strip().lower()
                    if v.startswith("true"):
                        return "true"
                    if v.startswith("false"):
                        return "false"
        return None
    except Exception:
        return None


def find_yaml_for_btor2(btor2_path, btor2_root, yaml_root):
    rel = os.path.relpath(btor2_path, btor2_root)
    base, _ = os.path.splitext(rel)
    cand = os.path.join(yaml_root, base + ".yml")
    if os.path.exists(cand):
        return cand
    cand2 = os.path.join(yaml_root, base + ".yaml")
    if os.path.exists(cand2):
        return cand2
    return None


def _normalize_case_to_btor2(rel_case):
    rel = rel_case.strip().replace("\\", "/")
    if not rel or rel.startswith("#"):
        return ""
    suffix = pathlib.PurePosixPath(rel).suffix.lower()
    if suffix in (".c", ".i"):
        return str(pathlib.PurePosixPath(rel).with_suffix(".btor2"))
    if suffix != ".btor2":
        return rel + ".btor2"
    return rel


def load_btor2_files_from_cases(cases_file, btor2_root):
    files = []
    seen = set()
    missing = []
    with open(cases_file, "r", encoding="utf-8") as f:
        for raw in f:
            rel = _normalize_case_to_btor2(raw)
            if not rel:
                continue
            if rel in seen:
                continue
            seen.add(rel)
            full = os.path.join(btor2_root, rel)
            try:
                if os.path.getsize(full) > 0:
                    files.append(full)
                else:
                    missing.append(rel)
            except OSError:
                missing.append(rel)
    return files, missing


def parse_result(output_text):
    result = None
    for line in output_text.splitlines():
        s = line.strip()
        if s in ("sat", "unsat", "unknown"):
            result = s
    return result


def parse_invariant(output_text):
    inv = None
    for line in output_text.splitlines():
        if line.startswith("INVAR:"):
            inv = line[len("INVAR:"):].strip()
    return inv


def parse_output_file(path):
    result = None
    inv = None
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        for line in f:
            s = line.strip()
            if s in ("sat", "unsat", "unknown"):
                result = s
            if line.startswith("INVAR:"):
                inv = line[len("INVAR:"):].strip()
    return result, inv


def run_single(pono_bin, btor2_path, timeout_sec, log_f):
    _, known, obligations = read_contract(btor2_path)
    source = pathlib.Path(btor2_path).resolve()
    identity = hashlib.sha256(str(source).encode()).hexdigest()[:12]
    query = pathlib.Path(log_f.name).parent / (source.stem + "." + identity + ".verification.btor2")
    if known:
        property_model(btor2_path, query)
    cmd = [pono_bin, "-e", "ic3ia", "--show-invar", "--check-invar", str(query) if known else btor2_path]
    tmp = tempfile.NamedTemporaryFile(mode="w+", delete=False, encoding="utf-8")
    tmp_path = tmp.name

    proc = None
    timed_out = False
    try:
        proc = subprocess.Popen(
            cmd,
            stdout=tmp,
            stderr=tmp,
            start_new_session=True,
        )
        try:
            proc.wait(timeout=timeout_sec)
        except subprocess.TimeoutExpired:
            timed_out = True
            if proc and proc.pid:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            if proc:
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.wait()
    finally:
        tmp.flush()
        tmp.close()

    result, inv = parse_output_file(tmp_path)
    if timed_out:
        result = "OOT"
        inv = None
    else:
        result = (result or "unknown") if proc.returncode == 0 else "unknown"
        if result != "unsat":
            inv = None

    if (result == "unsat" and not known) or (result == "sat" and obligations):
        result, inv = "unknown", None

    log_f.write("STDOUT/STDERR:\n")
    with open(tmp_path, "r", encoding="utf-8", errors="replace") as out_f:
        shutil.copyfileobj(out_f, log_f)
    if not timed_out and proc is not None:
        exit_code = proc.returncode
    else:
        exit_code = None

    os.unlink(tmp_path)

    return {
        "cmd": cmd,
        "exit_code": exit_code,
        "result": result,
        "invariant": inv,
        "timed_out": timed_out,
    }


def add_timestamp(path, stamp):
    base, ext = os.path.splitext(path)
    if ext:
        return f"{base}_{stamp}{ext}"
    return f"{path}_{stamp}"


def resolve_path(path, default_dir):
    if os.path.isabs(path):
        return path
    return os.path.join(default_dir, path)

def resolve_repo_or_test_path(path, *, repo_root, test_dir):
    """
    Accept either:
      - paths relative to repo root (e.g. 'test/sv_btor2')
      - paths relative to test/      (e.g. 'sv_btor2')
    """
    if os.path.isabs(path):
        return path
    cand_test = os.path.join(test_dir, path)
    if os.path.isdir(cand_test) or os.path.isfile(cand_test):
        return cand_test
    cand_repo = os.path.join(repo_root, path)
    return cand_repo


def main():
    parser = argparse.ArgumentParser(description="Run pono on a sample of BTOR2 files.")
    parser.add_argument(
        "--limit",
        type=int,
        default=100,
        help="Number of files to run (-1 means all selected files)",
    )
    parser.add_argument("--timeout", type=int, default=30, help="Timeout per file (seconds)")
    parser.add_argument(
        "--pono",
        default=os.path.expanduser("~/Developer/pono/build/bin/pono"),
        help="Path to pono binary",
    )
    parser.add_argument(
        "--btor2-root",
        default=None,
        help="Root directory for BTOR2 files (defaults to test/sv_btor2)",
    )
    parser.add_argument(
        "--yaml-root",
        default="/path/to/sv-benchmarks/c",
        help="Root directory for YAML label files",
    )
    parser.add_argument(
        "--cases-file",
        default=None,
        help="Optional file listing cases to run (relative to --btor2-root).",
    )
    parser.add_argument(
        "--oot-limit",
        type=int,
        default=-1,
        help="Stop early after reaching this many OOT results (-1 disables).",
    )
    parser.add_argument("--output", default=None, help="Output CSV name or path")
    parser.add_argument("--out-csv", default=None, help="Output CSV path (overrides --output)")
    parser.add_argument("--out-log", default=None, help="Output log path")
    args = parser.parse_args()

    script_dir = os.path.dirname(os.path.abspath(__file__))
    test_dir = os.path.dirname(script_dir)
    repo_root = os.path.dirname(test_dir)
    if args.btor2_root:
        btor2_root = resolve_repo_or_test_path(args.btor2_root, repo_root=repo_root, test_dir=test_dir)
    else:
        btor2_root = os.path.join(test_dir, "sv_btor2")

    if not os.path.isfile(args.pono):
        print(f"pono not found: {args.pono}", file=sys.stderr)
        return 2
    if not os.path.isdir(btor2_root):
        print(f"btor2 root not found: {btor2_root}", file=sys.stderr)
        return 2
    if not os.path.isdir(args.yaml_root):
        print(f"yaml root not found: {args.yaml_root}", file=sys.stderr)
        return 2

    if args.cases_file:
        cases_file = resolve_repo_or_test_path(
            args.cases_file, repo_root=repo_root, test_dir=test_dir
        )
        if not os.path.isfile(cases_file):
            print(f"cases file not found: {cases_file}", file=sys.stderr)
            return 2
        btor2_files, missing_cases = load_btor2_files_from_cases(cases_file, btor2_root)
        if missing_cases:
            print(
                f"[warn] {len(missing_cases)} case(s) missing/empty under btor2 root; first: {missing_cases[0]}",
                file=sys.stderr,
            )
    else:
        btor2_files = []
        for root, _, files in os.walk(btor2_root):
            for name in files:
                if name.endswith(".btor2"):
                    path = os.path.join(root, name)
                    try:
                        if os.path.getsize(path) == 0:
                            continue
                    except OSError:
                        continue
                    btor2_files.append(path)
        btor2_files.sort()

    if args.limit >= 0:
        btor2_files = btor2_files[: args.limit]

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    data_dir = os.path.join(test_dir, "pono_data")
    log_dir = os.path.join(test_dir, "pono_log")
    os.makedirs(data_dir, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    out_csv_arg = args.out_csv or args.output
    if out_csv_arg:
        out_csv_base = resolve_path(out_csv_arg, data_dir)
        out_csv = add_timestamp(out_csv_base, timestamp)
    else:
        out_csv = os.path.join(data_dir, f"pono_batch_{timestamp}.csv")

    if args.out_log:
        out_log_base = resolve_path(args.out_log, log_dir)
        out_log = add_timestamp(out_log_base, timestamp)
    else:
        log_name = os.path.splitext(os.path.basename(out_csv))[0] + ".log"
        out_log = os.path.join(log_dir, log_name)

    with open(out_csv, "w", newline="", encoding="utf-8") as csv_f, open(
        out_log, "w", encoding="utf-8"
    ) as log_f:
        writer = csv.writer(csv_f)
        writer.writerow(["filename", "label", "result", "invariant"])
        oot_count = 0

        for idx, btor2_path in enumerate(btor2_files, start=1):
            rel = os.path.relpath(btor2_path, btor2_root)
            yaml_path = find_yaml_for_btor2(btor2_path, btor2_root, args.yaml_root)
            label = parse_expected_verdict(yaml_path) if yaml_path else None
            label_str = label if label is not None else "unknown"

            log_f.write(f"==== {rel} ====" + "\n")
            log_f.write("CMD: " + " ".join([args.pono, "-e", "ic3ia", "--show-invar", "--check-invar", btor2_path]) + "\n")

            res = run_single(args.pono, btor2_path, args.timeout, log_f)

            invariant = res["invariant"] or ""
            writer.writerow([rel, label_str, res["result"], invariant])
            if res["result"] == "OOT":
                oot_count += 1

            log_f.write("EXIT: " + ("timeout" if res["timed_out"] else str(res["exit_code"])) + "\n")

            # Flush on each iteration to avoid losing data on interruption.
            csv_f.flush()
            log_f.flush()

            print(f"[{idx}/{len(btor2_files)}] {rel}: {res['result']}")

            if args.oot_limit >= 0 and oot_count >= args.oot_limit:
                print(f"[stop] reached oot-limit={args.oot_limit}, stopping early.")
                log_f.write(f"\n[stop] reached oot-limit={args.oot_limit}, stopping early.\n")
                log_f.flush()
                break

    print(f"CSV: {out_csv}")
    print(f"LOG: {out_log}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
