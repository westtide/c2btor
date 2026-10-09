#!/usr/bin/env python3
"""
Run rIC3 on BTOR2 files. Logs per-case to sv-log/ric3/<folder>/<case>.log.

Usage:
  python3 test/tools/run_ric3.py \
    --ric3 ric3 \
    --btor-root test/sv_btor2 \
    --yaml-root test/sv_c \
    --timeout 100 \
    --limit -1
"""
import argparse
import csv
import os
import pathlib
import re
import signal
import shlex
import subprocess
import sys
import time

UNSAT_RE = re.compile(r"\bUNSAT\b", re.IGNORECASE)
SAT_RE = re.compile(r"\bSAT\b", re.IGNORECASE)

CBMC_STATUSES = {"timeout", "error", "empty_output", "conversion_error"}

MEM_LIMIT_MB = 8 * 1024


sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "scripts"))
from c2btor_model_contract import property_model, read_contract, solver_verdict
from c2btor_solver import ric3_command


def parse_args():
    parser = argparse.ArgumentParser(description="Run rIC3 on BTOR2 files.")
    parser.add_argument("--ric3", default="ric3", help="ric3 binary path")
    parser.add_argument("--btor-root", default="test/sv_btor2", help="BTOR2 root dir")
    parser.add_argument("--yaml-root", default="test/sv_c", help="YAML root dir for labels")
    parser.add_argument("--log-root", default="sv-log/ric3", help="Log output root")
    parser.add_argument("--data-root", default="test/ric3_data", help="CSV output root")
    parser.add_argument("--timeout", type=int, default=100, help="rIC3 timeout per file (default: 100)")
    parser.add_argument("--engine", default="portfolio", help="rIC3 engine (default: portfolio)")
    parser.add_argument("--limit", type=int, default=-1, help="Max files (-1=all)")
    parser.add_argument("--cases-file", default=None, help="File listing cases relative to btor-root")
    parser.add_argument("--mem-limit-gb", type=float, default=8.0, help="Memory limit GB (default: 8)")
    return parser.parse_args()


def load_label(yml_path):
    if not os.path.exists(yml_path):
        return None
    try:
        import yaml
        with open(yml_path) as f:
            data = yaml.safe_load(f)
        if isinstance(data, dict):
            props = data.get("properties", [])
            if isinstance(props, list):
                for p in props:
                    if isinstance(p, dict) and "unreach-call" in p.get("property_file", ""):
                        v = p.get("expected_verdict")
                        if isinstance(v, bool):
                            return "true" if v else "false"
                        if isinstance(v, str) and v.lower() in ("true", "false"):
                            return v.lower()
            for p in (props if isinstance(props, list) else []):
                if isinstance(p, dict):
                    v = p.get("expected_verdict")
                    if isinstance(v, bool):
                        return "true" if v else "false"
            v = data.get("expected_verdict")
            if isinstance(v, bool):
                return "true" if v else "false"
    except Exception:
        pass

    try:
        current_prop = None
        fallback = None
        with open(yml_path) as f:
            for line in f:
                s = line.strip()
                if "property_file:" in s:
                    current_prop = s.split("property_file:", 1)[1].strip().strip("'\"")
                if s.startswith("expected_verdict:"):
                    val = s.split(":", 1)[1].strip().lower()
                    if val in ("true", "false"):
                        if current_prop and "unreach-call" in current_prop:
                            return val
                        if fallback is None:
                            fallback = val
        return fallback
    except Exception:
        return None


def parse_ric3_output(text):
    return solver_verdict(text)


def get_tree_rss_mb(pid):
    try:
        out = subprocess.check_output(
            f"ps -o rss= -p {pid} 2>/dev/null; "
            f"pgrep -P {pid} 2>/dev/null | xargs -I{{}} ps -o rss= -p {{}} 2>/dev/null",
            shell=True, text=True
        ).strip().split("\n")
        return sum(int(x) for x in out if x.strip().isdigit()) // 1024
    except Exception:
        return 0


def judge(label, ric3_result, cbmc_status=None):
    if cbmc_status and cbmc_status in CBMC_STATUSES:
        return "btor_error"
    if ric3_result == "OOT":
        return "oot"
    if ric3_result == "unknown":
        return "unknown"
    if label == "true" and ric3_result == "unsat":
        return "TT"
    if label == "true" and ric3_result == "sat":
        return "TF"
    if label == "false" and ric3_result == "unsat":
        return "FT"
    if label == "false" and ric3_result == "sat":
        return "FF"
    return "unknown"


def run_one(ric3_bin, btor_path, log_path, timeout_sec, mem_limit_mb, engine="portfolio"):
    original = btor_path
    _, known, obligations = read_contract(original)
    if known:
        prepared = log_path.with_suffix(".verification.btor2")
        prepared.parent.mkdir(parents=True, exist_ok=True)
        property_model(original, prepared)
        btor_path = str(prepared)
    cmd = ric3_command(ric3_bin, btor_path, engine, timeout_sec)
    log_path.parent.mkdir(parents=True, exist_ok=True)

    with open(log_path, "w") as logf:
        logf.write(f"CMD: {shlex.join(cmd)}\n")
        logf.write(f"BTOR2: {btor_path}\n")
        logf.write(f"Started: {time.ctime()}\n\n")
        logf.flush()

        t0 = time.monotonic()
        mem_peak = 0
        oom = False

        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=logf, stderr=logf)

        while True:
            rc = proc.poll()
            if rc is not None:
                break
            elapsed = time.monotonic() - t0
            if elapsed > timeout_sec + 30:
                break
            mb = get_tree_rss_mb(proc.pid)
            if mb > mem_peak:
                mem_peak = mb
            if mb > mem_limit_mb:
                oom = True
                break
            time.sleep(2)

        elapsed = time.monotonic() - t0

        if proc.poll() is None:
            proc.kill()
            proc.wait()

        logf.write(f"\nEXIT: {proc.returncode}\n")
        logf.write(f"Elapsed: {elapsed:.1f}s\n")
        logf.write(f"MemPeak: {mem_peak}MB\n")
        logf.flush()

    if oom:
        return "OOT", elapsed, mem_peak

    rc = proc.returncode
    if rc is None or (elapsed > timeout_sec and rc != 0):
        return "OOT", elapsed, mem_peak

    try:
        text = log_path.read_text(encoding="utf-8", errors="replace")
    except Exception:
        text = ""

    result = parse_ric3_output(text) if rc == 0 else "unknown"
    # New memory models carry auxiliary bad properties. The legacy runner
    # requests no trace, so SAT alone cannot identify a C source violation.
    if result == "unsat" and (not known or engine in {"bmc", "wl-bmc"}):
        result = "unknown"
    if result == "sat" and obligations:
        result = "unknown"
    if result == "sat":
        with open(original, encoding="utf-8") as model:
            if any(re.match(r"^\d+ bad \d+ (?:model_limit|memory_validity)_", line)
                   for line in model):
                result = "unknown"
                with log_path.open("a") as output:
                    output.write("\nSAT includes auxiliary memory properties; use run_witness_svcomp.py to classify the trace.\n")
    return result, elapsed, mem_peak


def find_btor2_files(root):
    files = []
    for dirpath, _, filenames in os.walk(root):
        for name in filenames:
            if name.endswith(".btor2"):
                p = os.path.join(dirpath, name)
                if os.path.getsize(p) > 0:
                    files.append(p)
    files.sort()
    return files


def load_btor2_from_cases(cases_file, btor_root):
    files = []
    missing = []
    seen = set()
    with open(cases_file) as f:
        for raw in f:
            rel = raw.strip().replace("\\", "/")
            if not rel or rel.startswith("#"):
                continue
            p = pathlib.PurePosixPath(rel)
            if p.suffix.lower() in (".c", ".i"):
                rel = str(p.with_suffix(".btor2"))
            elif p.suffix.lower() != ".btor2":
                rel += ".btor2"
            if rel in seen:
                continue
            seen.add(rel)
            full = os.path.join(btor_root, rel)
            if os.path.exists(full) and os.path.getsize(full) > 0:
                files.append(full)
            else:
                missing.append(rel)
    return files, missing


def main():
    args = parse_args()
    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))

    btor_root = args.btor_root if os.path.isabs(args.btor_root) else os.path.join(repo_root, args.btor_root)
    yaml_root = args.yaml_root if os.path.isabs(args.yaml_root) else os.path.join(repo_root, args.yaml_root)
    log_root = args.log_root if os.path.isabs(args.log_root) else os.path.join(repo_root, args.log_root)
    data_root = args.data_root if os.path.isabs(args.data_root) else os.path.join(repo_root, args.data_root)
    ric3_bin = args.ric3 if os.path.isabs(args.ric3) else os.path.join(repo_root, args.ric3)

    os.makedirs(log_root, exist_ok=True)
    os.makedirs(data_root, exist_ok=True)

    if args.cases_file:
        btor_files, missing = load_btor2_from_cases(args.cases_file, btor_root)
        if missing:
            print(f"[warn] {len(missing)} missing cases", file=sys.stderr)
    else:
        btor_files = find_btor2_files(btor_root)

    if not btor_files:
        print(f"No btor2 files in {btor_root}", file=sys.stderr)
        return 2

    if args.limit >= 0:
        btor_files = btor_files[:args.limit]

    total = len(btor_files)
    mem_limit_mb = int(args.mem_limit_gb * 1024)

    stamp = time.strftime("%Y%m%d_%H%M%S")
    csv_path = os.path.join(data_root, f"ric3_{stamp}.csv")

    counts = {"TT": 0, "TF": 0, "FT": 0, "FF": 0, "btor_error": 0, "unknown": 0, "oot": 0}

    with open(csv_path, "w", newline="") as cf:
        writer = csv.writer(cf)
        writer.writerow(["case", "folder", "label", "cbmc_status", "ric3_result", "judgment",
                          "time_s", "mem_mb", "log_path"])
        cf.flush()

        for idx, btor_path in enumerate(btor_files, 1):
            rel = os.path.relpath(btor_path, btor_root)
            case = os.path.splitext(os.path.basename(rel))[0]
            rel_dir = os.path.dirname(rel)
            folder = rel_dir if rel_dir else os.path.basename(btor_root)

            yml_path = os.path.join(yaml_root, os.path.splitext(rel)[0] + ".yml")
            label = load_label(yml_path) or ""

            case_log = os.path.join(log_root, folder, case + ".log")

            cbmc_status = ""
            ric3_result, elapsed, mem_peak = run_one(ric3_bin, btor_path, pathlib.Path(case_log),
                                                       args.timeout, mem_limit_mb, args.engine)
            j = judge(label, ric3_result, cbmc_status)
            counts[j] = counts.get(j, 0) + 1

            print(f"[{idx}/{total}] {elapsed:6.1f}s {ric3_result:<8} mem={mem_peak:>5}MB {label:<6} {j:<4} {case}",
                  flush=True)

            writer.writerow([case, folder, label, cbmc_status, ric3_result, j,
                             f"{elapsed:.1f}", mem_peak, case_log])
            cf.flush()

    solved = counts["TT"] + counts["TF"] + counts["FT"] + counts["FF"]
    print(f"\n=== Summary ===")
    print(f"Solved: {solved}/{total}  TT:{counts['TT']} TF:{counts['TF']} FT:{counts['FT']} FF:{counts['FF']}")
    print(f"OOT: {counts['oot']}  Unknown: {counts['unknown']}  btor_error: {counts['btor_error']}")
    print(f"CSV: {csv_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
