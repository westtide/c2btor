#!/usr/bin/env python3

import argparse
import csv
import fcntl
import gc
import os
import re
import selectors as sel_mod
import signal
import subprocess
import sys
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent

VALID_TOOLS = [
    "aise",
    "bubaak",
    "cpachecker",
    "esbmc",
    "symbiotic",
    "uautomizer",
    "veriabs",
]

TOOL_BINARIES = {
    "aise": SCRIPT_DIR / "aise" / "bin" / "aise",
    "bubaak": SCRIPT_DIR / "bubaak" / "bubaak",
    "cpachecker": SCRIPT_DIR / "cpachecker" / "bin" / "cpachecker",
    "esbmc": SCRIPT_DIR / "esbmc-kind" / "esbmc",
    "symbiotic": SCRIPT_DIR / "symbiotic" / "bin" / "symbiotic",
    "uautomizer": SCRIPT_DIR / "UAutomizer" / "Ultimate.py",
    "veriabs": SCRIPT_DIR / "VeriAbsL" / "scripts" / "veriabs",
}

SPEC_FILE = SCRIPT_DIR / "symbiotic" / "properties" / "unreach-call.prp"

VALID_STATUS = {"TRUE", "FALSE", "UNKNOWN", "TIMEOUT", "ERROR", "UNSUPPORTED"}

DEFAULT_TIMEOUT = 900


def parse_args():
    parser = argparse.ArgumentParser(
        description="Run verification tools against manifest.csv (SLURM-friendly)."
    )
    parser.add_argument("--tool", required=True, choices=VALID_TOOLS, help="Tool to run.")
    parser.add_argument("--manifest", type=Path, default=SCRIPT_DIR / "manifest.csv", help="Manifest CSV.")
    parser.add_argument("--start-id", type=int, default=1, help="First case id (inclusive).")
    parser.add_argument("--end-id", type=int, default=None, help="Last case id (inclusive).")
    parser.add_argument("--output-dir", type=Path, default=SCRIPT_DIR / "output", help="Output root.")
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT, help="Per-case timeout seconds.")
    return parser.parse_args()


def load_manifest(path):
    with path.open("r", newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def select_rows(rows, start_id, end_id):
    out = []
    for r in rows:
        rid = int(r["id"])
        if rid < start_id:
            continue
        if end_id is not None and rid > end_id:
            continue
        out.append(r)
    return out


def build_command(tool, source_file, architecture, spec_file, timeout_sec=900):
    source = str(source_file)
    spec = str(spec_file)

    if tool == "aise":
        arch_flag = "--32" if architecture == "32bit" else "--64"
        return [str(TOOL_BINARIES["aise"]), arch_flag, source]

    if tool == "bubaak":
        return [str(TOOL_BINARIES["bubaak"]), source]

    if tool == "cpachecker":
        arch_flag = "--32" if architecture == "32bit" else "--64"
        return [
            str(TOOL_BINARIES["cpachecker"]),
            "--spec", spec,
            "--timelimit", f"{timeout_sec}s",
            arch_flag,
            source,
        ]

    if tool == "esbmc":
        return [str(TOOL_BINARIES["esbmc"]), "--k-induction", source]

    if tool == "symbiotic":
        arch_flag = "--32" if architecture == "32bit" else "--64"
        return [str(TOOL_BINARIES["symbiotic"]), arch_flag, source]


    if tool == "uautomizer":
        arch = architecture
        return [
            str(TOOL_BINARIES["uautomizer"]),
            "--spec", spec,
            "--architecture", arch,
            "--file", source,
        ]

    if tool == "veriabs":
        return [str(TOOL_BINARIES["veriabs"]), "--property-file", spec, source]

    raise ValueError(f"Unknown tool: {tool}")


def parse_result(tool, output, returncode, timed_out):
    if timed_out:
        raw = output.strip().splitlines()[-1] if output.strip() else "TIMEOUT"
        return "TIMEOUT", raw

    text = output.upper()

    if tool == "aise":
        if "TRUE" in text and "FALSE" not in text:
            return "TRUE", "TRUE"
        if "FALSE" in text:
            return "FALSE", "FALSE"
        if returncode != 0:
            return "ERROR", f"EXIT_{returncode}"
        return "UNKNOWN", "UNKNOWN"
    if tool == "bubaak":
        if "ASSERTION FAIL" in text:
            return "FALSE", "FALSE"
        if "PROPERTY" in text and "HOLDS" in text:
            return "TRUE", "TRUE"
        if "PROPERTY" in text and "VIOLATED" in text:
            return "FALSE", "FALSE"
        if "RESULT: TRUE" in text or "RESULT TRUE" in text:
            return "TRUE", "TRUE"
        if "RESULT: FALSE" in text or "RESULT FALSE" in text:
            return "FALSE", "FALSE"



    if tool == "cpachecker":
        if "VERIFICATION SUCCESSFUL" in text or "VERIFICATION RESULT: TRUE" in text:
            return "TRUE", "TRUE"
        if "VERIFICATION FAILED" in text or "VERIFICATION RESULT: FALSE" in text:
            return "FALSE", "FALSE"
        if "SHUTDOWN REQUESTED" in text or "TIMEOUT" in text:
            return "TIMEOUT", "INTERNAL_TIMEOUT"
        if returncode != 0:
            return "ERROR", f"EXIT_{returncode}"
        return "UNKNOWN", "UNKNOWN"

    if tool == "esbmc":
        if "VERIFICATION SUCCESSFUL" in text:
            return "TRUE", "TRUE"
        if "VERIFICATION FAILED" in text:
            return "FALSE", "FALSE"
        if returncode != 0 and "UNKNOWN" not in text:
            return "ERROR", f"EXIT_{returncode}"
        return "UNKNOWN", "UNKNOWN"

    if tool == "symbiotic":
        if "RESULT: TRUE" in text:
            return "TRUE", "TRUE"
        if "RESULT: FALSE" in text:
            return "FALSE", "FALSE"
        if returncode != 0:
            return "ERROR", f"EXIT_{returncode}"
        return "UNKNOWN", "UNKNOWN"

    if tool == "uautomizer":
        if "RESULT: TRUE" in text:
            return "TRUE", "TRUE"
        if "RESULT: FALSE" in text:
            return "FALSE", "FALSE"
        if "UNSUPPORTED" in text:
            return "UNSUPPORTED", "UNSUPPORTED"
        if returncode != 0:
            return "ERROR", f"EXIT_{returncode}"
        return "UNKNOWN", "UNKNOWN"

    if tool == "veriabs":
        if "TRUE" in text and "FALSE" not in text:
            return "TRUE", "TRUE"
        if "FALSE" in text:
            return "FALSE", "FALSE"
        if returncode != 0:
            return "ERROR", f"EXIT_{returncode}"
        return "UNKNOWN", "UNKNOWN"

    return "UNKNOWN", "UNKNOWN"


def _kill_proc(proc):
    if proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except (ProcessLookupError, OSError):
        return
    try:
        proc.wait(timeout=5)
        return
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except (ProcessLookupError, OSError):
        return
    try:
        proc.wait(timeout=3)
    except subprocess.TimeoutExpired:
        pass


def run_one_case(tool, row, cases_root, timeout_sec, logs_dir, batch_ts):
    case_id = row["id"]
    file_path = cases_root / row["file_path"]
    architecture = row["architecture"]
    label = row["label"]

    err_result = {
        "case_id": case_id,
        "file_name": row["file_name"],
        "file_path": row["file_path"],
        "property": row["property"],
        "architecture": architecture,
        "label": label,
        "status_raw": "",
        "status_normalized": "ERROR",
        "time": 0.0,
        "returncode": -1,
        "timed_out": False,
    }

    if not file_path.exists():
        err_result["status_raw"] = "FILE_NOT_FOUND"
        return err_result

    command = build_command(tool, file_path, architecture, SPEC_FILE, timeout_sec)

    start = time.monotonic()

    try:
        proc = subprocess.Popen(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            bufsize=0,
            start_new_session=True,
        )
    except Exception as e:
        err_result["time"] = time.monotonic() - start
        err_result["status_raw"] = str(e)
        return err_result

    deadline = start + timeout_sec
    chunks = []
    timed_out = False

    selector = sel_mod.DefaultSelector()
    selector.register(proc.stdout, sel_mod.EVENT_READ)

    while True:
        now = time.monotonic()
        if now >= deadline:
            timed_out = True
            break
        if proc.poll() is not None:
            events = selector.select(timeout=0)
            if not events:
                break
        remaining = deadline - now
        events = selector.select(timeout=min(0.5, remaining))
        if not events:
            continue
        for key, _ in events:
            data = os.read(key.fileobj.fileno(), 4096)
            if not data:
                try:
                    selector.unregister(key.fileobj)
                except Exception:
                    pass
                continue
            chunks.append(data.decode("utf-8", errors="replace"))

    selector.close()

    if timed_out:
        _kill_proc(proc)

    try:
        fd = proc.stdout.fileno()
        flags = fcntl.fcntl(fd, fcntl.F_GETFL)
        fcntl.fcntl(fd, fcntl.F_SETFL, flags | os.O_NONBLOCK)
    except OSError:
        pass

    while True:
        try:
            data = os.read(proc.stdout.fileno(), 4096)
        except (BlockingIOError, OSError):
            break
        if not data:
            break
        chunks.append(data.decode("utf-8", errors="replace"))

    proc.stdout.close()

    if not timed_out:
        _kill_proc(proc)

    output = "".join(chunks)
    returncode = proc.returncode if proc.returncode is not None else -1
    elapsed = time.monotonic() - start

    status_normalized, status_raw = parse_result(tool, output, returncode, timed_out)

    safe_name = re.sub(r"[^\w.\-]", "_", row["file_name"])
    log_name = f"{tool}__{safe_name}__{batch_ts}.log"
    log_path = logs_dir / log_name

    header = "\n".join([
        f"case_id={case_id}",
        f"tool={tool}",
        f"file={row['file_path']}",
        f"architecture={architecture}",
        f"property={row['property']}",
        f"label={label}",
        f"status_normalized={status_normalized}",
        f"status_raw={status_raw}",
        f"returncode={returncode}",
        f"elapsed={elapsed:.3f}s",
        f"timed_out={timed_out}",
        "",
    ])
    log_path.write_text(header + output, encoding="utf-8")

    del output
    del proc
    gc.collect()

    return {
        "case_id": case_id,
        "file_name": row["file_name"],
        "file_path": row["file_path"],
        "property": row["property"],
        "architecture": architecture,
        "label": label,
        "status_raw": status_raw,
        "status_normalized": status_normalized,
        "time": elapsed,
        "returncode": returncode,
        "timed_out": timed_out,
    }


def compare_result(status_normalized, label):
    if status_normalized == "TRUE" and label == "true":
        return "TT"
    if status_normalized == "FALSE" and label == "true":
        return "TF"
    if status_normalized == "TRUE" and label == "false":
        return "FT"
    if status_normalized == "FALSE" and label == "false":
        return "FF"
    if status_normalized == "TIMEOUT":
        return "OOT"
    if status_normalized == "ERROR":
        return "ERROR"
    if status_normalized == "UNKNOWN":
        return "UNKNOWN"
    if status_normalized == "UNSUPPORTED":
        return "UNSUPPORTED"
    return "UNKNOWN"


RES_FIELDNAMES = [
    "index",
    "tool",
    "case_name",
    "source_file",
    "property",
    "architecture",
    "status",
    "time",
    "compare_res",
    "status_raw",
    "status_normalized",
    "label",
    "returncode",
    "timed_out",
]


def write_res_csv(results, csv_path, tool):
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    with csv_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=RES_FIELDNAMES)
        writer.writeheader()
        for r in results:
            cmp = compare_result(r["status_normalized"], r["label"])
            writer.writerow({
                "index": r["case_id"],
                "tool": tool,
                "case_name": r["file_name"],
                "source_file": r["file_path"],
                "property": r["property"],
                "architecture": r["architecture"],
                "status": r["status_normalized"],
                "time": f"{r['time']:.2f}",
                "compare_res": cmp,
                "status_raw": r["status_raw"],
                "status_normalized": r["status_normalized"],
                "label": r["label"],
                "returncode": r["returncode"],
                "timed_out": r["timed_out"],
            })


def print_summary(results):
    total = len(results)
    counts = {}
    for r in results:
        cmp = compare_result(r["status_normalized"], r["label"])
        counts[cmp] = counts.get(cmp, 0) + 1
    print(f"\n{'='*60}")
    print(f"Total: {total}")
    for k in sorted(counts):
        print(f"  {k}: {counts[k]}")
    correct = counts.get("TT", 0) + counts.get("FF", 0)
    if total > 0:
        print(f"  accuracy: {correct}/{total} = {correct/total*100:.1f}%")
    print(f"{'='*60}")


def main():
    args = parse_args()
    tool = args.tool

    rows = load_manifest(args.manifest.resolve())
    selected = select_rows(rows, args.start_id, args.end_id)

    if not selected:
        print(f"No cases selected (start={args.start_id}, end={args.end_id}).")
        sys.exit(1)

    cases_root = SCRIPT_DIR / "cases"
    batch_ts = time.strftime("%Y%m%d-%H%M%S")

    output_dir = args.output_dir.resolve()
    logs_dir = output_dir / "logs"
    res_dir = output_dir / "res"
    logs_dir.mkdir(parents=True, exist_ok=True)
    res_dir.mkdir(parents=True, exist_ok=True)

    start_id = int(selected[0]["id"])
    end_id = int(selected[-1]["id"])
    csv_name = f"{tool}__{start_id}_{end_id}__{batch_ts}.csv"
    csv_path = res_dir / csv_name

    print(f"tool       = {tool}")
    print(f"manifest   = {args.manifest}")
    print(f"range      = {start_id}-{end_id} ({len(selected)} cases)")
    print(f"timeout    = {args.timeout}s")
    print(f"output_dir = {output_dir}")
    print(f"csv        = {csv_path}")
    sys.stdout.flush()

    results = []
    for i, row in enumerate(selected):
        case_id = row["id"]
        print(f"[{i+1}/{len(selected)}] id={case_id} file={row['file_name']} ... ", end="", flush=True)

        result = run_one_case(tool, row, cases_root, args.timeout, logs_dir, batch_ts)
        results.append(result)

        cmp = compare_result(result["status_normalized"], result["label"])
        print(f"{cmp} ({result['status_normalized']}) {result['time']:.1f}s")
        sys.stdout.flush()

    write_res_csv(results, csv_path, tool)
    print_summary(results)
    print(f"\nResults saved: {csv_path}")
    print(f"Logs saved: {logs_dir}/")


if __name__ == "__main__":
    main()