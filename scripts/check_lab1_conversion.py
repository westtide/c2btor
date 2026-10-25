#!/usr/bin/env python3
"""Reproduce Lab1 conversion and parser checks only; never invoke a solver.

Accepts the server records CSV, the local case collection, and optional include
paths to reproduce frontend/library loading on another host. Outputs commands,
logs, models, parser status, failure categories, and per-configuration totals.
"""
import argparse
import collections
import concurrent.futures
import csv
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time


def category(log):
    if "No selected source property" in log:
        return "no-property"
    if "allocation size upper bound" in log:
        return "allocation-size-capacity"
    if "runtime object" in log and "upper bound" in log:
        return "runtime-object-capacity"
    if "automatic object re-entry" in log:
        return "automatic-lifetime"
    if "cannot establish a finite allocation count" in log:
        return "unbounded-allocation-count"
    if "finite allocation count" in log:
        return "allocation-count-limit"
    if "Unsupported byte memory" in log:
        return "memory-representation"
    if "PARSING ERROR" in log or "failed to open" in log:
        return "frontend"
    return "other"


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--c2btor", type=Path, required=True)
    p.add_argument("--catbtor", type=Path, required=True)
    p.add_argument("--records", type=Path, required=True)
    p.add_argument("--cases", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--include", action="append", default=[])
    p.add_argument("--aiob-headers", type=Path)
    p.add_argument("--jobs", type=int, default=2)
    p.add_argument("--timeout", type=int, default=60)
    p.add_argument("--max-model-mib", type=int, default=128)
    p.add_argument("--failed-only", action="store_true")
    args = p.parse_args()
    if args.jobs < 1 or args.timeout < 1 or args.max_model_mib < 1:
        p.error("jobs, timeout, and max-model-mib must be positive")
    args.output.mkdir(parents=True, exist_ok=False)
    # Keep every row on one executable even if the workspace is rebuilt during
    # a long audit. The snapshot also makes the recorded commands rerunnable.
    converter = (args.output / "c2btor").resolve()
    shutil.copy2(args.c2btor.resolve(), converter)
    manifest = dict(
        converter_sha256=hashlib.sha256(converter.read_bytes()).hexdigest(),
        records_sha256=hashlib.sha256(args.records.read_bytes()).hexdigest(),
        version=subprocess.check_output([str(converter), "--version"], text=True).strip(),
        arguments=vars(args), model_checking_run=False)
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2, default=str) + "\n")
    with args.records.open(newline="") as f:
        rows = list(csv.DictReader(f))
    if args.failed_only:
        rows = [row for row in rows if row["status"] != "ok"]

    def convert(row):
        dest = args.output / row["config"] / row["file_path"]
        dest.mkdir(parents=True)
        model = dest / "model.btor2"
        encoding = {"ob": "bv", "oa": "array", "om": "mixed"}[row["config"]]
        source = (args.cases / row["file_path"]).resolve()
        cmd = [str(converter), str(source),
               "--goto-btor2", "--inline", "--64" if row["architecture"] == "LP64" else "--32",
               "--memory", "object", "--array", encoding, "--goto-btor2-out", str(model)]
        for include in args.include:
            cmd += ["-I", include]
        if args.aiob_headers and row["file_path"].startswith("loop-industry-pattern/aiob_4"):
            cmd += ["--arch", "i386", "--os", "linux", "-I", str(args.aiob_headers.resolve())]
        (dest / "command.json").write_text(json.dumps(cmd, indent=2) + "\n")
        start = time.monotonic()
        # prlimit is not available on macOS. A tiny wrapper sets a file limit
        # before exec; avoid preexec_fn in this multithreaded runner.
        wrapper = [sys.executable, "-c",
                   "import os,resource,sys; n=int(sys.argv[1]); "
                   "resource.setrlimit(resource.RLIMIT_FSIZE,(n,n)); "
                   "os.execv(sys.argv[2],sys.argv[2:])",
                   str(args.max_model_mib * 1024 * 1024), *cmd]
        with (dest / "conversion.log").open("w") as log:
            try:
                rc = subprocess.run(wrapper, stdout=log, stderr=subprocess.STDOUT,
                                    timeout=args.timeout).returncode
                status = "ok" if rc == 0 and model.exists() else "fail"
            except subprocess.TimeoutExpired:
                rc, status = None, "timeout"
        item = {key: row[key] for key in ("idx", "file_path", "config", "architecture")}
        item.update(server_status=row["status"], status=status, exit=rc,
                    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                    conversion_seconds=round(time.monotonic() - start, 3),
                    model_bytes=model.stat().st_size if model.exists() else None,
                    directory=str(dest), model_checking_run=False)
        text = (dest / "conversion.log").read_text(errors="replace")
        item["category"] = "ok" if status == "ok" else category(text)
        item["evidence"] = [line for line in text.splitlines()
                            if "Unsupported" in line or "No selected source property" in line][-1:]
        if rc is not None and rc < 0:
            item["category"] = "resource-limit-or-signal"
        if status == "ok":
            with (dest / "parser.log").open("w") as log:
                try:
                    item["parser_exit"] = subprocess.run(
                        [str(args.catbtor.resolve()), str(model)], stdout=log,
                        stderr=subprocess.STDOUT, timeout=args.timeout).returncode
                except subprocess.TimeoutExpired:
                    item["parser_exit"] = None
            if item["parser_exit"] != 0:
                item["status"], item["category"] = "parser-fail", "parser-fail"
        return item

    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        with (args.output / "results.jsonl").open("w") as f:
            for item in pool.map(convert, rows):
                results.append(item)
                f.write(json.dumps(item) + "\n")
                f.flush()
                if len(results) % 100 == 0:
                    print("completed", len(results), "of", len(rows), flush=True)
    summary = {}
    for config in sorted({row["config"] for row in results}):
        selected = [row for row in results if row["config"] == config]
        summary[config] = dict(
            status=dict(collections.Counter(row["status"] for row in selected)),
            categories=dict(collections.Counter(row["category"] for row in selected)),
            newly_accepted=sum(row["server_status"] != "ok" and row["status"] == "ok" for row in selected),
            server_ok_local_not_ok=[row["file_path"] for row in selected
                                   if row["server_status"] == "ok" and row["status"] != "ok"])
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
