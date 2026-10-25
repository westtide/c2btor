#!/usr/bin/env python3
"""One frozen converter, exact recorded Lab1 cohort, parser only; no checking."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
import importlib.util
import json
from pathlib import Path
import shutil
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
RECURSIVE = {
    "bitvector-regression/recHanoi03-1.c", "loop-industry-pattern/ofuf_1.c",
    "loop-industry-pattern/ofuf_2.c", "loop-industry-pattern/ofuf_3.c"}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--c2btor", type=Path, required=True)
    p.add_argument("--output-dir", type=Path, required=True)
    p.add_argument("--feature-flag", action="append", default=[])
    p.add_argument("--bv-fallback", action="store_true")
    p.add_argument("--configs", default="bv,array,mixed")
    p.add_argument("--workers", type=int, default=3)
    p.add_argument("--memory-gib", type=float, default=0)
    p.add_argument("--include-recursive", action="store_true")
    p.add_argument("--case-filter", action="append", default=[])
    args = p.parse_args()
    output = args.output_dir.resolve()
    if not output.is_relative_to(HERE) or output.exists():
        p.error("output must be a fresh directory inside this fixture directory")
    configs = args.configs.split(",")
    if any(x not in {"bv", "array", "mixed"} for x in configs):
        p.error("configs must be bv,array,mixed")
    output.mkdir(parents=True)
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location(
        "c2btor_metrics", ROOT / "scripts/check_c2btor_optimizations.py")
    h = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(h)
    binary = output / "c2btor.frozen"
    shutil.copy2(args.c2btor.resolve(), binary)
    options = argparse.Namespace(
        dataset=ROOT / "test/lab1-data",
        records=Path("/Users/west/Downloads/Lab1_btor_v8_records.csv"),
        cases_file=None, case_filter=args.case_filter, limit=None,
        output_dir=output, common_arg=[
            "--goto-btor2-optimize-state", "--goto-btor2-logical-arrays",
            "--goto-btor2-scalar-blocks", "--goto-btor2-array-blocks",
            "-I", "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include",
            *args.feature_flag],
        aiob_headers=HERE / "linux_compatible_headers",
        catbtor=Path("/Users/west/Developer/btor2tools/build/bin/catbtor"),
        conversion_timeout=60, parser_timeout=30,
        memory_gib=args.memory_gib, max_model_mib=128)
    cases = h.benchmark_cases(options)
    excluded = sorted(c["case"] for c in cases if c["case"] in RECURSIVE)
    if not args.include_recursive:
        cases = [c for c in cases if c["case"] not in RECURSIVE]
    h.save(output / "run.json", {
        "binary_sha256": h.digest(binary), "binary": str(binary),
        "arguments": {k: str(v) if isinstance(v, Path) else v
                      for k, v in vars(args).items()},
        "common_options": options.common_arg,
        "harness_sha256": h.digest(Path(__file__)),
        "helper_sha256": h.digest(ROOT / "scripts/check_c2btor_optimizations.py"),
        "selected_cases": len(cases), "excluded_recursive": excluded,
        "frontend_header_hashes": {x.name: h.digest(x) for x in options.aiob_headers.glob("*.h")},
        "model_checking_run": False, "backend_verdict": "NOT_RUN",
        "scope": "conversion and official parser only; no SAFE/FALSE claim"})
    results = []
    jobs = [(case, config, "native", []) for case in cases for config in configs]
    if args.bv_fallback:
        jobs += [(case, "bv", "bv-array-fallback",
                  ["--goto-btor2-symbolic-heap-bv-array-fallback"]) for case in cases]
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(h.execute, case, config, variant, binary, extra, options)
                   for case, config, variant, extra in jobs]
        for future in as_completed(futures):
            results.append(future.result())
            if len(results) % 100 == 0 or len(results) == len(jobs):
                h.save(output / "results.json", results)
                print(f"{len(results)}/{len(jobs)} {dict(Counter(x['status'] for x in results))}", flush=True)
    results.sort(key=lambda r: (r["variant"], r["config"], r["case"]))
    h.save(output / "results.json", results)
    groups = {}
    for variant, config in sorted({(r["variant"], r["config"]) for r in results}):
        group = [r for r in results if r["variant"] == variant and r["config"] == config]
        groups[f"{variant}/{config}"] = {
            "cases": len(group), "statuses": dict(Counter(r["status"] for r in group))}
        failures = [r["case"] for r in group if r["status"] != "pass"]
        (output / f"failed-{variant}-{config}.txt").write_text("\n".join(failures) + "\n")
    h.save(output / "summary.json", {
        "groups": groups, "run_count": len(results), "selected_cases": len(cases),
        "excluded_recursive": excluded, "model_checking_run": False,
        "backend_verdict": "NOT_RUN"})
    print(json.dumps(groups, ensure_ascii=False), flush=True)


if __name__ == "__main__":
    main()
