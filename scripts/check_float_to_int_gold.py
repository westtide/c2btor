#!/usr/bin/env python3
"""Small float/double -> int/unsigned bit-pattern comparison against CBMC.

Each fixed input is constrained after nondeterministic generation. The plain
CBMC BMC path runs with simplification and propagation disabled, and C2Btor's
source map must retain both symbolic floatbv_typecast instructions. The test
compares frozen CBMC circuit results, fresh CBMC JSON traces, and BtorSim states
at the assertion frame. NaN, infinity and out-of-range conversions are a check
of this CBMC implementation's behavior, not a claim that C defines their result.
No BTOR2 solver, loop unrolling, or unbounded safety claim is involved.
"""

import argparse
import csv
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time


FIXTURES = Path(__file__).resolve().parent / "fixtures"
CHECK_FLAGS = [
    "--32", "--no-standard-checks", "--no-pointer-check",
    "--no-bounds-check", "--no-built-in-assertions",
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def execute(command, directory, label, timeout, expected_exit=0, discard=False):
    start = time.monotonic()
    record = {"command": [str(part) for part in command], "timeout_s": timeout}
    stdout = directory / (label + ".stdout")
    stderr = directory / (label + ".stderr")
    try:
        with stdout.open("w") as out, stderr.open("w") as err:
            process = subprocess.run(
                record["command"], stdout=subprocess.DEVNULL if discard else out,
                stderr=err, timeout=timeout, check=False,
            )
        record["exit_code"] = process.returncode
    except subprocess.TimeoutExpired:
        record["timeout"] = True
        raise RuntimeError(f"{label}: exceeded {timeout:g}s") from None
    finally:
        record["elapsed_s"] = round(time.monotonic() - start, 6)
        (directory / (label + ".command.json")).write_text(
            json.dumps(record, indent=2) + "\n"
        )
    if process.returncode != expected_exit:
        raise RuntimeError(
            f"{label}: exit {process.returncode}, expected {expected_exit}; "
            f"see {stderr} and {stdout}"
        )
    return stdout


def cbmc_results(path, raw_bits):
    document = json.loads(path.read_text())
    properties = [result for item in document for result in item.get("result", [])]
    if len(properties) != 1 or properties[0].get("status") != "FAILURE":
        raise RuntimeError("CBMC must expose only the intentional capture assertion")
    values = {}
    for step in properties[0].get("trace", []):
        if step.get("stepType") != "assignment" or step.get("hidden"):
            continue
        if step.get("lhs") in {"result_signed", "result_unsigned", "input.value"}:
            values[step["lhs"]] = step["value"]["binary"]
    if values.pop("input.value", None) != raw_bits:
        raise RuntimeError("CBMC trace does not contain the requested floating bits")
    if set(values) != {"result_signed", "result_unsigned"} or any(
        len(bits) != 32 or re.fullmatch("[01]+", bits) is None
        for bits in values.values()
    ):
        raise RuntimeError("CBMC trace is missing concrete 32-bit integer results")
    return values


def replay_metadata(model, source_map, raw_width):
    metadata = json.loads(source_map.read_text())
    if metadata["int_width"] != 32:
        raise RuntimeError("fixture requires a 32-bit int target")
    casts = [item for item in metadata["instructions"]
             if item.get("assign_symbol") in {"result_signed", "result_unsigned"}]
    if len(casts) != 2 or any(
        "floatbv_typecast" not in item["instruction"]
        or item["last_node"] <= item["first_node"] + 32 for item in casts
    ):
        raise RuntimeError("C2Btor folded away a symbolic floating conversion")
    assertions = [item for item in metadata["instructions"] if item["kind"] == "ASSERT"]
    if len(assertions) != 1:
        raise RuntimeError("fixture must retain one capture assertion")
    frame = assertions[0]["pc"]
    prefix = metadata["instructions"][:frame]
    if any(item["pc"] != index or item["successors"] != [index + 1]
           for index, item in enumerate(prefix)):
        raise RuntimeError("fixture is no longer a straight-line transition sequence")

    sorts = {}
    inputs = []
    for line in model.read_text().splitlines():
        words = line.split()
        if len(words) >= 4 and words[1:3] == ["sort", "bitvec"]:
            sorts[words[0]] = int(words[3])
        elif len(words) >= 4 and words[1] == "input":
            if sorts[words[2]] != raw_width or not (
                words[3].startswith("nondet_") or words[3].endswith("_decl")
            ):
                raise RuntimeError(f"unexpected model input: {line}")
            inputs.append(words[3])
    if not inputs or sum(name.startswith("nondet_") for name in inputs) != 1:
        raise RuntimeError("expected exactly one nondeterministic raw input")
    return frame, inputs


def simulation_results(path, frame):
    values = {}
    in_frame = False
    for line in path.read_text().splitlines():
        if line.startswith("#"):
            in_frame = line == f"#{frame}"
        elif line.startswith("@"):
            in_frame = False
        elif in_frame:
            words = line.split()
            if len(words) == 3:
                symbol = words[2].removesuffix(f"#{frame}")
                if symbol in {"result_signed", "result_unsigned", "pc"}:
                    values[symbol] = words[1]
    if int(values.pop("pc", "-1"), 2) != frame:
        raise RuntimeError("BtorSim did not reach the capture assertion PC")
    if set(values) != {"result_signed", "result_unsigned"} or any(
        len(bits) != 32 or re.fullmatch("[01]+", bits) is None
        for bits in values.values()
    ):
        raise RuntimeError("BtorSim omitted concrete 32-bit integer result states")
    return values


def compare_case(case, args, source, root):
    directory = root / f"f{case['float_width']}_{case['name']}"
    directory.mkdir()
    raw_width = case["float_width"]
    raw_bits = f"{int(case['input_hex'], 16):0{raw_width}b}"
    suffix = "u" if raw_width == 32 else "ull"
    defines = ["-D", f"FLOAT_WIDTH={raw_width}",
               "-D", f"INPUT_BITS={case['input_hex']}{suffix}"]
    bmc = execute(
        [args.cbmc, source, *defines, *CHECK_FLAGS, "--no-simplify",
         "--no-propagation", "--json-ui", "--trace"],
        directory, "cbmc", args.timeout, expected_exit=10,
    )
    baseline = cbmc_results(bmc, raw_bits)
    model = directory / "model.btor2"
    source_map = directory / "model.map.json"
    execute(
        [args.c2btor, source, *defines, *CHECK_FLAGS, "--goto-btor2",
         "--goto-btor2-out", model, "--goto-btor2-map-out", source_map, "--inline"],
        directory, "convert", args.timeout,
    )
    execute([args.catbtor, model], directory, "parser", args.timeout, discard=True)
    frame, inputs = replay_metadata(model, source_map, raw_width)
    witness = directory / "fixed-input.witness"
    content = ["sat", "b0", "#0"]
    for step in range(frame + 1):
        content.append(f"@{step}")
        content.extend(f"{index} {raw_bits}" for index in range(len(inputs)))
    witness.write_text("\n".join([*content, ".", ""]))
    replay = execute(
        [args.btorsim, "--states", model, witness],
        directory, "btorsim", args.timeout,
    )
    simulated = simulation_results(replay, frame)
    expected = {
        "result_signed": f"{int(case['signed_hex'], 16):032b}",
        "result_unsigned": f"{int(case['unsigned_hex'], 16):032b}",
    }
    return {
        **case, "cbmc_signed_hex": f"0x{int(baseline['result_signed'], 2):08x}",
        "cbmc_unsigned_hex": f"0x{int(baseline['result_unsigned'], 2):08x}",
        "btor_signed_hex": f"0x{int(simulated['result_signed'], 2):08x}",
        "btor_unsigned_hex": f"0x{int(simulated['result_unsigned'], 2):08x}",
        "assertion_frame": frame, "parser_passed": True,
        "cbmc_matches_gold": baseline == expected,
        "btor_matches_cbmc": simulated == baseline,
        "status": "pass" if baseline == expected == simulated else "mismatch",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c2btor", type=Path, required=True)
    parser.add_argument("--cbmc", type=Path,
                        help="CBMC binary; defaults to c2btor's plain BMC mode")
    parser.add_argument("--catbtor", type=Path, required=True)
    parser.add_argument("--btorsim", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True,
                        help="new run directory; must not already exist")
    parser.add_argument("--timeout", type=float, default=15,
                        help="per-command wall-clock limit in seconds (default 15)")
    args = parser.parse_args()
    args.cbmc = args.cbmc or args.c2btor
    for name in ("c2btor", "cbmc", "catbtor", "btorsim"):
        path = getattr(args, name).resolve()
        if not path.is_file():
            parser.error(f"missing {name} binary: {path}")
        setattr(args, name, path)
    if args.output_dir.exists():
        parser.error("--output-dir must not already exist")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    root = args.output_dir.resolve()
    root.mkdir(parents=True)
    source = root / "float_to_int_gold.c"
    golden = root / "float_to_int_gold.json"
    shutil.copyfile(FIXTURES / source.name, source)
    shutil.copyfile(FIXTURES / golden.name, golden)
    manifest = json.loads(golden.read_text())
    (root / "tools.json").write_text(json.dumps({
        name: {"path": str(getattr(args, name)), "sha256": digest(getattr(args, name))}
        for name in ("c2btor", "cbmc", "catbtor", "btorsim")
    }, indent=2) + "\n")
    results = []
    for case in manifest["cases"]:
        try:
            result = compare_case(case, args, source, root)
        except (RuntimeError, KeyError, ValueError, OSError) as error:
            result = {**case, "status": "error", "error": str(error)}
        results.append(result)
        print(f"f{case['float_width']} {case['name']}: {result['status']}", flush=True)
    summary = {
        "scope": manifest["scope"], "cases": len(results),
        "integer_bit_comparisons": 2 * len(results),
        "passed": sum(item["status"] == "pass" for item in results),
        "results": results,
    }
    (root / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    columns = list(dict.fromkeys(key for item in results for key in item))
    with (root / "summary.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=columns)
        writer.writeheader()
        writer.writerows(results)
    print(f"{summary['passed']}/{len(results)} cases passed; {root / 'summary.json'}")
    return 0 if summary["passed"] == len(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
