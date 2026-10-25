#!/usr/bin/env python3
"""Summarize finite phase3 artifacts without running any verification tool."""

import argparse
from collections import Counter
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def read(path):
    return json.loads(path.read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path, default=HERE / "results/finite-phase3-reviewed")
    parser.add_argument("--bv", type=Path, default=HERE / "results/finite-phase3-reviewed-bv-fallback")
    parser.add_argument("--output", type=Path, default=HERE / "finite-phase3-results.json")
    args = parser.parse_args()
    if not args.output.resolve().is_relative_to(HERE):
        parser.error("output must be under test/c2btor_symbolic_heap")
    directories = {"array_mixed": args.native.resolve(), "bv_explicit_fallback": args.bv.resolve()}
    groups, evidence, failures = {}, [], []
    traces = counterparts = counterpart_traces = 0
    for name, directory in directories.items():
        rows, run, summary = read(directory / "results.json"), read(directory / "run.json"), read(directory / "summary.json")
        groups[name] = {"directory": str(directory.relative_to(HERE)),
                        "binary_sha256": run["binary_sha256"], "feature_flags": run["feature_flags"],
                        "array_seed_byte": run["array_seed_byte"],
                        "case_runs": len(rows), "status_counts": dict(Counter(row["status"] for row in rows)),
                        "malloc_cli_options_rejected": summary["malloc_options_rejected_by_current_cli"]}
        failures.extend(summary["failures"])
        for row in rows:
            item = {"case": row["case"], "architecture": row["architecture"], "array": row["array"],
                    "status": row["status"]}
            if row["status"] == "finite_regression_pass":
                traces += len(row["traces"])
                item["source_sha256"] = row["source_sha256"]
                item["model_sha256"] = row["model_sha256"]
                item["traces"] = {mode: {key: trace[key] for key in (
                    "source_assertion_execution_frames", "source_failure_frames", "valid_prefix_frames",
                    "first_constraint_violation_frame", "observed_values", "source_nondet_call_frames",
                    "static_vcd_suffix_carried", "terminal_self_loop_pc_if_carried")}
                                  for mode, trace in row["traces"].items()}
                if row.get("same_backend_constant_ub_observations"):
                    counterparts += 1
                    counterpart_traces += len(row["same_backend_constant_ub_observations"])
                    item["same_backend_constant_ub_observations"] = row["same_backend_constant_ub_observations"]
                if row["case"].startswith("T2_symbolic_extent"):
                    case_dir = directory / f"{row['case']}_{row['architecture']}_{row['array']}"
                    memory = read(case_dir / "model.map.json")["memory"]
                    model = (case_dir / "model.btor2").read_text()
                    item["symbolic_storage"] = {key: memory[key] for key in (
                        "allocation_storage_slots", "object_id_width", "pointer_width", "offset_width")}
                    item["symbolic_storage"]["effective_internal_pointer_width"] = memory.get("internal_pointer_width", memory["pointer_width"])
                    item["symbolic_storage"]["wide_offsets_activated"] = memory["symbolic_heap"]["wide_pointer_offsets"]
                    item["symbolic_storage"]["legacy_signed_offset_capacity_bytes"] = (1 << (memory["pointer_width"] - memory["object_id_width"] - 1)) - 1
                    item["symbolic_storage"]["objects"] = memory["object_storage"]
                    item["symbolic_storage"]["allocation_expressions"] = memory["symbolic_heap"]["allocation_expressions"]
                    item["symbolic_storage"]["numeric_nodes"] = sum(line[:1].isdigit() for line in model.splitlines())
                    item["symbolic_storage"]["model_bytes"] = len(model.encode())
                    wide = memory["symbolic_heap"]["wide_pointer_offsets"]
                    expected_offset = int(row["architecture"]) if wide else int(row["architecture"]) - memory["object_id_width"]
                    if (memory["allocation_storage_slots"] != 2 or memory["pointer_width"] != int(row["architecture"]) or
                        memory["offset_width"] != expected_offset or
                        (not wide and any(expression["upper_bytes"] is None or expression["upper_bytes"] > (1 << (memory["offset_width"] - 1)) - 1
                                          for expression in memory["symbolic_heap"]["allocation_expressions"])) or
                        any(not expression["symbolic"] for expression in memory["symbolic_heap"]["allocation_expressions"]) or
                        any(storage["data_encoding"] != "array" or storage["element_bits"] != 8 or
                            storage["index_bits"] != memory["offset_width"] or storage["elements"] is not None or
                            storage["capacity_bytes"] is not None or storage["bitmap_encoding"] != "none"
                            for storage in memory["object_storage"])):
                        failures.append({"kind": "symbolic_storage_shape", "case": row["case"],
                                         "architecture": row["architecture"], "array": row["array"]})
            else:
                item["rejection_diagnostics"] = [line for line in row.get("diagnostic_tail", [])
                                                  if "Unsupported" in line or "unsupported" in line]
            evidence.append(item)
    same_models = []
    for architecture in ["32", "64"]:
        for array in ["array", "mixed", "bv"]:
            pair = [item for item in evidence if item["case"].startswith("T2_symbolic_extent") and
                    item["architecture"] == architecture and item["array"] == array]
            equal = (len(pair) == 2 and all(item["status"] == "finite_regression_pass" for item in pair) and
                     pair[0]["source_sha256"] == pair[1]["source_sha256"] and
                     pair[0]["model_sha256"] == pair[1]["model_sha256"])
            same_models.append({"architecture": architecture, "array": array,
                                "small_large_same_source_and_model": equal})
            if not equal:
                failures.append({"kind": "small_large_model_differs", "architecture": architecture, "array": array})
    report = {
        "scope": "Fully supplied finite BtorSim prefixes and explicit representation rejection checks; no solver, model checker, C SAFE/UNSAFE verdict or standard-C equivalence claim.",
        "status": "pass" if not failures else "mismatch", "groups": groups,
        "total_case_runs": sum(group["case_runs"] for group in groups.values()),
        "successful_fixture_configurations": sum(item["status"] == "finite_regression_pass" for item in evidence),
        "expected_rejections": sum(item["status"] == "expected_rejection" for item in evidence),
        "fixture_simulation_traces": traces, "constant_counterpart_configurations": counterparts,
        "constant_counterpart_traces": counterpart_traces, "total_finite_simulation_traces": traces + counterpart_traces,
        "requested_max_input_frame": 512,
        "t1_valid_prefix_note": "N=1 source unreach-call executes and fails at frame64, while both existing source-abort constraints still hold. First abort constraint=false is frame66: only frames0..65 are counted valid; later requested frames are excluded.",
        "t2_small_large_same_models": same_models,
        "malloc_policy": "Existing CLI malloc success-none policy is unchanged; failure option probes are rejected, so no failure input or failure semantics is synthesized.",
        "vcd_suffix_policy": "Missing static suffix is carried only after stdout confirms requested k and the last PC is a mapped END_FUNCTION self-loop. All constraint checks precede source observations, and only the constraint-valid prefix is scored.",
        "namespace_policy": "Original model bytes, node IDs, source namespace markers and map remain unchanged; appended observation model has a distinct hash and is excluded from conversion-hash metrics.",
        "ub_policy": "T5 one-past and T8 post-free observations are compared only to same-backend constant-size counterparts. They are not C safety conclusions.",
        "superseded_outputs": ["results/finite-phase3-initial (initial harness exploration)",
                               "results/finite-phase3 and results/finite-phase3-bv-fallback (before compatibility refinement)"],
        "limits": {"conversion_seconds": 20, "parser_seconds": 10, "simulation_seconds": 30,
                   "output_file_mib": 64, "memory_limit": None, "peak_rss": None},
        "validation_failures": failures, "evidence": evidence}
    if (args.native.resolve() == HERE / "results/finite-phase3-reviewed" and
            args.bv.resolve() == HERE / "results/finite-phase3-reviewed-bv-fallback"):
        report["initial_state_coverage_correction"] = {
            "historical_gap": "The original traces explicitly supplied every input port, including Array inputs, but did not assign no-init Array states at #0. BtorSim checking-mode defaults selected those initial states.",
            "superseded_by": "phase3-explicit-state-recheck.json",
            "preservation": "Only the initial-state seed coverage claim is superseded. Historical source/model/map hashes and raw outputs remain unchanged."}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ("status", "total_case_runs", "successful_fixture_configurations",
                     "expected_rejections", "total_finite_simulation_traces", "validation_failures")}, indent=2))
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
