#!/usr/bin/env python3
"""Summarize compact finite traces, structural checks and scoped P3 comparisons."""

from collections import Counter
import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def read(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def key(row):
    return row["case"], row["architecture"], row["array"]


def behavior(trace):
    return {
        "source_assertion_execution_counts": {name: len(frames) for name, frames in trace["source_assertion_execution_frames"].items()},
        "source_failure_counts": {name: len(frames) for name, frames in trace["source_failure_frames"].items()},
        "observed_values": {name: [entry["unsigned_value"] for entry in entries]
                            for name, entries in trace["observed_values"].items()}}


def main():
    names = {
        "compact_array_mixed": "finite-phase4-final",
        "compact_bv_fallback": "finite-phase4-final-bv-fallback",
        "p3_new_cases_array_mixed": "finite-phase4-final-new-cases-off",
        "p3_new_cases_bv_fallback": "finite-phase4-final-new-cases-off-bv-fallback"}
    paths = {name: HERE / "results" / directory for name, directory in names.items()}
    groups, rows, failures = {}, {}, []
    for name, path in paths.items():
        entries, run, summary = read(path / "results.json"), read(path / "run.json"), read(path / "summary.json")
        rows[name] = {key(row): row for row in entries}
        groups[name] = {"directory": str(path.relative_to(HERE)), "binary_sha256": run["binary_sha256"],
                        "case_runs": len(entries), "status_counts": dict(Counter(row["status"] for row in entries)),
                        "array_seed_byte": run["array_seed_byte"], "feature_flags": run["feature_flags"],
                        "malloc_failure_options_rejected": summary["malloc_options_rejected_by_current_cli"]}
        failures.extend(summary["failures"])
        for row in entries:
            if row["status"] == "finite_regression_pass" and digest(Path(row["source"])) != row["source_sha256"]:
                failures.append({"kind": "current_source_hash_differs", "key": key(row), "group": name})
    compact = {**rows["compact_array_mixed"], **rows["compact_bv_fallback"]}
    parent = {**rows["p3_new_cases_array_mixed"], **rows["p3_new_cases_bv_fallback"]}
    comparisons = []
    for case_key, before in parent.items():
        after = compact[case_key]
        matched = (before["status"] == after["status"] == "finite_regression_pass" and
                   before["source_sha256"] == after["source_sha256"] and
                   all(behavior(before["traces"][mode]) == behavior(after["traces"][mode])
                       for mode in before.get("traces", {})))
        comparisons.append({"case": case_key[0], "architecture": case_key[1], "array": case_key[2],
                            "source_sha256": after.get("source_sha256"), "behavior_matches": matched,
                            "p3_model_sha256": before.get("model_sha256"),
                            "p4_model_sha256": after.get("model_sha256")})
        if not matched:
            failures.append({"kind": "parent_compact_behavior_differs", "key": case_key})
    same_models = []
    for architecture in ["32", "64"]:
        for array in ["array", "mixed", "bv"]:
            a = compact[("T2_symbolic_extent_small", architecture, array)]
            b = compact[("T2_symbolic_extent_large", architecture, array)]
            same = a["source_sha256"] == b["source_sha256"] and a["model_sha256"] == b["model_sha256"]
            same_models.append({"architecture": architecture, "array": array, "same_source_and_model": same})
            if not same:
                failures.append({"kind": "different_N_models_differ", "architecture": architecture, "array": array})
    seeds = []
    seed_path = HERE / "results/finite-phase4-seed-checks"
    for path in sorted(seed_path.glob("*/seed-check.result.json")):
        record = read(path)
        original_dir = HERE / record["source_directory"]
        association = (record["original_model_sha256"] == digest(original_dir / "model.btor2") and
                       record["original_map_sha256"] == digest(original_dir / "model.map.json") and
                       record["trace_sha256"] == digest(original_dir / "fixed.trace"))
        seeds.append({"directory": str(path.parent.relative_to(HERE)), "status": record["status"],
                      "model_map_trace_association_checked": association, "samples": record["samples"]})
        if record["status"] != "pass" or not association:
            failures.append({"kind": "initial_seed_check", "directory": str(path.parent)})
    evidence = []
    for case_key, row in sorted(compact.items()):
        item = {"case": case_key[0], "architecture": case_key[1], "array": case_key[2], "status": row["status"]}
        if row["status"] == "finite_regression_pass":
            path = paths["compact_bv_fallback" if case_key[2] == "bv" else "compact_array_mixed"] / "_".join(case_key)
            if row["model_sha256"] != digest(path / "model.btor2") or row["map_sha256"] != digest(path / "model.map.json"):
                failures.append({"kind": "model_map_hash_association", "key": case_key})
            item.update({"source_sha256": row["source_sha256"], "model_sha256": row["model_sha256"],
                         "map_sha256": row["map_sha256"], "storage_structure": row["storage_structure"],
                         "traces": {mode: {**behavior(trace),
                             "source_assertion_execution_frames": trace["source_assertion_execution_frames"],
                             "source_failure_frames": trace["source_failure_frames"],
                             "valid_prefix_frames": trace["valid_prefix_frames"],
                             "first_constraint_violation_frame": trace["first_constraint_violation_frame"],
                             "explicit_uninitialized_array_states": trace["explicit_uninitialized_array_states"]}
                             for mode, trace in row["traces"].items()}})
            if row.get("same_backend_constant_ub_observations"):
                item["same_backend_constant_ub_observations"] = row["same_backend_constant_ub_observations"]
        else:
            item["rejection_diagnostics"] = [line for line in row.get("diagnostic_tail", []) if "Unsupported" in line or "unsupported" in line]
        evidence.append(item)
    fixture_traces = sum(len(row.get("traces", {})) for row in compact.values())
    counterpart_traces = sum(len(row.get("same_backend_constant_ub_observations", {})) for row in compact.values())
    parent_traces = sum(len(row.get("traces", {})) for row in parent.values())
    report = {
        "status": "pass" if not failures else "mismatch",
        "scope": "Parser/type acceptance, supplied finite prefixes, explicit source assertions and storage contracts only; no solver, model checker, C SAFE/UNSAFE or standard-C equivalence claim.",
        "groups": groups, "compact_case_runs": len(compact),
        "compact_status_counts": dict(Counter(row["status"] for row in compact.values())),
        "parent_new_case_runs": len(parent), "fixture_simulation_traces": fixture_traces,
        "same_backend_constant_ub_traces": counterpart_traces, "parent_new_case_traces": parent_traces,
        "initial_seed_observation_traces": len(seeds),
        "total_finite_simulation_traces": fixture_traces + counterpart_traces + parent_traces + len(seeds),
        "nsqm_compact_contract": "Two active data arrays and two total Array states, two dynamic size states, word64_certified=true with accesses8, element_bits64/index_bits29; no zero helper. Existing source-abort constraints are scored only on their valid prefix.",
        "mixed_byte_contract": "Non-singleton companion has symbolic native byte8 storage and word64_certified=false. The original singleton case and small bounded Mixed calloc preserve their existing representation.",
        "calloc_contract": "Supplied n3 observes first/last unwritten values0, writes first9 and retains last0/size24. Array path has one dynamic data/size state and a separately counted initialized zero-helper; calloc conservatively retains byte cells.",
        "array_seed_contract": "Array input elements and all no-init Array state defaults at #0 receive repeated 0x3d bytes. Init-constrained zero helpers are excluded. Independent read(index0) aliases verify frame0 values61 for byte8 or4412750543122677053 for word64, while zero helpers remain0.",
        "source_model_map_hashes_checked": not any(f["kind"] in {"current_source_hash_differs", "model_map_hash_association"} for f in failures),
        "different_N_same_model": same_models, "parent_compact_new_case_comparisons": comparisons,
        "seed_checks": seeds, "superseded_outputs": ["results/finite-phase4", "results/finite-phase4-new-cases-off"],
        "validation_failures": failures, "evidence": evidence}
    (HERE / "finite-phase4-results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ["status", "compact_case_runs", "compact_status_counts",
                      "parent_new_case_runs", "total_finite_simulation_traces", "validation_failures"]}, indent=2))
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
