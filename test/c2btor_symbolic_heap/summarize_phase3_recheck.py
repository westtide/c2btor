#!/usr/bin/env python3
"""Summarize P3 finite replays with explicit no-init Array state seeds."""

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


def nodes_from(path):
    result = {}
    for line in path.read_text().splitlines():
        tokens = line.split(";", 1)[0].split()
        if tokens:
            result[int(tokens[0])] = tokens[1:]
    return result


def traces_summary(row):
    return {mode: {
        "source_assertion_execution_frames": trace["source_assertion_execution_frames"],
        "source_failure_frames": trace["source_failure_frames"],
        "valid_prefix_frames": trace["valid_prefix_frames"],
        "first_constraint_violation_frame": trace["first_constraint_violation_frame"],
        "no_init_array_state_count": len(trace["explicit_uninitialized_array_states"])}
        for mode, trace in row["traces"].items()}


def main():
    group_names = ["finite-phase3-explicit-states", "finite-phase3-explicit-states-bv-fallback"]
    groups, rows, paths, bindings, failures = [], {}, {}, [], []
    expected_flags = ["--goto-btor2-symbolic-heap", "--goto-btor2-symbolic-heap-arrays",
                      "--goto-btor2-symbolic-heap-wide-offsets"]
    sources, seeded_states, fixture_traces, ub_traces = {}, 0, 0, 0
    for name in group_names:
        path = HERE / "results" / name
        entries, run, summary = read(path / "results.json"), read(path / "run.json"), read(path / "summary.json")
        expected = expected_flags + (["--goto-btor2-symbolic-heap-bv-array-fallback"] if name.endswith("bv-fallback") else [])
        if (run["feature_flags"] != expected or run["array_seed_byte"] != 61 or
                digest(Path(run["binary"])) != run["binary_sha256"]):
            failures.append({"kind": "run_policy_or_binary_hash", "group": name})
        groups.append({"directory": str(path.relative_to(HERE)), "case_runs": len(entries),
                       "status_counts": dict(Counter(row["status"] for row in entries)),
                       "binary_sha256": run["binary_sha256"], "feature_flags": run["feature_flags"],
                       "run_sha256": digest(path / "run.json"), "results_sha256": digest(path / "results.json"),
                       "summary_sha256": digest(path / "summary.json"),
                       "manifest_sha256": run["manifest_sha256"], "fixture_types_sha256": run["fixture_types_sha256"]})
        failures.extend(summary["failures"])
        for row in entries:
            row_key = key(row)
            rows[row_key] = row
            source_path = Path(row["source"])
            sources[str(source_path.relative_to(HERE.parents[1]))] = row["source_sha256"]
            if digest(source_path) != row["source_sha256"]:
                failures.append({"kind": "current_source_hash_differs", "key": row_key})
            directory = path / "_".join(row_key)
            paths[row_key] = directory
            binding = {"key": row_key, "source_sha256": row["source_sha256"], "status": row["status"]}
            if row["status"] != "finite_regression_pass":
                bindings.append(binding)
                continue
            nodes = nodes_from(directory / "model.btor2")
            initialized = {int(node[2]) for node in nodes.values() if node[0] == "init"}
            required = {nid for nid, node in nodes.items() if node[0] == "state" and
                        nodes[int(node[1])][1] == "array" and nid not in initialized}
            if not (directory / "observation-model.btor2").read_bytes().startswith((directory / "model.btor2").read_bytes()):
                failures.append({"kind": "original_model_namespace_changed", "key": row_key})
            for field, filename in [("model_sha256", "model.btor2"), ("map_sha256", "model.map.json"),
                                    ("observations_sha256", "observation-model.btor2")]:
                actual = digest(directory / filename)
                binding[field] = actual
                if actual != row[field]:
                    failures.append({"kind": "model_map_observation_hash", "key": row_key, "field": field})
            fixture_traces += len(row["traces"])
            ub_traces += len(row.get("same_backend_constant_ub_observations", {}))
            for mode, trace in row["traces"].items():
                policy = read(directory / (mode + "-initial-state-policy.json"))
                frame0_lines = (directory / (mode + ".trace")).read_text().split("@0", 1)[0].splitlines()
                state_lines = set(frame0_lines[1:])
                state_ordinals = {nid: ordinal for ordinal, (nid, node) in
                                  enumerate((nid, node) for nid, node in nodes.items() if node[0] == "state")}
                expected_lines = set()
                widths_match = True
                for item in policy:
                    sort = nodes[int(nodes[item["node"]][1])]
                    width = int(nodes[int(sort[3])][2])
                    widths_match = widths_match and item["element_width"] == width
                    bits = (f"{61:08b}" * ((width + 7) // 8))[-width:]
                    expected_lines.add(f"{state_ordinals[item['node']]} [*] {bits}")
                matches = ({item["node"] for item in policy} == required and
                           policy == trace["explicit_uninitialized_array_states"] and
                           all(item["seed_byte"] == 61 and item["state_ordinal"] == state_ordinals[item["node"]] for item in policy) and
                           state_lines == expected_lines and widths_match and trace["all_inputs_explicitly_assigned"] and
                           trace["simulator_confirmed_steps"] == 512)
                if not matches:
                    failures.append({"kind": "initial_state_or_input_assignment", "key": row_key, "mode": mode})
                seeded_states += len(policy)
                binding[mode + "_trace_sha256"] = digest(directory / (mode + ".trace"))
            bindings.append(binding)
    historical = {}
    for name in ["finite-phase3-reviewed", "finite-phase3-reviewed-bv-fallback"]:
        historical.update({key(row): row for row in read(HERE / "results" / name / "results.json")})
    unchanged = 0
    for row_key, before in historical.items():
        after = rows[row_key]
        fields = ["source_sha256", "status"] + (["model_sha256", "map_sha256"] if before["status"] == "finite_regression_pass" else [])
        if all(before[field] == after[field] for field in fields):
            unchanged += 1
        else:
            failures.append({"kind": "historical_conversion_changed", "key": row_key})
    selected = []
    for row_key, row in sorted(rows.items()):
        if row_key[0] not in {"T1_original_nsqm_iff", "T2_symbolic_extent_small", "T2_symbolic_extent_large",
                              "T5_one_past_ub", "T8_free_ub"}:
            continue
        item = {"case": row_key[0], "architecture": row_key[1], "array": row_key[2],
                "model_sha256": row["model_sha256"],
                "map_sha256": row["map_sha256"], "traces": traces_summary(row)}
        if row_key[0] == "T1_original_nsqm_iff":
            item["source_abort_constraints"] = row["traces"]["fixed"]["source_abort_constraint_provenance"]
        if row_key[0].startswith("T2_"):
            storage = row["storage_structure"]
            item["storage"] = {name: storage[name] for name in ["native_symbolic_storage", "allocation_slots",
                                                                "element_bits", "index_bits", "offset_width"]}
        if row.get("same_backend_constant_ub_observations"):
            item["same_backend_constant_ub_observations"] = row["same_backend_constant_ub_observations"]
            item["ub_comparison_is_c_safety_proof"] = False
        selected.append(item)
    same_models = []
    for architecture in ["32", "64"]:
        for array in ["array", "mixed", "bv"]:
            a, b = rows[("T2_symbolic_extent_small", architecture, array)], rows[("T2_symbolic_extent_large", architecture, array)]
            same = a["source_sha256"] == b["source_sha256"] and a["model_sha256"] == b["model_sha256"]
            same_models.append({"architecture": architecture, "array": array, "same_source_and_model": same})
            if not same:
                failures.append({"kind": "different_N_model", "architecture": architecture, "array": array})
    seeds = []
    for path in sorted((HERE / "results/finite-phase3-explicit-state-seed-checks").glob("*/seed-check.result.json")):
        record = read(path)
        source = HERE / record["source_directory"]
        association = all(record[field] == digest(source / filename) for field, filename in [
            ("original_model_sha256", "model.btor2"), ("original_map_sha256", "model.map.json"),
            ("original_observation_model_sha256", "observation-model.btor2"), ("trace_sha256", "fixed.trace")])
        seeds.append({"directory": str(path.parent.relative_to(HERE)), "result_sha256": digest(path),
                      "model_map_observation_trace_hashes_checked": association,
                      "status": record["status"], "samples": record["samples"]})
        if record["status"] != "pass" or not association:
            failures.append({"kind": "seed_readback", "directory": str(path)})
    report = {"status": "pass" if not failures else "mismatch",
              "scope": "Supplied finite prefixes, parser/type checks, explicit no-init Array state seed coverage only; no solver/model checker or C safety/equivalence verdict.",
              "supersedes": "Only the no-init Array state seed coverage claim in finite-phase3-results.json. Historical conversion hashes and raw outputs remain unchanged.",
              "groups": groups, "case_runs": len(rows), "status_counts": dict(Counter(row["status"] for row in rows.values())),
              "fixture_simulation_traces": fixture_traces, "same_backend_constant_ub_traces": ub_traces,
              "initial_seed_readback_traces": len(seeds), "total_finite_simulation_traces": fixture_traces + ub_traces + len(seeds),
              "array_seed_byte": 61, "seeded_no_init_array_state_assignments_across_fixture_traces": seeded_states,
              "all_no_init_array_states_explicitly_assigned_and_initialized_states_excluded": not any(f["kind"] == "initial_state_or_input_assignment" for f in failures),
              "historical_configurations_with_unchanged_source_status_model_map": unchanged,
              "historical_configurations_checked": len(historical),
              "source_hashes": dict(sorted(sources.items())),
              "all_configuration_source_model_map_observation_trace_bindings_sha256": hashlib.sha256(json.dumps(sorted(bindings, key=lambda b: b["key"]), sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
              "different_N_same_model": same_models, "seed_readback_checks": seeds,
              "T1_T2_UB_evidence": selected, "validation_failures": failures}
    (HERE / "phase3-explicit-state-recheck.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({name: report[name] for name in ["status", "case_runs", "status_counts", "total_finite_simulation_traces", "validation_failures"]}, indent=2))
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
