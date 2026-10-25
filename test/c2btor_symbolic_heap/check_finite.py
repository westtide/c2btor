#!/usr/bin/env python3
"""Replay fully supplied finite traces; no solver or model checker is invoked."""

import argparse
import importlib.util
import json
from pathlib import Path
import re
import shutil
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def save(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def load_helpers():
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location(
        "existing_c2btor_finite_helpers", ROOT / "scripts/check_c2btor_optimizations.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def executed_node(entry, nodes):
    output = entry.get("executed_output")
    if not output or nodes[int(output)][0] != "output":
        raise ValueError("finite replay requires LBE executed-output observations")
    return int(nodes[int(output)][1])


def prepare_observations(case, source, model, mapping, directory, helpers):
    nodes = helpers.nodes_from(model)
    bool_sort = next(nid for nid, node in nodes.items() if node == ["sort", "bitvec", "1"])
    new_id = max(nodes)
    appended = []

    def alias(nid, signal):
        nonlocal new_id
        sort = int(nodes[nid][1])
        if nodes[sort][1] != "bitvec":
            raise ValueError("observation must name a bitvector node")
        new_id += 1
        appended.append(f"{new_id} or {sort} {nid} {nid} {signal}")
        return {"signal": signal, "node": nid, "width": int(nodes[sort][2])}

    properties = []
    for ordinal, prop in enumerate(mapping["source_properties"]):
        matches = [entry for entry in mapping["instructions"]
                   if entry["kind"] == "ASSERT" and entry.get("property_id") == prop["property_id"]]
        if len(matches) != 1 or not prop.get("condition_node"):
            raise ValueError("source ASSERT is absent, eliminated, or ambiguous")
        properties.append({"property_id": prop["property_id"], "source": prop["source"],
                           "failure": alias(int(prop["condition_node"]), f"__symheap_bad_{ordinal}"),
                           "executed": alias(executed_node(matches[0], nodes), f"__symheap_assert_exec_{ordinal}")})
    if len(properties) != case["expected_source_properties"]:
        raise ValueError("source property count differs from the fixture contract")
    bads = [alias(int(node[1]), f"__symheap_root_bad_{ordinal}")
            for ordinal, node in enumerate(node for node in nodes.values() if node[0] == "bad")]
    if len(bads) != 1:
        raise ValueError("expected exactly the merged source bad")
    constraints = []
    for ordinal, node in enumerate(node for node in nodes.values() if node[0] == "constraint"):
        name = node[2] if len(node) > 2 else ""
        match = re.fullmatch(r"assume_at_loc_(\d+)", name)
        assumptions = [entry for entry in mapping["instructions"] if entry["kind"] == "ASSUME" and
                       match and int(entry["goto_location"]) == int(match[1])]
        if (case["name"] != "T1_original_nsqm_iff" or len(assumptions) != 1 or
            assumptions[0]["source"].get("file_name") != "<builtin-library-abort>" or
            assumptions[0]["source"].get("function") != "abort"):
            raise ValueError("constraint has no accepted source-abort ASSUME provenance")
        constraints.append({**alias(int(node[1]), f"__symheap_constraint_{ordinal}"),
                            "constraint_name": name, "source": assumptions[0]["source"],
                            "goto_location": assumptions[0]["goto_location"]})
    pc_alias = alias(int(mapping["pc_node"]), "__symheap_pc")
    terminal_pcs = [int(entry["pc"]) for entry in mapping["instructions"]
                    if entry["kind"] == "END_FUNCTION" and
                    (not entry["successors"] or entry["goto_location"] in entry["successors"])]

    calls = []
    for entry in mapping["instructions"]:
        if not entry.get("nondet_function") or entry.get("source", {}).get("file_name") != str(source):
            continue
        value = int(entry.get("value_node", 0))
        candidates = ([value] if value in nodes and nodes[value][0] == "input" else
                      [nid for nid, node in nodes.items() if node[0] == "input" and
                       int(entry["first_node"]) <= nid <= int(entry["last_node"])])
        if len(candidates) != 1:
            raise ValueError("cannot associate a source nondet call with one emitted input")
        calls.append({"function": entry["nondet_function"], "input_node": candidates[0],
                      "result_state_node": entry.get("result_state_node"),
                      "executed": alias(executed_node(entry, nodes), f"__symheap_call_exec_{len(calls)}")})
    if len(calls) != len(case["inputs"]) or len({call["input_node"] for call in calls}) != len(calls):
        raise ValueError("source nondet call/input cardinality differs from the manifest")
    requested = dict(case.get("observations", {}))
    requested.update(case.get("observations_by_architecture", {}).get(case["architecture"], {}))
    for name in case.get("ub_observations", []):
        requested[name] = None
    values = []
    for name, expected in requested.items():
        matches = [entry for entry in mapping["instructions"]
                   if entry.get("assign_symbol") == name and
                   entry.get("source", {}).get("file_name") == str(source) and
                   entry.get("source", {}).get("function") != "__CPROVER_initialize"]
        if len(matches) != 1 or not matches[0].get("value_node"):
            raise ValueError("assignment observation is absent or ambiguous: " + name)
        entry = matches[0]
        values.append({"name": name, "expected_unsigned_value": expected,
                       "value": alias(int(entry["value_node"]), f"__symheap_value_{len(values)}"),
                       "executed": alias(executed_node(entry, nodes), f"__symheap_value_exec_{len(values)}")})
    # Preserve the last requested signal in BtorSim versions with id < max_id.
    new_id += 1
    appended.append(f"{new_id} zero {bool_sort}")
    observed = directory / "observation-model.btor2"
    observed.write_text(model.read_text() + "\n; Finite regression observation aliases only\n" +
                        "\n".join(appended) + "\n")
    if not observed.read_bytes().startswith(model.read_bytes()):
        raise ValueError("observation model must preserve original bytes and source namespace markers")
    info = {"properties": properties, "bad_roots": bads, "constraints": constraints,
            "source_calls": calls, "values": values, "aliases_added": len(appended),
            "pc": pc_alias, "terminal_self_loop_pcs": terminal_pcs,
            "original_node_ids_and_source_namespace_preserved": True,
            "source_map_binding_scope": "original model; appended observation model has its own hash"}
    save(directory / "observations.json", info)
    return nodes, observed, info


def repeated_byte_seed(width, byte):
    # Low bits also define a consistent seed for any non-byte metadata arrays.
    return int((f"{byte:08b}" * ((width + 7) // 8))[-width:], 2)


def write_trace(nodes, case, info, frames, mode, pilot_calls, path, array_seed_byte=None):
    inputs = [(nid, node) for nid, node in nodes.items() if node[0] == "input"]
    fixed = {call["input_node"]: value for call, value in zip(info["source_calls"], case["inputs"])}
    call_frames = {call["input_node"]: pilot_calls[ordinal][0]
                   for ordinal, call in enumerate(info["source_calls"])} if pilot_calls else {}
    trace = ["#0"]
    initializers = {int(node[2]) for node in nodes.values() if node[0] == "init"}
    initial_states = []
    for ordinal, (nid, node) in enumerate((nid, node) for nid, node in nodes.items() if node[0] == "state"):
        sort = nodes[int(node[1])]
        if nid in initializers or sort[1] != "array":
            continue
        width = int(nodes[int(sort[3])][2])
        byte = 0 if array_seed_byte is None else array_seed_byte
        seed = repeated_byte_seed(width, byte)
        trace.append(f"{ordinal} [*] {seed:0{width}b}")
        initial_states.append({"state_ordinal": ordinal, "node": nid,
                               "symbol": node[2] if len(node) > 2 else None,
                               "seed_byte": byte, "element_width": width,
                               "seed_policy": "explicit arbitrary initial Array value at #0; initialized states excluded"})
    policies = []
    for ordinal, (nid, node) in enumerate(inputs):
        sort = nodes[int(node[1])]
        policies.append({"ordinal": ordinal, "node": nid, "symbol": node[2] if len(node) > 2 else None,
                         "source_nondet": nid in fixed, "sort": sort,
                         "seed_policy": "constant repeated byte pattern" if sort[1] == "array" and array_seed_byte is not None else
                                        "constant source value" if nid in fixed and mode == "fixed" else
                                        "source value at executed call; changing port otherwise" if nid in fixed else
                                        "zero input/array seed" if mode == "fixed" else "deterministic frame-varying seed"})
    for frame in range(frames + 1):
        trace.append(f"@{frame}")
        for ordinal, (nid, node) in enumerate(inputs):
            sort = nodes[int(node[1])]
            seed = 0 if mode == "fixed" else 17 * frame + ordinal + 1
            if nid in fixed:
                if mode == "fixed" or frame == call_frames[nid]:
                    seed = fixed[nid]
                else:
                    # Ensure a later read cannot accidentally see the chosen value.
                    seed = fixed[nid] + 1 + frame % 7
            if sort[1] == "bitvec":
                width = int(sort[2])
                if width > 1048576:
                    raise ValueError("trace would materialize an enormous BV input")
                trace.append(f"{ordinal} {seed % (1 << width):0{width}b}")
            elif sort[1] == "array":
                width = int(nodes[int(sort[3])][2])
                if array_seed_byte is not None:
                    seed = repeated_byte_seed(width, array_seed_byte)
                trace.append(f"{ordinal} [*] {seed % (1 << width):0{width}b}")
            else:
                raise ValueError("unsupported input sort")
    trace.extend([".", ""])
    path.write_text("\n".join(trace))
    return policies, initial_states


def bit_value(snapshot, alias):
    bits = snapshot.get(alias["signal"], "")
    if len(bits) != alias["width"] or set(bits) - {"0", "1"}:
        raise ValueError("nonconcrete or missing observation: " + alias["signal"])
    return int(bits, 2)


def check_frames(case, info, frames, requested_frames):
    property_frames = {entry["property_id"]: [] for entry in info["properties"]}
    failures = {entry["property_id"]: [] for entry in info["properties"]}
    calls = [[] for _ in info["source_calls"]]
    observations = {entry["name"]: [] for entry in info["values"]}
    first_invalid = None
    valid_frames = 0
    for frame, snapshot in sorted(frames.items()):
        if any(bit_value(snapshot, constraint) == 0 for constraint in info["constraints"]):
            first_invalid = frame
            break
        valid_frames += 1
        any_source_failure = False
        for prop in info["properties"]:
            executed = bit_value(snapshot, prop["executed"])
            bad = bit_value(snapshot, prop["failure"])
            if bad and not executed:
                raise ValueError("source bad occurred outside its ASSERT execution")
            if executed:
                property_frames[prop["property_id"]].append(frame)
            if bad:
                failures[prop["property_id"]].append(frame)
                any_source_failure = True
        if bool(bit_value(snapshot, info["bad_roots"][0])) != any_source_failure:
            raise ValueError("merged bad differs from source-property observations")
        for ordinal, call in enumerate(info["source_calls"]):
            if bit_value(snapshot, call["executed"]):
                calls[ordinal].append(frame)
        for value in info["values"]:
            if bit_value(snapshot, value["executed"]):
                observations[value["name"]].append({"frame": frame,
                    "unsigned_value": bit_value(snapshot, value["value"])})
    if any(not frames for frames in property_frames.values()):
        raise ValueError("source assertion was never executed (including early-return paths)")
    if any(len(frames) != 1 for frames in calls):
        raise ValueError("each fixture source nondet call must execute exactly once")
    want_failure = case["name"] == "T1_original_nsqm_iff"
    if want_failure != any(failures.values()):
        raise ValueError("executed source assertion failure differs from the supplied-trace expectation")
    if first_invalid is not None and not want_failure:
        raise ValueError("a constraint failed on a positive fixture")
    for value in info["values"]:
        seen = observations[value["name"]]
        if len(seen) != 1:
            raise ValueError("assignment observation must execute exactly once: " + value["name"])
        expected = value["expected_unsigned_value"]
        if expected is not None and seen[0]["unsigned_value"] != expected:
            raise ValueError("assignment value differs: " + value["name"])
    return {"frames_observed": len(frames), "valid_prefix_frames": valid_frames,
            "first_constraint_violation_frame": first_invalid,
            "source_abort_constraint_provenance": info["constraints"],
            "source_assertion_execution_frames": property_frames,
            "source_failure_frames": failures, "source_nondet_call_frames": calls,
            "observed_values": observations,
            "source_property_behavior": "supplied source failure" if want_failure else "no source failure in executed prefix",
            "contains_deliberate_ub": bool(case.get("ub_observations")),
            "source_may_contain_ub": bool(case.get("source_may_have_ub")),
            "scope": "fully supplied finite execution; no C SAFE/UNSAFE verdict"}


def simulate_trace(case, args, directory, nodes, observed, info, helpers, mode, pilot_calls=None):
    trace = directory / (mode + ".trace")
    policies, initial_states = write_trace(nodes, case, info, args.frames, mode, pilot_calls, trace, args.array_seed_byte)
    save(directory / (mode + "-input-policy.json"), policies)
    save(directory / (mode + "-initial-state-policy.json"), initial_states)
    outcome = helpers.run([args.btorsim.resolve(), "-v", "--states", "--vcd",
                           directory / (mode + ".vcd"), observed, trace], directory,
                          mode + "-simulation", args.simulation_timeout, 0,
                          file_limit_mib=args.file_limit_mib)
    if outcome["status"] != "finished" or outcome["returncode"]:
        raise ValueError("finite simulator did not finish: " + json.dumps(outcome))
    stdout = (directory / (mode + "-simulation.stdout")).read_text()
    completed = re.search(r"finished parsing k\s*=\s*(\d+) frames", stdout)
    if not completed or int(completed[1]) != args.frames:
        raise ValueError("simulator stdout does not confirm the requested supplied steps")
    raw_frames = helpers.vcd_frames(directory / (mode + ".vcd"))
    if not raw_frames or 0 not in raw_frames:
        raise ValueError("simulator VCD lacks an initial frame")
    last_frame = max(raw_frames)
    static_suffix = last_frame < args.frames
    terminal_pc = None
    if static_suffix:
        terminal_pc = bit_value(raw_frames[last_frame], info["pc"])
        if terminal_pc not in info["terminal_self_loop_pcs"]:
            raise ValueError("missing VCD suffix is not at a mapped terminal PC self-loop")
    # VCD contains changes, so carry the last complete signal valuation.
    frames, latest = {}, None
    for frame in range(args.frames + 1):
        if frame in raw_frames:
            latest = raw_frames[frame]
        if latest is None:
            raise ValueError("VCD frame cannot be reconstructed")
        frames[frame] = latest
    result = check_frames(case, info, frames, args.frames)
    result.update({"status": "finite_regression_pass", "simulation": outcome, "trace_mode": mode,
                   "all_inputs_explicitly_assigned": True, "input_count": len(policies),
                   "simulator_confirmed_steps": int(completed[1]), "raw_vcd_frames": len(raw_frames),
                   "raw_vcd_last_frame": last_frame, "static_vcd_suffix_carried": static_suffix,
                   "terminal_self_loop_pc_if_carried": terminal_pc,
                   "array_seed_byte": args.array_seed_byte,
                   "explicit_uninitialized_array_states": initial_states})
    save(directory / (mode + ".result.json"), result)
    return result


def storage_structure(case, args, model, mapping, helpers):
    nodes = helpers.nodes_from(model)
    memory = mapping["memory"]
    symbolic = memory.get("symbolic_heap", {})
    objects = memory.get("object_storage", [])
    first_heap = memory["first_heap_tag"]
    slots = memory.get("allocation_storage_slots", 0)
    dynamic_objects = [obj for obj in objects if first_heap <= obj["tag"] < first_heap + slots]
    array_states = [nid for nid, node in nodes.items() if node[0] == "state" and
                    nodes[int(node[1])][1] == "array"]
    data_states = [int(obj["states"]["data"]) for obj in dynamic_objects if "data" in obj["states"]]
    size_states = [int(obj["states"]["size"]) for obj in dynamic_objects if "size" in obj["states"]]
    other_array_states = [int(obj["states"]["data"]) for obj in objects if obj not in dynamic_objects and
                          "data" in obj["states"] and int(obj["states"]["data"]) in array_states]
    zero_helpers = [nid for nid in array_states if len(nodes[nid]) > 2 and
                    nodes[nid][2].startswith("__zero_object_array_")]
    native = bool(symbolic.get("native_array_storage"))
    requested_compact = "--goto-btor2-symbolic-heap-compact" in args.feature_flag
    info = {"native_symbolic_storage": native,
            "allocation_slots": memory.get("allocation_storage_slots"),
            "active_data_state_nodes": data_states, "active_size_state_nodes": size_states,
            "total_array_state_nodes": array_states, "zero_helper_array_state_nodes": zero_helpers,
            "other_object_array_state_nodes": other_array_states,
            "element_bits": [obj["element_bits"] for obj in dynamic_objects],
            "index_bits": [obj["index_bits"] for obj in dynamic_objects],
            "offset_width": memory["offset_width"],
            "compact_enabled": symbolic.get("compact_enabled", False),
            "word64_certified": symbolic.get("word64_certified", False),
            "cell_certificate_accesses": symbolic.get("cell_certificate_accesses"),
            "cell_certificate_reason": symbolic.get("cell_certificate_reason")}
    expected_slots = case.get("expected_allocation_slots")
    if expected_slots is not None and memory.get("allocation_storage_slots") != expected_slots:
        raise ValueError("allocation storage-slot count differs from the source fixture")
    if len(data_states) != len(set(data_states)) or len(size_states) != len(set(size_states)):
        raise ValueError("distinct objects share a data/size state")
    expect_native = case.get("expected_symbolic_storage") or case["array"] in case.get("expected_symbolic_storage_configs", [])
    if expect_native and not native:
        raise ValueError("non-singleton fixture did not select symbolic native storage")
    if requested_compact and native:
        if not symbolic.get("compact_enabled"):
            raise ValueError("compact requested but metadata is disabled")
        if len(array_states) != len(data_states) + len(zero_helpers) + len(other_array_states):
            raise ValueError("compact symbolic model retains duplicate/helper Array storage")
        if len(data_states) != expected_slots or len(size_states) != expected_slots:
            raise ValueError("compact symbolic slots do not retain one data/size state each")
        word = bool(symbolic.get("word64_certified"))
        expected_bits = 64 if word else 8
        expected_index = memory["offset_width"] - (3 if word else 0)
        if any(obj["element_bits"] != expected_bits or obj["index_bits"] != expected_index
               for obj in dynamic_objects):
            raise ValueError("cell representation does not match its certificate/byte fallback")
        if case["name"] == "T1_original_nsqm_iff":
            if (not word or len(array_states) != 2 or len(data_states) != 2 or
                len(size_states) != 2 or zero_helpers or expected_index != 29):
                raise ValueError("nsqm compact contract requires two word64/index29 data and size states, no zero helper")
        if case["name"] == "T8_symbolic_mixed_bytes" and word:
            raise ValueError("mixed-byte source must fail uniform word certification")
    if requested_compact and case["name"] == "T8_legal_mixed_bytes" and symbolic.get("word64_certified"):
        raise ValueError("constant mixed-byte source unexpectedly claims a word certificate")
    return info


def execute(case, args, directory, helpers, manifest, source=None):
    directory.mkdir(parents=True)
    source = source or (HERE / case["source"]).resolve()
    model, map_path = directory / "model.btor2", directory / "model.map.json"
    # LBE maps carry instruction-executed/value outputs. This model is separate
    # from the no-LBE models used for conversion/hash compatibility metrics.
    options = [option for option in manifest["common_options"] if option != "--goto-btor2-no-lbe"]
    command = [args.c2btor, source, "--" + case["architecture"], *options,
               "--goto-btor2-lbe", "--array", case["array"], *args.feature_flag,
               "-I", HERE, "--goto-btor2-out", model, "--goto-btor2-map-out", map_path]
    converted = helpers.run(command, directory, "conversion", args.conversion_timeout, 0,
                            file_limit_mib=args.file_limit_mib)
    log = (directory / "conversion.stdout").read_text() + (directory / "conversion.stderr").read_text()
    result = {"case": case["name"], "architecture": case["architecture"], "array": case["array"],
              "source": str(source), "source_sha256": helpers.digest(source), "conversion": converted,
              "model_checking_run": False, "solver_run": False, "finite_simulation_run": False}
    if converted["status"] != "finished" or converted["returncode"]:
        expected = (case["name"] == "T6_unbounded_event_count" or
                    case["name"].startswith("boundary_") and "--goto-btor2-symbolic-heap-wide-offsets" in args.feature_flag or
                    case["array"] == "bv" and ("bit-vector" in log or "bitvector" in log))
        no_model = not model.exists() or not model.stat().st_size
        result.update({"status": "expected_rejection" if expected and no_model and
                       converted["status"] == "finished" else "conversion_incomplete",
                       "diagnostic_tail": log.splitlines()[-12:], "no_nonempty_model": no_model})
        if case["name"] == "T6_unbounded_event_count" and "finite allocation count" not in log:
            result["status"] = "rejection_reason_mismatch"
        save(directory / "case.result.json", result)
        return result
    for stage, path in (("parser", model),):
        parsed = helpers.run([args.catbtor.resolve(), path], directory, stage,
                             args.parser_timeout, 0, discard_stdout=True)
        if parsed["status"] != "finished" or parsed["returncode"]:
            raise ValueError("model parser/type check failed")
        result[stage] = parsed
    mapping = json.loads(map_path.read_text())
    result["storage_structure"] = storage_structure(case, args, model, mapping, helpers)
    nodes, observed, info = prepare_observations(case, source, model, mapping, directory, helpers)
    parsed = helpers.run([args.catbtor.resolve(), observed], directory, "observation-parser",
                         args.parser_timeout, 0, discard_stdout=True)
    if parsed["status"] != "finished" or parsed["returncode"]:
        raise ValueError("observation model parser/type check failed")
    fixed = simulate_trace(case, args, directory, nodes, observed, info, helpers, "fixed")
    traces = {"fixed": fixed}
    if case["name"] == "T7_nondet_latch" or args.vary_all_source_inputs:
        traces["varying"] = simulate_trace(case, args, directory, nodes, observed, info, helpers,
                                          "varying", fixed["source_nondet_call_frames"])
    result.update({"status": "finite_regression_pass", "finite_simulation_run": True, "traces": traces,
                   "model_sha256": helpers.digest(model), "map_sha256": helpers.digest(map_path),
                   "observations_sha256": helpers.digest(observed),
                   "observation_model_used_for_conversion_hash_comparison": False,
                   "original_node_ids_and_source_namespace_preserved": True,
                   "source_map_binding_scope": "original model; map is never rewritten for observation aliases"})
    save(directory / "case.result.json", result)
    return result


def probe_malloc_options(args, output, helpers):
    records = []
    source = HERE / "t4_same_object_alias.c"
    for flag in ["--malloc-may-fail", "--malloc-fail-null", "--no-malloc-may-fail"]:
        directory = output / ("cli-probe-" + flag[2:])
        directory.mkdir()
        model = directory / "model.btor2"
        outcome = helpers.run([args.c2btor, source, "--goto-btor2", "--inline", flag,
                               "--goto-btor2-out", model], directory, "probe", 10, 0)
        log = (directory / "probe.stdout").read_text() + (directory / "probe.stderr").read_text()
        records.append({"flag": flag, "outcome": outcome,
                        "unknown_option": bool(re.search(r"unknown option", log, re.IGNORECASE)),
                        "model_exists": model.exists(), "diagnostic_tail": log.splitlines()[-5:]})
    save(output / "malloc-cli-probes.json", records)
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c2btor", type=Path, default=ROOT / "build/bin/c2btor")
    parser.add_argument("--catbtor", type=Path, default=Path("/Users/west/Developer/btor2tools/build/bin/catbtor"))
    parser.add_argument("--btorsim", type=Path, default=Path("/Users/west/Developer/btor2tools/build/bin/btorsim"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--architectures", default="32,64")
    parser.add_argument("--arrays", default="array")
    parser.add_argument("--feature-flag", action="append", default=[])
    parser.add_argument("--case-filter", action="append", default=[])
    parser.add_argument("--frames", type=int, default=512)
    parser.add_argument("--vary-all-source-inputs", action="store_true")
    parser.add_argument("--array-seed-byte", type=lambda value: int(value, 0), default=0,
                        help="fill every Array element with this repeated byte (default 0; e.g. 0x3d); constant across frames")
    parser.add_argument("--freeze-binary", action="store_true")
    parser.add_argument("--conversion-timeout", type=float, default=20)
    parser.add_argument("--parser-timeout", type=float, default=10)
    parser.add_argument("--simulation-timeout", type=float, default=30)
    parser.add_argument("--file-limit-mib", type=int, default=64)
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.c2btor = args.c2btor.resolve()
    if not args.output.is_relative_to(HERE) or args.output.exists():
        parser.error("output must be a fresh directory within test/c2btor_symbolic_heap")
    if args.frames <= 0 or args.frames > 10000:
        parser.error("frames must be between 1 and 10000")
    if args.array_seed_byte is not None and not 0 <= args.array_seed_byte <= 255:
        parser.error("array-seed-byte must be between 0 and 255")
    if any(value not in {"32", "64"} for value in args.architectures.split(",")):
        parser.error("architectures must be 32 and/or 64")
    if any(value not in {"bv", "array", "mixed"} for value in args.arrays.split(",")):
        parser.error("arrays must be bv, array and/or mixed")
    args.output.mkdir(parents=True)
    helpers = load_helpers()
    if args.freeze_binary:
        frozen = args.output / "c2btor.frozen"
        shutil.copy2(args.c2btor, frozen)
        args.c2btor = frozen
    manifest = json.loads((HERE / "cases.json").read_text())
    save(args.output / "run.json", {
        "scope": "fully supplied finite BtorSim execution; no solver/model checker or C safety verdict",
        "binary": str(args.c2btor), "binary_sha256": helpers.digest(args.c2btor),
        "feature_flags": args.feature_flag, "frames": args.frames,
        "array_seed_byte": args.array_seed_byte,
        "array_seed_policy": "constant repeated byte in every element width" if args.array_seed_byte is not None else "existing zero/frame-varying seed policy",
        "malloc_policy": "existing BTOR2 success-none policy; no failure input synthesized",
        "manifest_sha256": helpers.digest(HERE / "cases.json"),
        "fixture_types_sha256": helpers.digest(HERE / "fixture_types.h"),
        "memory_limit": None, "peak_rss": None})
    probes = probe_malloc_options(args, args.output, helpers)
    results = []
    for item in manifest["cases"]:
        if args.case_filter and not any(re.search(pattern, item["name"]) for pattern in args.case_filter):
            continue
        for architecture in args.architectures.split(","):
            if architecture not in item["architectures"]:
                continue
            for array in args.arrays.split(","):
                case = {**item, "architecture": architecture, "array": array}
                directory = args.output / f"{item['name']}_{architecture}_{array}"
                try:
                    result = execute(case, args, directory, helpers, manifest)
                    if case.get("ub_observations") and result["status"] == "finite_regression_pass":
                        constant_dir = directory / "constant-counterpart"
                        constant_dir.mkdir()
                        source = constant_dir / Path(case["source"]).name
                        original = (HERE / case["source"]).read_text()
                        replacement = "malloc(24U)" if item["name"] == "T5_one_past_ub" else "malloc(16U)"
                        pattern = "malloc(sizeof(*p) * (size_t)n)"
                        if original.count(pattern) != 1:
                            raise ValueError("constant counterpart allocation replacement is ambiguous")
                        source.write_text(original.replace(pattern, replacement))
                        counterpart = execute(case, args, constant_dir / "replay", helpers, manifest, source.resolve())
                        if counterpart["status"] != "finite_regression_pass":
                            raise ValueError("same-backend constant counterpart did not replay")
                        pairs = {}
                        for mode, replay in result["traces"].items():
                            pairs[mode] = {}
                            for name in case["ub_observations"]:
                                actual = [entry["unsigned_value"] for entry in replay["observed_values"][name]]
                                expected = [entry["unsigned_value"] for entry in counterpart["traces"][mode]["observed_values"][name]]
                                if actual != expected:
                                    raise ValueError("same-backend UB totalization observation differs: " + name)
                                pairs[mode][name] = actual
                        result["same_backend_constant_ub_observations"] = pairs
                        result["ub_comparison_is_c_safety_proof"] = False
                        save(directory / "case.result.json", result)
                except Exception as error:
                    result = {"case": item["name"], "architecture": architecture, "array": array,
                              "status": "finite_regression_error", "error": str(error),
                              "model_checking_run": False, "solver_run": False}
                    directory.mkdir(parents=True, exist_ok=True)
                    save(directory / "case.result.json", result)
                results.append(result)
                save(args.output / "results.json", results)
                print(f"{item['name']} --{architecture} {array}: {result['status']}", flush=True)
    failures = [result for result in results if result["status"] not in {"finite_regression_pass", "expected_rejection"}]
    summary = {"scope": "supplied finite executions and explicit rejection checks only; no C safety verdict",
               "case_runs": len(results), "status": "pass" if not failures else "mismatch",
               "malloc_options_rejected_by_current_cli": all(record["unknown_option"] for record in probes),
               "malloc_policy_note": "The current BTOR2 CLI forces success-none and does not register these malloc failure options. AGENTS.md's general malloc-failure-input statement does not describe this CLI path.",
               "failures": failures}
    save(args.output / "summary.json", summary)
    print(json.dumps({"case_runs": len(results), "status": summary["status"], "failures": len(failures)}))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
