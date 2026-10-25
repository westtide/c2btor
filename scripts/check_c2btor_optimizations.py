#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors
"""Compare converter snapshots using finite regressions and structural metrics.

No model checker is invoked. Regression traces assign every input explicitly and
check source-property observations over a finite prefix. Metrics conversions omit
maps, because map-only witness observations affect the model size.
"""

import argparse
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "test/c2btor_optimizations"
CONFIGS = {"bv": "bv", "array": "array", "mixed": "mixed"}
CONFIG_ALIASES = {"ob": "bv", "oa": "array"}
METRIC_KEYS = ("state_count", "bitvec_state_bits", "array_state_count",
               "instruction_positions", "pc_positions", "active_pc_entries",
               "pc_equality_guards", "numeric_nodes", "read_ops", "write_ops",
               "model_bytes")


def save(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def digest(path):
    hasher = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def tree_rss(pid):
    rows = subprocess.check_output(["ps", "-axo", "pid=,ppid=,rss="], text=True)
    processes = [tuple(map(int, line.split())) for line in rows.splitlines()]
    members = {pid}
    while True:
        children = {child for child, parent, _ in processes if parent in members}
        if children <= members:
            break
        members |= children
    return sum(rss for child, _, rss in processes if child in members) * 1024


def run(command, directory, stage, timeout, memory_gib, discard_stdout=False, file_limit_mib=0):
    command = [str(value) for value in command]
    save(directory / (stage + ".command.json"), command)
    launch = command
    if file_limit_mib:
        # Avoid preexec_fn in worker threads: set the inherited limit in a
        # short-lived Python wrapper, then replace that process with the tool.
        wrapper = ("import os,resource,sys; n=int(sys.argv[1]); "
                   "resource.setrlimit(resource.RLIMIT_FSIZE,(n,n)); "
                   "os.execv(sys.argv[2],sys.argv[2:])")
        launch = [sys.executable, "-c", wrapper, str(int(file_limit_mib * 1024 ** 2)), *command]
        save(directory / (stage + ".resource-limit.json"), {"max_output_file_bytes": int(file_limit_mib * 1024 ** 2)})
    start = time.monotonic()
    status, peak = "finished", 0
    with (directory / (stage + ".stdout")).open("w") as stdout, \
            (directory / (stage + ".stderr")).open("w") as stderr:
        process = subprocess.Popen(launch, stdout=subprocess.DEVNULL if discard_stdout else stdout,
                                   stderr=stderr, start_new_session=True)
        try:
            while process.poll() is None:
                if memory_gib:
                    peak = max(peak, tree_rss(process.pid))
                    if peak > memory_gib * 1024 ** 3:
                        status = "memory_limit"
                        break
                if time.monotonic() - start >= timeout:
                    status = "timeout"
                    break
                time.sleep(0.1)
        finally:
            if process.poll() is None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            returncode = process.wait()
    if returncode == -signal.SIGXFSZ:
        status = "file_size_limit"
    elif file_limit_mib and returncode:
        limit_bytes = int(file_limit_mib * 1024 ** 2)
        outputs = [directory / (stage + ".stdout"), directory / (stage + ".stderr"),
                   directory / "model.btor2", directory / "model.map.json"]
        # C++ streams can catch EFBIG and return an ordinary conversion error
        # instead of terminating with SIGXFSZ. Retain the resource cause.
        if any(path.exists() and path.stat().st_size >= limit_bytes for path in outputs):
            status = "file_size_limit"
    result = {"status": status, "returncode": returncode,
              "wall_seconds": round(time.monotonic() - start, 6),
              "sampled_peak_rss_bytes": peak if memory_gib else None}
    save(directory / (stage + ".result.json"), result)
    return result


def nodes_from(path):
    nodes = {}
    with path.open() as stream:
        for line in stream:
            words = line.split(";", 1)[0].split()
            if words:
                nodes[int(words[0])] = words[1:]
    return nodes


def structural_metrics(model, conversion_log, mapping=None):
    nodes = nodes_from(model)
    counts = Counter(node[0] for node in nodes.values())
    states = [node for node in nodes.values() if node[0] == "state"]
    bv_states = [node for node in states if nodes[int(node[1])][1] == "bitvec"]
    pc = next((nid for nid, node in nodes.items()
               if node[0] == "state" and node[2:] == ["pc"]), None)
    pc_sort = nodes[pc][1] if pc is not None else None
    literals = {}
    for nid, node in nodes.items():
        # Only PC comparisons need concrete literals. Packed storage sorts can
        # have billions of bits; decoding their zero/ones values is unnecessary.
        if node[0] in {"zero", "one", "ones", "const", "constd", "consth"} and node[1] == pc_sort:
            width = int(nodes[int(node[1])][2])
            value = (0 if node[0] == "zero" else 1 if node[0] == "one" else
                     (1 << width) - 1 if node[0] == "ones" else
                     int(node[2], {"const": 2, "constd": 10, "consth": 16}[node[0]]))
            literals[nid] = value % (1 << width)
    guard_values, guard_count = set(), 0
    if pc is not None:
        for node in nodes.values():
            if node[0] == "eq" and str(pc) in node[2:4]:
                other = int(node[3] if node[2] == str(pc) else node[2])
                if other in literals:
                    guard_count += 1
                    guard_values.add(literals[other])
    locations = re.search(r"Collected (\d+) locations", conversion_log)
    lbe = re.search(r"Scalar LBE: (\d+) instructions -> (\d+) blocks", conversion_log)
    instruction_positions = int(locations[1]) if locations else None
    pc_positions = int(lbe[2]) if lbe else instruction_positions
    if mapping is not None:
        instruction_positions = len(mapping.get("instructions", []))
        pc_positions = (len(mapping["blocks"]) if "blocks" in mapping else
                        len({entry["pc"] for entry in mapping.get("instructions", [])}))
    return {"state_count": len(states),
            "bitvec_state_bits": sum(int(nodes[int(node[1])][2]) for node in bv_states),
            "array_state_count": len(states) - len(bv_states),
            "instruction_positions": instruction_positions, "pc_positions": pc_positions,
            "active_pc_entries": len(guard_values), "pc_equality_guards": guard_count,
            "numeric_nodes": len(nodes), "read_ops": counts["read"],
            "write_ops": counts["write"], "model_bytes": model.stat().st_size,
            "operation_counts": dict(sorted(counts.items())),
            "pc_entry_values": sorted(guard_values), "model_sha256": digest(model)}


def vcd_frames(path):
    identifiers, values, frames = {}, {}, {}
    timestamp = None

    def snapshot():
        if timestamp is not None and timestamp % 10 == 0:
            frames[timestamp // 10] = dict(values)

    with path.open() as stream:
        for line in stream:
            line = line.strip()
            fields = line.split()
            if fields[:2] == ["$var", "wire"] and len(fields) == 6:
                identifiers[fields[3]] = (fields[4], int(fields[2]))
            elif line.startswith("#"):
                snapshot()
                timestamp = int(line[1:])
            elif line.startswith("b") and len(fields) == 2 and fields[1] in identifiers:
                name, width = identifiers[fields[1]]
                bits = fields[0][1:]
                values[name] = bits.rjust(width, bits[0] if bits[0] in "xz" else "0")
            elif line and line[0] in "01xz" and line[1:] in identifiers:
                name, width = identifiers[line[1:]]
                values[name] = line[0] * width
    snapshot()
    return frames


def conversion_rejection(case, config, command):
    rules = list(case.get("conversion_rejections", []))
    if case.get("conversion_rejection_without_flag"):
        rules.append({"without_flag": case["conversion_rejection_without_flag"],
                      "message": case["conversion_rejection_message"]})
    for rule in rules:
        if config not in rule.get("configs", CONFIGS):
            continue
        if rule.get("with_flag") and rule["with_flag"] not in command:
            continue
        if rule.get("without_flag") and rule["without_flag"] in command:
            continue
        if not rule.get("message"):
            raise ValueError("expected conversion rejection requires a specific message")
        return rule
    return None


def check_array_storage(case, config, command, model, mapping):
    """Check the explicit representation contract, separately from replay."""
    checks = case.get("array_storage_checks", [])
    if not checks:
        return []
    enabled = "--goto-btor2-logical-arrays" in command
    memory = mapping["memory"]
    logical = memory.get("logical_arrays", [])
    objects = memory["objects"]
    reserved = memory.get("reserved_logical_array_identities", [])
    nodes = nodes_from(model)
    outcomes = []
    for request in checks:
        matches = lambda entries: [entry for entry in entries
                                   if re.search(request["symbol_regex"], entry["symbol"])]
        logical_matches, object_matches = matches(logical), matches(objects)
        expect_logical = enabled and request["logical_when_enabled"]
        if expect_logical:
            if len(logical_matches) != 1 or object_matches:
                raise ValueError(f"expected independent logical storage for {request['symbol_regex']}")
            entry = logical_matches[0]
            unused = request.get("unused_storage", False)
            if entry.get("unused_storage", False) != unused:
                raise ValueError("unexpected logical-array unused-storage classification")
            for key in ("rank", "element_width", "static_lifetime", "upper_elements"):
                if key in request and entry.get(key) != request[key]:
                    raise ValueError(f"logical-array {key} differs for {entry['symbol']}")
            dimensions = entry["dimensions"]
            block_local = (request.get("allow_block_local_storage", False) and
                           "--goto-btor2-array-blocks" in command and
                           "--goto-btor2-optimize-state" in command and
                           mapping.get("array_blocks", {}).get("enabled") and
                           mapping.get("array_blocks", {}).get("latest_storage_versions"))
            if len(dimensions) != entry["rank"] or sum(d["width"] for d in dimensions) != entry["index_width"]:
                raise ValueError("logical dimensions/rank/index width metadata disagree")
            latched = sum("state" in d for d in dimensions)
            if "latched_dimensions" in request and latched != request["latched_dimensions"]:
                dynamic = sum("constant" not in d for d in dimensions)
                if not block_local or latched > request["latched_dimensions"] or dynamic != request["latched_dimensions"]:
                    raise ValueError("VLA dimensions must retain the expected DECL-latched states")
            if entry["symbol"] not in reserved or memory["static_identity_count"] != len(objects) + len(reserved):
                raise ValueError("logical-array identity reservation metadata missing or inconsistent")
            if unused:
                if (entry["storage"] != "unused" or entry["semantics"] != "unused-element-storage" or
                        "data_state" in entry or any("state" in d for d in dimensions)):
                    raise ValueError("write-only logical array still has physical storage/dimension state")
                outcomes.append({"symbol": entry["symbol"], "storage": "unused", "logical": True,
                                 "tag": entry["tag"], "rank": entry["rank"], "unused_storage": True})
                continue
            if entry["semantics"] != "independent-element-storage":
                raise ValueError("unexpected logical-array semantics metadata")
            if "data_state" in entry:
                state = nodes[int(entry["data_state"])]
                if state[0] != "state":
                    raise ValueError("logical data_state does not name a declared state")
                storage_node = int(entry["data_state"])
            elif block_local:
                prefix = "__c2btor_elements_fresh$" + entry["symbol"] + "$"
                fresh = [nid for nid, node in nodes.items()
                         if node[0] == "input" and len(node) > 2 and node[2].startswith(prefix)]
                if len(fresh) != 1:
                    raise ValueError("pruned logical storage lacks one retained DECL storage input")
                storage_node = fresh[0]
            else:
                raise ValueError("logical data storage state is absent")
            sort = nodes[int(nodes[storage_node][1])]
            expected_storage = "bitvector" if config == "bv" else "array"
            if config == "mixed":
                limit = memory["array_mixed_threshold_bits"]
                upper = entry.get("upper_elements")
                expected_storage = "bitvector" if upper is not None and upper * entry["element_width"] <= limit else "array"
            if entry["storage"] != expected_storage:
                raise ValueError("logical-array storage does not follow the selected backend")
            if expected_storage == "array":
                if (sort[1] != "array" or int(nodes[int(sort[2])][2]) != entry["index_width"] or
                        int(nodes[int(sort[3])][2]) != entry["element_width"]):
                    raise ValueError("logical Array sort disagrees with its metadata")
            elif sort[1] != "bitvec":
                raise ValueError("logical packed BV storage has a non-bitvector sort")
            elif int(sort[2]) != max(1, entry["upper_elements"] * entry["element_width"]):
                raise ValueError("logical packed BV sort width disagrees with its element bound")
            outcomes.append({"symbol": entry["symbol"], "storage": entry["storage"],
                             "logical": True, "tag": entry["tag"], "rank": entry["rank"],
                             "latched_dimensions": latched,
                             "data_state_retained": "data_state" in entry,
                             "storage_sort_probe": storage_node,
                             "block_local_storage_permitted": bool(block_local)})
        else:
            if logical_matches or len(object_matches) != 1:
                raise ValueError(f"expected object-storage fallback for {request['symbol_regex']}")
            entry = object_matches[0]
            if not any(storage["tag"] == entry["tag"] and
                       (not request.get("require_object_data", True) or storage.get("states", {}).get("data"))
                       for storage in memory["object_storage"]):
                raise ValueError("fallback object lacks canonical byte-storage data state")
            outcomes.append({"symbol": entry["symbol"], "logical": False, "tag": entry["tag"]})
    return outcomes


def check_scalar_structure(case, command, model, mapping):
    nodes = nodes_from(model)
    outcomes = []
    for request in case.get("state_checks", []):
        if request.get("with_flag") and request["with_flag"] not in command:
            continue
        if request.get("without_flag") and request["without_flag"] in command:
            continue
        matches = [entry for entry in mapping["states"]
                   if re.search(request["symbol_regex"], entry["symbol"])]
        if bool(matches) != request["present"]:
            raise ValueError(f"state presence differs for {request['symbol_regex']}")
        if any(nodes.get(int(entry["node"]), [None])[0] != "state" for entry in matches):
            raise ValueError("mapped scalar state no longer names an emitted state")
        symbols = {entry[key] for entry in mapping["instructions"]
                   for key in ("decl_symbol", "assign_symbol", "dead_symbol")
                   if key in entry and re.search(request["symbol_regex"], entry[key])}
        if not matches and not symbols:
            raise ValueError("expected local scalar is absent from retained source instructions")
        source_values = [int(entry["value_node"]) for entry in mapping["instructions"]
                         if entry.get("value_node") and
                         any(entry.get(key) in symbols for key in ("decl_symbol", "assign_symbol"))]
        widths = {int(nodes[int(nodes[value][1])][2]) for value in source_values
                  if nodes[int(nodes[value][1])][1] == "bitvec"}
        if "width" in request and widths != {request["width"]}:
            raise ValueError("local scalar observations do not retain the expected bitvector type")
        declaration_inputs = {int(entry["value_node"]) for entry in mapping["instructions"]
                              if entry.get("decl_symbol") in symbols and entry.get("value_node") and
                              nodes[int(entry["value_node"])][0] == "input"}
        for symbol in symbols:
            name = symbol.rsplit("::", 1)[-1]
            name = "pc__2" if name == "pc" else re.sub(r"[^a-zA-Z0-9_]", "_", name)
            if not request["present"] and any(
                    node[0] == "input" and len(node) > 2 and
                    (node[2] == name or node[2].startswith(name + "_")) and
                    nid not in declaration_inputs for nid, node in nodes.items()):
                raise ValueError("eliminated local state was replaced by a free input")
        outcomes.append({"symbol_regex": request["symbol_regex"],
                         "present": request["present"], "symbols": sorted(symbols),
                         "state_nodes": [entry["node"] for entry in matches],
                         "observation_widths": sorted(widths),
                         "source_declaration_inputs": sorted(declaration_inputs)})
    if case.get("scalar_block_checks") and "--goto-btor2-scalar-blocks" in command:
        metadata = mapping.get("scalar_blocks", {})
        blocks = mapping.get("blocks", [])
        if not metadata.get("enabled") or not metadata.get("assume_boundary") or \
                metadata.get("runtime_blocks") != len(blocks):
            raise ValueError("scalar block metadata is missing or inconsistent")
        instructions = {entry["instruction_id"]: entry for entry in mapping["instructions"]}
        members = [member for block in blocks for member in block["instructions"]]
        if len(members) != len(set(members)) or set(members) != set(instructions):
            raise ValueError("scalar blocks do not partition retained instructions")
        merged_assertions = 0
        for block in blocks:
            for position, member in enumerate(block["instructions"]):
                entry = instructions[member]
                if (entry["kind"] == "ASSUME" or entry.get("nondet_function")) and len(block["instructions"]) != 1:
                    raise ValueError("ASSUME or nondet event crossed a singleton block boundary")
                if entry["kind"] == "ASSERT":
                    if position != len(block["instructions"]) - 1:
                        raise ValueError("ASSERT is not the final instruction of its scalar block")
                    merged_assertions += len(block["instructions"]) > 1
        if merged_assertions < case.get("minimum_merged_assertions", 0):
            raise ValueError("expected terminal ASSERT did not merge with preceding scalar instructions")
        outcomes.append({"runtime_blocks": len(blocks), "local_scalars": metadata["local_scalars"],
                         "merged_assertions": merged_assertions,
                         "assume_nondet_singletons": True, "assertions_terminal": True})
        if case.get("array_block_checks") and "--goto-btor2-array-blocks" in command:
            arrays = mapping.get("array_blocks", {})
            if not arrays.get("enabled") or not arrays.get("latest_storage_versions"):
                raise ValueError("array block metadata does not certify current storage versions")
            if merged_assertions < case.get("minimum_merged_array_assertions", 0):
                raise ValueError("expected array ASSERT did not merge with preceding array instructions")
            outcomes.append({"array_blocks": True, "latest_storage_versions": True,
                             "merged_assertions": merged_assertions})
    return outcomes


def simulate(case, args, directory, model, mapping):
    """Append observation aliases without changing original model roots.

    The fixture calls occur once, in lexical order, before any loop/branch.
    Distinct nondet_N inputs must survive. Other inputs use zero seeds unless a
    fixture requests explicit frame-varying seeds to test stable unwritten data.
    No reachability search or solver-generated witness is involved.
    """
    nodes = nodes_from(model)
    inputs = [(nid, node) for nid, node in nodes.items() if node[0] == "input"]
    nondet = [(nid, node) for nid, node in inputs
              if len(node) >= 3 and re.fullmatch(r"nondet_\d+", node[2])]
    if len(nondet) != len(case["inputs"]):
        raise ValueError(f"expected {len(case['inputs'])} distinct nondet inputs, got {len(nondet)}")
    if case.get("required_nondet_calls") is not None:
        events = [entry for entry in mapping["instructions"] if entry.get("nondet_function")]
        if len(events) != case["required_nondet_calls"]:
            raise ValueError("required nondet source call observations were removed")
        if any(not entry.get("executed_output") or not entry.get("value_output") or
               nodes.get(int(entry.get("result_state_node", 0)), [None])[0] != "state" for entry in events):
            raise ValueError("required nondet call/result metadata no longer names emitted observations/states")
    fixed = {nid: value for (nid, _), value in zip(nondet, case["inputs"])}
    trace = ["#0"]
    for frame in range(args.frames + 1):
        assignments = []
        for ordinal, (nid, node) in enumerate(inputs):
            sort = nodes[int(node[1])]
            seed = 17 * frame + ordinal + 1 if case.get("vary_declaration_inputs") else 0
            if sort[1] == "bitvec":
                width = int(sort[2])
                assignments.append(f"{ordinal} {fixed.get(nid, seed) % (1 << width):0{width}b}")
            elif sort[1] == "array":
                width = int(nodes[int(sort[3])][2])
                assignments.append(f"{ordinal} [*] {seed % (1 << width):0{width}b}")
            else:
                raise ValueError("unhandled input sort")
        trace += [f"@{frame}", *assignments]
    trace += [".", ""]
    (directory / "fixed-input.trace").write_text("\n".join(trace))
    target = case.get("target", "optimization-reached")
    properties = []
    for entry in mapping["source_properties"]:
        condition = int(entry.get("condition_node", 0))
        if not condition:
            continue
        line = int(entry["source"]["line"])
        source_line = Path(case["source"]).read_text().splitlines()[line - 1]
        properties.append({"node": condition, "property_id": entry["property_id"],
                           "line": line, "column": entry["source"].get("column", ""),
                           "target": target in source_line,
                           "unexecuted": any(marker in source_line for marker in case.get("unexecuted_assertions", []))})
    if sum(entry["target"] for entry in properties) != 1:
        raise ValueError("expected one retained target assertion")
    if sum(entry["unexecuted"] for entry in properties) != len(case.get("unexecuted_assertions", [])):
        raise ValueError("expected skipped source assertion is absent or ambiguous")
    constraints = [int(node[1]) for node in nodes.values() if node[0] == "constraint"]
    bool_sort = next(nid for nid, node in nodes.items() if node == ["sort", "bitvec", "1"])
    new_id = max(nodes) + 1
    appended = [f"{new_id} one {bool_sort}"]
    one = new_id
    for kind, entries in (("property", properties), ("constraint", [{"node": n} for n in constraints])):
        for ordinal, entry in enumerate(entries):
            new_id += 1
            entry["signal"] = f"__optimization_{kind}_{ordinal}"
            appended.append(f"{new_id} and {bool_sort} {entry['node']} {one} {entry['signal']}")
            if entry.get("unexecuted"):
                matches = [instruction for instruction in mapping["instructions"]
                           if instruction.get("property_id") == entry["property_id"] and instruction["kind"] == "ASSERT"]
                if len(matches) != 1 or int(matches[0]["source"]["line"]) != entry["line"]:
                    raise ValueError("skipped assertion instruction/source metadata is ambiguous")
                output = int(matches[0]["executed_output"])
                executed = nodes[output][1]
                entry["executed_signal"] = entry["signal"] + "_executed"
                new_id += 1
                appended.append(f"{new_id} and {bool_sort} {executed} {one} {entry['executed_signal']}")
    observations = []
    for request in case.get("compare_observations", []):
        matches = [entry for entry in mapping["instructions"]
                   if re.search(request["assign_symbol_regex"], entry.get("assign_symbol", ""))]
        if len(matches) != 1:
            raise ValueError(f"expected one assignment observation for {request['name']}, got {len(matches)}")
        entry = matches[0]
        value = int(entry["value_node"])
        sort = int(nodes[value][1])
        if nodes[sort][1] != "bitvec":
            raise ValueError("paired assignment observations require a bitvector value")
        executed = nodes[int(entry["executed_output"])][1]
        signal = f"__optimization_value_{len(observations)}"
        new_id += 1
        appended.append(f"{new_id} or {sort} {value} {value} {signal}")
        new_id += 1
        appended.append(f"{new_id} and {bool_sort} {executed} {one} {signal}_executed")
        observations.append({"name": request["name"], "signal": signal,
                             "width": int(nodes[sort][2]), "value_node": value,
                             "assign_symbol": entry["assign_symbol"],
                             **({"expected_unsigned_value": request["expected_unsigned_value"]}
                                if "expected_unsigned_value" in request else {})})
    # BtorSim versions whose VCD loop uses id < max_id omit the last node.
    # A final unnamed constant keeps every requested observation below max_id.
    new_id += 1
    appended.append(f"{new_id} zero {bool_sort}")
    observed = directory / "simulation.btor2"
    observed.write_text(model.read_text() + "\n; Regression-only observation aliases\n" +
                        "\n".join(appended) + "\n")
    save(directory / "simulation-observations.json", {"properties": properties, "values": observations})
    parsed = run([args.catbtor, observed], directory, "simulation-parser",
                 args.parser_timeout, args.memory_gib, discard_stdout=True)
    if parsed["status"] != "finished" or parsed["returncode"]:
        raise ValueError("simulator observation model failed parser/type check")
    outcome = run([args.btorsim, "-v", "--states", "--vcd", directory / "trace.vcd",
                   observed, directory / "fixed-input.trace"], directory, "simulation",
                  args.simulation_timeout, args.memory_gib)
    if outcome["status"] != "finished" or outcome["returncode"]:
        return {"status": "simulation_" + outcome["status"] if outcome["status"] != "finished"
                else "simulation_error", "simulation": outcome}
    frames = vcd_frames(directory / "trace.vcd")
    constraint_signals = [f"__optimization_constraint_{i}" for i in range(len(constraints))]
    required_signals = constraint_signals + [entry["signal"] for entry in properties] + \
        [entry["executed_signal"] for entry in properties if entry["unexecuted"]]
    unexpected_executions = {}
    failures, first_invalid = {}, None
    for frame, values in sorted(frames.items()):
        if any(values.get(name) not in {"0", "1"} for name in required_signals):
            raise ValueError(f"missing or nonconcrete property/constraint observation at frame {frame}")
        if any(values[name] == "0" for name in constraint_signals):
            first_invalid = frame
            break
        for entry in properties:
            if entry["unexecuted"] and values[entry["executed_signal"]] == "1":
                unexpected_executions.setdefault(entry["property_id"], frame)
            if values[entry["signal"]] == "1":
                failures.setdefault(entry["property_id"], frame)
    target_entry = next(entry for entry in properties if entry["target"])
    expected = {target_entry["property_id"]}
    passed = set(failures) == expected and not unexpected_executions
    if case.get("constraint_after_target"):
        passed &= first_invalid is not None and failures.get(target_entry["property_id"], args.frames + 1) < first_invalid
    else:
        passed &= first_invalid is None
    observed_values = {}
    target_frame = failures.get(target_entry["property_id"])
    for entry in observations:
        values = []
        for frame, snapshot in sorted(frames.items()):
            if target_frame is None or frame > target_frame:
                break
            if snapshot.get(entry["signal"] + "_executed") != "1":
                continue
            bits = snapshot.get(entry["signal"], "")
            if len(bits) != entry["width"] or set(bits) - {"0", "1"}:
                raise ValueError(f"nonconcrete paired value observation {entry['name']} at frame {frame}")
            values.append({"frame": frame, "bits": bits, "unsigned_value": int(bits, 2)})
        if len(values) != 1:
            raise ValueError(f"expected one executed value observation {entry['name']}, got {len(values)}")
        if "expected_unsigned_value" in entry and values[0]["unsigned_value"] != entry["expected_unsigned_value"]:
            raise ValueError(f"fixed value observation differs for {entry['name']}")
        observed_values[entry["name"]] = values
    return {"status": "pass" if passed else "regression_mismatch",
            "simulation": outcome, "frames_requested": args.frames + 1,
            "frames_observed": len(frames), "target_property": target_entry["property_id"],
            "target_frame": failures.get(target_entry["property_id"]),
            "observed_property_failures": failures,
            "unexpected_assertion_executions": unexpected_executions,
            "first_constraint_violation": first_invalid, "nondet_inputs": len(nondet),
            "input_seed_policy": "frame-varying non-nondet seeds" if case.get("vary_declaration_inputs") else "zero non-nondet seeds",
            "observation_aliases_added": len(appended),
            "observed_values": observed_values,
            "scope": "fixed-input finite prefix; no model checking"}


def regression_cases(args):
    manifest = json.loads(args.regression_manifest.read_text())
    cases = []
    for item in manifest["cases"]:
        if args.case_filter and not any(re.search(pattern, item["name"]) for pattern in args.case_filter):
            continue
        source = (args.regression_manifest.parent / item["source"]).resolve()
        if item.get("export_spec"):
            item = {**item, "export_spec": str((args.regression_manifest.parent / item["export_spec"]).resolve())}
        for architecture in args.architectures.split(","):
            if architecture not in item.get("architectures", ["32", "64"]):
                continue
            cases.append({**item, "source": str(source), "architecture": "ILP32" if architecture == "32" else "LP64",
                          "case": item["name"], "kind": "regression"})
    return cases


def read_csv(path):
    with path.open(encoding="utf-8-sig", newline="") as stream:
        return list(csv.DictReader(stream))


def benchmark_cases(args):
    try:
        import yaml
    except ImportError as error:
        raise ValueError("metrics mode requires PyYAML (scripts/requirements-witness.txt)") from error
    rows = read_csv(args.dataset / "lab1_manifest.csv")
    manifest = {row["file_path"]: row for row in rows}
    if len(manifest) != len(rows):
        raise ValueError("duplicate benchmark manifest file_path")
    selected = set(manifest)
    if args.records:
        records = read_csv(args.records)
        if any(not row.get("file_path") for row in records):
            raise ValueError("records CSV requires a nonempty file_path column")
        selected = {row["file_path"] for row in records}
    if args.cases_file:
        wanted = {line.strip() for line in args.cases_file.read_text().splitlines()
                  if line.strip() and not line.lstrip().startswith("#")}
        by_yml = {row["yml_path"]: row["file_path"] for row in rows}
        wanted = {by_yml.get(name, name) for name in wanted}
        if wanted - set(manifest):
            raise ValueError("cases file contains tasks absent from benchmark manifest: " + ", ".join(sorted(wanted - set(manifest))))
        selected &= wanted
    if selected - set(manifest):
        raise ValueError("records contain tasks absent from benchmark manifest: " + ", ".join(sorted(selected - set(manifest))))
    requested = set(selected)
    selected = [name for name in sorted(selected)
                if not args.case_filter or any(re.search(pattern, name) for pattern in args.case_filter)]
    if args.limit:
        selected = selected[:args.limit]
    cases = []
    for name in selected:
        row = manifest[name]
        task_path = (args.dataset / row["yml_path"]).resolve()
        task = yaml.safe_load(task_path.read_text())
        architecture = task.get("options", {}).get("data_model")
        if architecture not in {"ILP32", "LP64"} or architecture != row["architecture"]:
            raise ValueError("task architecture mismatch: " + name)
        properties = [entry for entry in task.get("properties", [])
                      if Path(entry["property_file"]).name == "unreach-call.prp"]
        if len(properties) != 1:
            raise ValueError("expected exactly one unreach-call property: " + name)
        source = (args.dataset / name).resolve()
        task_inputs = task["input_files"]
        task_inputs = [task_inputs] if isinstance(task_inputs, str) else task_inputs
        if len(task_inputs) != 1 or (task_path.parent / task_inputs[0]).resolve() != source:
            raise ValueError("task input mismatch: " + name)
        cases.append({"case": name, "kind": "metrics", "source": str(source),
                      "architecture": architecture, "task_yml": str(task_path),
                      "task_yml_sha256": digest(task_path),
                      "property": "unreach-call.prp", "expected_verdict": properties[0].get("expected_verdict")})
    save(args.output_dir / "benchmark-selection.json", {
        "dataset_manifest_tasks": len(manifest), "requested_tasks": len(requested),
        "selected_tasks": len(cases), "requested_file_paths": sorted(requested),
        "selected_file_paths": selected,
        "additional_manifest_tasks": sorted(set(manifest) - requested),
        "records": str(args.records) if args.records else None,
        "records_sha256": digest(args.records) if args.records else None})
    return cases


def execute(case, config, variant, executable, extra_args, args):
    directory = args.output_dir / case["kind"] / case["case"] / case["architecture"] / config / variant
    directory.mkdir(parents=True)
    result = {**case, "config": config, "dataset_config": {"bv": "ob", "array": "oa", "mixed": "mixed"}[config],
              "variant": variant, "directory": str(directory), "model_checking_run": False,
              "source_sha256": digest(Path(case["source"]))}
    model = directory / "model.btor2"
    mapping_path = directory / "model.map.json"
    command = [executable, case["source"], "--goto-btor2", "--inline",
               "--32" if case["architecture"] == "ILP32" else "--64",
               "--memory", "object", "--array", CONFIGS[config],
               "--goto-btor2-out", model, *args.common_arg, *extra_args]
    if case["kind"] == "metrics" and case["case"].startswith("loop-industry-pattern/aiob_4") and args.aiob_headers:
        # These preprocessed glibc tasks need their established Linux header
        # shim even when conversion runs on macOS. Source bytes stay intact.
        command += ["--arch", "i386", "--os", "linux", "-I", args.aiob_headers]
        result["frontend_adaptation"] = "Linux/i386 declarations with aiob compatibility headers"
    if case["kind"] == "regression":
        command += ["--goto-btor2-no-slice-property", "--goto-btor2-map-out", mapping_path]
    if case.get("witness_roundtrip"):
        raise ValueError("legacy witness_roundtrip cases are retired; run "
                         "python3 -m unittest test.c2btor_optimizations.test_witness_v2")
    try:
        expected_rejection = conversion_rejection(case, config, command)
        conversion = run(command, directory, "conversion", args.conversion_timeout, args.memory_gib,
                         file_limit_mib=args.max_model_mib)
        result["conversion"] = conversion
        if conversion["status"] != "finished":
            result["status"] = "conversion_" + conversion["status"]
        elif conversion["returncode"]:
            conversion_log = (directory / "conversion.stdout").read_text() + (directory / "conversion.stderr").read_text()
            expected_error = expected_rejection and not model.exists() and expected_rejection["message"] in conversion_log
            result["status"] = "expected_conversion_error" if expected_error else "conversion_error"
            result["regression_passed"] = result["status"] == "expected_conversion_error"
            result["model_passed"] = False
        elif not model.is_file() or not model.stat().st_size:
            result["status"] = "conversion_empty_output"
        else:
            if expected_rejection:
                raise ValueError("expected conversion rejection for this flag/configuration combination")
            mapping = json.loads(mapping_path.read_text()) if case["kind"] == "regression" else None
            conversion_log = (directory / "conversion.stdout").read_text() + (directory / "conversion.stderr").read_text()
            result.update(structural_metrics(model, conversion_log, mapping))
            if mapping is not None and case.get("array_storage_checks"):
                result["array_storage_observations"] = check_array_storage(case, config, command, model, mapping)
                result["array_storage_checks_passed"] = True
            if mapping is not None and (case.get("state_checks") or case.get("scalar_block_checks")):
                result["scalar_structure_observations"] = check_scalar_structure(case, command, model, mapping)
                result["scalar_structure_checks_passed"] = True
            forbidden = case.get("forbidden_state_symbols", [])
            if any(word in " ".join(node[2:]) for node in nodes_from(model).values()
                   if node[0] == "state" for word in forbidden):
                raise ValueError("an expected pruned source object still has a state declaration")
            result["metrics_include_witness_observations"] = mapping is not None
            parsed = run([args.catbtor, model], directory, "parser", args.parser_timeout,
                         args.memory_gib, discard_stdout=True)
            result["parser"] = parsed
            if parsed["status"] != "finished":
                result["status"] = "parser_" + parsed["status"]
            elif parsed["returncode"]:
                result["status"] = "parser_error"
            elif case["kind"] == "regression":
                result.update(simulate(case, args, directory, model, mapping))
            else:
                result["status"] = "pass"
            result["model_passed"] = parsed["status"] == "finished" and parsed["returncode"] == 0
            if case["kind"] == "regression":
                result["regression_passed"] = result["status"] == "pass"
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        result.update(status="harness_error", error=str(error))
    save(directory / "result.json", result)
    return result


def summarize(results, args):
    totals = {}
    for kind in ("regression", "metrics"):
        for config in args.configs:
            for variant in ("before", "after"):
                group = [item for item in results if item["kind"] == kind and item["config"] == config and item["variant"] == variant]
                if not group:
                    continue
                model_passed = [item for item in group if item["status"] == "pass"]
                passed = [item for item in group if item["status"] in {"pass", "expected_conversion_error"}]
                totals[f"{kind}/{config}/{variant}"] = {
                    "cases": len(group), "passed": len(passed), "model_passed": len(model_passed),
                    "status_counts": dict(Counter(item["status"] for item in group)),
                    "successful_metric_totals": {key: sum(item[key] for item in model_passed if item.get(key) is not None)
                                                  for key in METRIC_KEYS}}
    pairs = defaultdict(dict)
    for item in results:
        pairs[(item["kind"], item["case"], item["architecture"], item["config"])][item["variant"]] = item
    comparisons = []
    for (kind, name, architecture, config), pair in sorted(pairs.items()):
        before, after = pair["before"], pair["after"]
        comparable = before["status"] == after["status"] == "pass"
        item = {"kind": kind, "case": name, "architecture": architecture, "config": config,
                "before_status": before["status"], "after_status": after["status"],
                "comparable": comparable}
        if comparable:
            item["delta"] = {key: after[key] - before[key] for key in METRIC_KEYS
                             if before.get(key) is not None and after.get(key) is not None}
            item["reduction_percent"] = {key: round(100 * (before[key] - after[key]) / before[key], 4)
                                         for key in METRIC_KEYS if before.get(key) and after.get(key) is not None}
            if before.get("compare_observations"):
                values = lambda result: {name: [event["bits"] for event in events]
                                         for name, events in result["observed_values"].items()}
                item["paired_values_equal"] = values(before) == values(after)
                item["paired_values_before"] = before["observed_values"]
                item["paired_values_after"] = after["observed_values"]
        comparisons.append(item)
    summary = {"model_checking_run": False,
               "scope": "conversion/parser and fixed-input finite regressions; no safety proof",
               "run_count": len(results), "totals": totals, "comparisons": comparisons,
               "results": results}
    summary["paired_observations_passed"] = all(item.get("paired_values_equal", True) for item in comparisons)
    save(args.output_dir / "summary.json", summary)
    flat = [{key: value for key, value in item.items() if not isinstance(value, (dict, list))} for item in results]
    columns = list(dict.fromkeys(key for item in flat for key in item))
    with (args.output_dir / "summary.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=columns)
        writer.writeheader()
        writer.writerows(flat)
    save(args.output_dir / "comparisons.json", comparisons)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, required=True, help="baseline converter snapshot")
    parser.add_argument("--after", type=Path, help="candidate converter; defaults to --before")
    for name in ("before-arg", "after-arg", "common-arg"):
        parser.add_argument("--" + name, action="append", default=[],
                            help="repeat per token; use --" + name + "=--option for flags")
    parser.add_argument("--catbtor", type=Path, required=True)
    parser.add_argument("--btorsim", type=Path, help="required for regressions/both; finite simulation only")
    parser.add_argument("--output-dir", type=Path, required=True, help="new run directory")
    parser.add_argument("--mode", choices=("regressions", "metrics", "both"), default="regressions")
    parser.add_argument("--configs", default="bv,array,mixed", help="comma-separated BV/Array/mixed; ob/oa accepted as dataset aliases")
    parser.add_argument("--architectures", default="32,64", help="regression targets; benchmarks read architecture from YAML")
    parser.add_argument("--regression-manifest", type=Path, default=FIXTURES / "cases.json")
    parser.add_argument("--dataset", type=Path, default=ROOT / "test/lab1-data")
    parser.add_argument("--records", type=Path, help="CSV file_path column selects the exact benchmark set (deduplicated)")
    parser.add_argument("--aiob-headers", type=Path, help="Linux-compatible headers for loop-industry-pattern/aiob_4* tasks")
    parser.add_argument("--cases-file", type=Path, help="relative source/YAML names, one per line; intersects records selection")
    parser.add_argument("--case-filter", action="append", default=[], help="regular expression; repeat for OR matching")
    parser.add_argument("--limit", type=int, help="maximum selected benchmark tasks")
    parser.add_argument("--frames", type=int, default=256, help="finite simulator transition count")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--conversion-timeout", type=float, default=60)
    parser.add_argument("--parser-timeout", type=float, default=30)
    parser.add_argument("--simulation-timeout", type=float, default=30)
    parser.add_argument("--memory-gib", type=float, default=4, help="sampled per-process-tree RSS limit; 0 disables")
    parser.add_argument("--max-model-mib", type=float, default=128, help="conversion output-file size limit; 0 disables")
    args = parser.parse_args()
    args.after = args.after or args.before
    for name in ("before", "after", "catbtor", "btorsim", "output_dir", "regression_manifest", "dataset", "records", "cases_file", "aiob_headers"):
        value = getattr(args, name)
        if value is not None:
            setattr(args, name, value.resolve())
    for name in ("before", "after", "catbtor"):
        path = getattr(args, name)
        if not path.is_file() or not os.access(path, os.X_OK):
            parser.error("missing executable: " + str(path))
    if args.mode != "metrics" and (args.btorsim is None or not args.btorsim.is_file() or not os.access(args.btorsim, os.X_OK)):
        parser.error("regressions require an executable --btorsim")
    if args.output_dir.exists():
        parser.error("--output-dir must not already exist")
    if args.workers < 1 or args.frames < 1 or min(args.memory_gib, args.max_model_mib) < 0 or (args.limit is not None and args.limit < 1):
        parser.error("workers, frames and limit must be positive; memory-gib and max-model-mib must be nonnegative")
    if args.aiob_headers and not args.aiob_headers.is_dir():
        parser.error("missing --aiob-headers directory")
    if min(args.conversion_timeout, args.parser_timeout, args.simulation_timeout) <= 0:
        parser.error("timeouts must be positive")
    if any(architecture not in {"32", "64"} for architecture in args.architectures.split(",")):
        parser.error("--architectures must contain 32 and/or 64")
    args.configs = list(dict.fromkeys(CONFIG_ALIASES.get(config, config) for config in args.configs.split(",")))
    if not args.configs or any(config not in CONFIGS for config in args.configs):
        parser.error("--configs must contain bv, array, mixed, ob or oa")
    for pattern in args.case_filter:
        re.compile(pattern)
    if args.memory_gib:
        try:
            tree_rss(os.getpid())
        except (OSError, subprocess.SubprocessError) as error:
            parser.error("process RSS sampling is unavailable; run with process-table access or explicitly use --memory-gib 0: " + str(error))
    args.output_dir.mkdir(parents=True)
    save(args.output_dir / "run.json", {"arguments": {key: str(value) if isinstance(value, Path) else value
                                                      for key, value in vars(args).items()},
                                       "model_checking_run": False,
                                       "python": {"executable": sys.executable, "version": sys.version},
                                       "harness_sha256": digest(Path(__file__)),
                                       "tools": {name: {"path": str(getattr(args, name)), "sha256": digest(getattr(args, name))}
                                                 for name in ("before", "after", "catbtor", "btorsim") if getattr(args, name)}})
    cases = []
    if args.mode != "metrics":
        cases += regression_cases(args)
    if args.mode != "regressions":
        cases += benchmark_cases(args)
    if not cases:
        parser.error("selection is empty")
    jobs = [(case, config, variant, executable, extra)
            for case in cases for config in args.configs
            if config in case.get("configs", CONFIGS)
            for variant, executable, extra in (("before", args.before, args.before_arg),
                                               ("after", args.after, args.after_arg))]
    results = []
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(execute, *job, args) for job in jobs]
        for future in as_completed(futures):
            item = future.result()
            results.append(item)
            print(f"{len(results)}/{len(jobs)} {item['kind']} {item['case']} {item['architecture']} {item['config']} {item['variant']}: {item['status']}", flush=True)
            if len(results) % 25 == 0:
                save(args.output_dir / "results.json", results)
    results.sort(key=lambda item: (item["kind"], item["case"], item["architecture"], item["config"], item["variant"]))
    save(args.output_dir / "results.json", results)
    summary = summarize(results, args)
    run_metadata = json.loads((args.output_dir / "run.json").read_text())
    final_hashes = {name: digest(Path(tool["path"])) for name, tool in run_metadata["tools"].items()}
    unchanged = all(final_hashes[name] == tool["sha256"] for name, tool in run_metadata["tools"].items())
    summary["tool_hashes_unchanged"] = unchanged
    summary["completed_tool_hashes"] = final_hashes
    save(args.output_dir / "summary.json", summary)
    passed = sum(item["status"] in {"pass", "expected_conversion_error"} for item in results)
    print(f"{passed}/{summary['run_count']} conversions/regressions passed; {args.output_dir / 'summary.json'}")
    if not unchanged:
        print("Tool executable changed during the run; repeat using frozen snapshots.", file=sys.stderr)
    if not summary["paired_observations_passed"]:
        print("Paired assignment observations differ; inspect comparisons.json.", file=sys.stderr)
    return 0 if passed == len(results) and unchanged and summary["paired_observations_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
