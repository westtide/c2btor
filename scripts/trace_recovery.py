# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors

"""Replay one standard BTOR2 counterexample and recover YAML 2.1 source calls."""
import datetime
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import uuid

from .cex_parser import ArrayValue, Trace, open_cex
from .source_map import digest, load_map
from .summary_recovery import SummaryRecovery
from .yaml21_writer import SequenceWriter, publish_file
from .yaml_io import dump as dump_witness, load_file as load_yaml_file, yaml_module


def executable(name):
    """Find installation tools; environment overrides are for installation only."""
    import shutil
    override = os.environ.get(name.upper())
    root = Path(__file__).resolve().parents[1]
    candidates = ([Path(override)] if override else
                  [root / "bin" / name, root / "build" / "bin" / name,
                   root / "checkers" / "carat" / "build" / name,
                   root / "checkers" / "carat" / "deps" / "btor2tools" / "build" / "bin" / name,
                   root / name])
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate.resolve())
    found = shutil.which(override or name)
    if found:
        return found
    raise ValueError(f"{name} executable missing; install bin/{name} or set {name.upper()}")


def complete_value(value, declaration):
    if declaration.sort.kind == "bitvec":
        return (isinstance(value, str) and len(value) == declaration.sort.width and
                not set(value) - {"0", "1"})
    return (isinstance(value, ArrayValue) and
            (value.default is not None or len(value.entries) == 1 << declaration.sort.index_width))


def read_complete_trace(path, model):
    """Reject omissions before BtorSim can fill anything with a default value."""
    with open_cex(path, model) as stream:
        trace = Trace(stream.bads, dict(stream))
    for time, frame in trace.frames.items():
        declarations = list(model.inputs)
        declarations += [d for d in model.states
                         if (time == 0 and d.node not in model.initialized) or
                            (time > 0 and d.node not in model.successors)]
        for declaration in declarations:
            section = "inputs" if declaration.kind == "input" else "states"
            if not complete_value(frame[section].get(declaration.node), declaration):
                raise ValueError(f"missing concrete {declaration.kind} node {declaration.node} at frame {time}; "
                                 "backend export must supply it")
    return trace


def replay(model, cex, scratch):
    vcd = scratch / "replay.vcd"
    result = subprocess.run([executable("btorsim"), "--states", "--vcd", str(vcd),
                             str(model.path), str(cex)], capture_output=True, text=True)
    if result.returncode:
        raise ValueError("original-model replay failed: " + (result.stderr or result.stdout)[-4000:])
    # BtorSim checks both the claimed bad and all model constraints. It exits
    # nonzero on a violated constraint or an untriggered claimed bad.
    if not vcd.is_file():
        raise ValueError("BtorSim produced no replay observations")
    return read_observation_vcd(vcd)


def node_bits(node, signals, model, description):
    fields = model.nodes.get(node)
    if not fields:
        raise ValueError(f"missing {description} node {node}")
    if fields[0] == "output":
        node = int(fields[1])
        fields = model.nodes[node]
    sort = model.sorts.get(int(fields[1])) if len(fields) > 1 else None
    if sort is None or sort.kind != "bitvec":
        raise ValueError(f"non-scalar {description}")
    # BtorSim VCD keys are original BTOR symbols, emitted by the converter.
    bits = signals.get(fields[-1])
    if bits is None or len(bits) != sort.width or set(bits) - {"0", "1"}:
        raise ValueError(f"missing concrete replay observation for {description} (node {node})")
    return bits


def check_counter(event, time, observations, model, executed):
    if event.get("counter_width") != 8 or not event.get("counter_node"):
        raise ValueError("ordinary nondet event lacks a post-counter-1 counter")
    counter = event["counter_node"]
    current = int(node_bits(counter, observations[time], model, "nondet counter"), 2)
    if time == 0 and current != 0:
        raise ValueError("nondet counter is not initialized to zero")
    if time + 1 in observations:
        following = int(node_bits(counter, observations[time + 1], model, "next nondet counter"), 2)
        if (following - current) % 256 != int(executed):
            raise ValueError(f"counter/execution mismatch at frame {time}")
    # No successor exists at the last witness frame: its direct execution
    # predicate controls the call and its value is the input at this frame.


def recover(model_path, map_path, cex_path, output):
    """The only unsafe recovery API: artifacts in, requested YAML file out."""
    mapping, model = load_map(map_path, model_path)
    if mapping.get("witness_counter_format") != "post-counter-1":
        raise ValueError("map lacks post-counter-1 nondet instrumentation")
    backend = read_complete_trace(cex_path, model)
    locations = SourceLocations()
    target_function = error_function(mapping["specification"])
    summary = SummaryRecovery(mapping, model, backend, sys.maxsize)
    claimed = {model.bads[index] for index in backend.bads}
    metadata = {"format_version": "2.1", "uuid": str(uuid.uuid4()),
                "creation_time": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                "producer": {"name": "C2Btor", "version": mapping.get("producer_version", "development"),
                             "description": "Standard BTOR2 counterexample replay and source recovery"},
                "task": {"input_files": mapping["input_files"],
                         "input_file_hashes": {p: mapping["source_hashes"][p] for p in mapping["input_files"]},
                         "specification": mapping["specification"], "data_model": mapping["data_model"], "language": "C"}}
    output = Path(output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".c2btor-replay-", dir=output.parent) as temporary:
        scratch = Path(temporary)
        observations = replay(model, cex_path, scratch)
        # BtorSim terminates VCD at one empty timestamp after its last frame.
        end = len(backend.frames)
        if observations.get(end) == observations.get(end - 1):
            observations.pop(end, None)
        if set(observations) != set(backend.frames):
            raise ValueError("simulator and counterexample frame counts differ")
        candidate = scratch / "witness.yml"
        with candidate.open("w") as outgoing:
            writer = SequenceWriter(outgoing, metadata)
            reached = False
            for time in backend.frames:
                signals = observations[time]
                pc = int(node_bits(mapping["pc_node"], signals, model, "PC"), 2)
                events = block_events(mapping, pc, signals, model.nodes)
                # Validate every retained call counter, including inactive calls.
                for event in mapping["instructions"]:
                    if "nondet_function" in event:
                        executed = node_bits(event.get("executed_output", event["executed_node"]), signals, model, "call execution") == "1"
                        check_counter(event, time, observations, model, executed)
                target = first_violation(events, claimed, signals, model)
                for event, observed in events:
                    for sample in summary.iter_consume(event, time):
                        if sample["iteration_first"]:
                            writer.append({"type": "branching", "action": "follow",
                                           "location": locations.loop(sample["loop_condition_entry"]),
                                           "constraint": {"value": "true"}})
                        writer.append(_return_point(sample, sample["value_bits"], locations))
                        if sample["group_last"]:
                            writer.append({"type": "branching", "action": "follow",
                                           "location": locations.loop(sample["loop_condition_entry"]),
                                           "constraint": {"value": "false"}})
                    if "nondet_function" in event and not event["source"]["file_name"].startswith("<"):
                        if event.get("nondet_return_unsupported"):
                            raise ValueError("unsupported source return: " + str(event["nondet_return_unsupported"]))
                        require_source_input_assignments(event, time, backend.frames, model.nodes)
                        bits = node_bits(event.get("value_output", event["value_node"]), signals, model, "call-time nondet value")
                        if len(bits) != event["result_width"]:
                            raise ValueError("nondet result width mismatch")
                        writer.append(_return_point(event, bits, locations))
                    if event is target:
                        if event.get("property_class") != "unreach-call":
                            raise ValueError("violated property is not unreach-call")
                        writer.append({"type": "target", "action": "follow",
                                       "location": locations.call(event, event.get("error_function", target_function), False)})
                        reached = True
                        break
                if reached:
                    break
            summary.finish()
            writer.finish()
        return publish_file(output, candidate)


def _return_point(event, bits, locations):
    return {"type": "function_return", "action": "follow",
            "location": locations.call(event, event["nondet_function"], True),
            "constraint": {"format": "ext_c_expression", "value": return_constraint(bits, event["result_type"])}}


def first_violation(events, claimed, signals, model):
    for event, _ in events:
        if event.get("bad_node") not in claimed:
            continue
        output = event.get("bad_condition_output")
        if not output:
            raise ValueError("source assertion lacks its call-time bad predicate")
        if observation_bits(output, signals, model.nodes, "source bad predicate") == "1":
            return event
    return None


def error_function(specification):
    match = re.fullmatch(r"CHECK\s*\(\s*init\s*\(main\(\)\)\s*,\s*LTL\s*\(G\s*!\s*call\((\w+)\(\)\)\s*\)\s*\)", specification)
    if match is None:
        raise ValueError("witness translation supports unreach-call properties only")
    return match[1]

def load_witness(path):
    return load_yaml_file(path)

def return_constraint(value_bits, result_type):
    if not value_bits or set(value_bits) - {"0", "1"}:
        raise ValueError("nondet return value must be a concrete bit vector")
    if result_type == "floatbv":
        # An integer significand and a binary exponent give an exact C hex
        # literal, including subnormals. Never round through decimal or a
        # host floating-point conversion. For special values, use a necessary
        # C predicate: both zero signs share zero bounds, NaNs share their
        # unordered self-comparison, and infinities exceed the largest finite
        # value. The exact original bits remain in the BTOR2 counterexample; the source
        # predicate deliberately does not constrain NaN payloads or zero sign.
        layouts = {32: (8, 23, 127, "f"), 64: (11, 52, 1023, "")}
        if len(value_bits) not in layouts:
            raise ValueError("unsupported nondet floating-point width")
        exponent_bits, fraction_bits, bias, suffix = layouts[len(value_bits)]
        exponent = int(value_bits[1:1 + exponent_bits], 2)
        fraction = int(value_bits[1 + exponent_bits:], 2)
        if exponent == (1 << exponent_bits) - 1:
            if fraction:
                return "\\result != \\result"
            maximum = {32: "0x1.fffffep+127f", 64: "0x1.fffffffffffffp+1023"}[len(value_bits)]
            return (f"\\result < -{maximum}" if value_bits[0] == "1" else
                    f"\\result > {maximum}")
        if exponent == 0 and fraction == 0:
            # Keep the two IEEE zero signs available. Some validators turn
            # equality to a zero literal into an explicit +0 assignment;
            # equivalent ordered bounds preserve -0 through that transfer.
            return f"\\result <= 0.0{suffix} && \\result >= 0.0{suffix}"
        significand = fraction if exponent == 0 else (1 << fraction_bits) | fraction
        power = (exponent or 1) - bias - fraction_bits
        sign = "-" if value_bits[0] == "1" else ""
        return f"\\result == {sign}0x{significand:x}p{power:+d}{suffix}"
    if result_type not in {"signedbv", "unsignedbv", "c_bool", "bool"}:
        raise ValueError(f"unsupported nondet return type: {result_type}")
    value = int(value_bits, 2)
    width = len(value_bits)
    if result_type in {"c_bool", "bool"} and value not in {0, 1}:
        raise ValueError("nondet boolean return is not zero or one")
    if result_type == "signedbv" and value_bits[0] == "1":
        value -= 1 << width
    if width > 64:
        raise ValueError("nondet result exceeds supported C integer literal width")
    if result_type == "unsignedbv" and width > 32:
        literal = str(value) + "ULL"
    elif result_type == "signedbv" and width > 32:
        # The minimum signed 64-bit value is not a positive decimal C literal.
        literal = "(-9223372036854775807LL - 1LL)" if value == -(1 << 63) else str(value) + "LL"
    else:
        literal = str(value)
    return f"\\result == {literal}"


def _masked_source(path):
    token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\''
    return re.sub(token, lambda m: re.sub(r"[^\n]", " ", m[0]), path.read_text())


def _location_key(value):
    if isinstance(value, dict):
        return (dict, tuple((key, _location_key(item)) for key, item in sorted(value.items())))
    if isinstance(value, list):
        return (list, tuple(_location_key(item) for item in value))
    return (type(value), value)


class SourceLocations:
    """One recovery task's source text and certified static call locations.

    Cache positions, never dynamic calls or return values. Include the source
    event identity and every argument used by the uncached resolver, so two
    same-line calls cannot select each other's certificate or destination.
    """
    def __init__(self):
        self._sources, self._paths, self._calls, self._loops = {}, {}, {}, {}

    def clean(self, path):
        if path not in self._sources:
            self._sources[path] = _masked_source(path)
        return self._sources[path]

    def resolve(self, path):
        if path not in self._paths:
            self._paths[path] = path.resolve()
        return self._paths[path]

    def call(self, event, function, is_return):
        source = event["source"]
        certificate = event.get("call_return_location")
        unavailable = event.get("call_return_location_unavailable")
        destination = event.get("result_destination") if is_return else None
        key = (_location_key(source), _location_key(event.get("instruction_id")),
               _location_key(event.get("original_event_ids", [])), function, is_return,
               _location_key(destination), _location_key(certificate), _location_key(unavailable))
        if key not in self._calls:
            self._calls[key] = call_location(source, function, is_return, destination,
                                             certificate, unavailable, _locations=self)
        return self._calls[key]

    def loop(self, source):
        key = _location_key(source)
        if key not in self._loops:
            self._loops[key] = loop_location(source, _locations=self)
        return self._loops[key]


def call_location(source, function, is_return, destination=None, call_return_location=None,
                  call_return_location_unavailable=None, *, _locations=None):
    """Resolve an unambiguous direct, nullary C call; reject macros/ambiguity.

    CBMC locations need not identify the ')' required by function_return.
    Mask comments/literals without changing offsets, then use the original
    file to recover the precise column. No fuzzy line/column guessing.
    """
    if call_return_location_unavailable is not None:
        raise ValueError("frontend could not certify the original C call position: " +
                         str(call_return_location_unavailable))
    path = Path(source["file_name"])
    clean = _locations.clean(path) if _locations is not None else _masked_source(path)
    resolve = _locations.resolve if _locations is not None else Path.resolve
    calls = list(re.finditer(r"\b" + re.escape(function) + r"\s*\(\s*\)", clean))
    if call_return_location is not None:
        # A frontend certificate is independent of a folded destination and
        # runtime call order. Recheck its physical ')' against this exact
        # hash-bound source; a malformed certificate must never select another
        # call through the legacy fallback below.
        site = call_return_location
        if (not isinstance(site, dict) or site.get("format") != "c2btor-c-call-site-1" or
                not isinstance(site.get("file_name"), str) or
                resolve(Path(site["file_name"])) != resolve(path) or
                not re.fullmatch(r"[0-9]+", str(site.get("line", ""))) or
                not re.fullmatch(r"[0-9]+", str(site.get("column", "")))):
            raise ValueError("invalid frontend call-return location certificate")
        line, column = int(site["line"]), int(site["column"])
        matches = [match for match in calls
                   if clean.count("\n", 0, match.end() - 1) + 1 == line and
                   match.end() - 1 - clean.rfind("\n", 0, match.end() - 1) == column]
        if len(matches) != 1:
            raise ValueError(f"frontend call-return certificate does not identify {function} at {path}:{line}:{column}")
        offset = matches[0].end() - 1 if is_return else matches[0].start()
        return {"file_name": str(path), "line": clean.count("\n", 0, offset) + 1,
                "column": offset - clean.rfind("\n", 0, offset)}
    line = int(source["line"])
    matches = []
    for match in calls:
        if clean.count("\n", 0, match.start()) + 1 == line:
            matches.append(match)
    if len(matches) > 1 and source.get("column"):
        # Use a frontend column only when it exactly names the function token.
        # A statement/LHS column is not evidence for choosing a nearby call.
        column = int(source["column"])
        at_column = [match for match in matches
                     if match.start() - clean.rfind("\n", 0, match.start()) == column]
        if len(at_column) == 1:
            matches = at_column
    if len(matches) > 1 and destination:
        # GotoIR proves that this call's result flows directly into this
        # designator. Semantic equality alone does NOT identify its spelling:
        # a[0+0] and a[0] fold to the same GOTO lhs. Require every candidate on
        # this source line to have a simple, literal assignment designator;
        # otherwise an unmatched complex lhs could alias the matched one.
        # Exact frontend call columns above remain authoritative.
        simple = []
        for match in matches:
            start = max(clean.rfind(mark, 0, match.start()) for mark in ";{}") + 1
            # A top-level comma can separate simple declarators/assignments.
            # Commas inside calls or subscripts cannot establish call identity.
            parens = brackets = 0
            for offset, char in enumerate(clean[:match.start()]):
                if char == "(": parens += 1
                elif char == ")": parens -= 1
                elif char == "[": brackets += 1
                elif char == "]": brackets -= 1
                elif char == "," and parens == 0 and brackets == 0:
                    start = max(start, offset + 1)
            prefix = clean[start:match.start()].strip()
            # Declarations may precede the final bare identifier. No pointers,
            # operators, casts, member access, calls or condition prefixes.
            found = re.fullmatch(
                r"(?:[A-Za-z_]\w*\s+)*([A-Za-z_]\w*(?:\s*\[\s*(?:0|[1-9][0-9]*)\s*\])*)\s*=\s*",
                prefix)
            if found is None:
                raise ValueError(f"ambiguous source designators for {function} at {path}:{line}")
            simple.append((re.sub(r"\s+", "", found[1]), match))
        matches = [match for spelling, match in simple if spelling == destination]
    if len(matches) != 1:
        raise ValueError(f"cannot locate unique direct call {function} at {path}:{line}")
    offset = matches[0].end() - 1 if is_return else matches[0].start()
    return {"file_name": str(path), "line": clean.count("\n", 0, offset) + 1,
            "column": offset - clean.rfind("\n", 0, offset)}

def loop_location(source, *, _locations=None):
    """Resolve a certified loop's keyword on its exact frontend source line."""
    if not source or source.get("kind") not in {"for", "while"}:
        raise ValueError("summary expansion lacks a supported certified loop anchor")
    path = Path(source["file_name"])
    clean = _locations.clean(path) if _locations is not None else _masked_source(path)
    line = int(source["line"])
    lines = clean.splitlines()
    if not 1 <= line <= len(lines):
        raise ValueError("certified loop anchor is outside its source file")
    matches = list(re.finditer(r"\b" + source["kind"] + r"\b", lines[line - 1]))
    column = int(source.get("column") or 0)
    exact = [match for match in matches if match.start() + 1 == column]
    matches = exact or matches
    if len(matches) != 1:
        raise ValueError("cannot locate a unique certified loop keyword")
    location = {"file_name": str(path), "line": line, "column": matches[0].start() + 1}
    if source.get("function"):
        location["function"] = source["function"]
    return location

def read_observation_vcd(path):
    """Read named BV signals at BtorSim step times, carrying omitted changes."""
    identifiers, values, snapshots = {}, {}, {}
    timestamp = None

    def snapshot():
        if timestamp is not None and timestamp % 10 == 0:
            snapshots[timestamp // 10] = dict(values)

    for line in Path(path).read_text().splitlines():
        fields = line.split()
        if fields[:2] == ["$var", "wire"] and len(fields) == 6:
            identifiers[fields[3]] = (fields[4], int(fields[2]))
        elif line.startswith("#"):
            snapshot()
            timestamp = int(line[1:])
        elif line.startswith("b") and len(fields) == 2:
            if fields[1] in identifiers:
                name, width = identifiers[fields[1]]
                bits = fields[0][1:]
                values[name] = bits.rjust(width, bits[0] if bits[0] in "xz" else "0")
        elif line and line[0] in "01xz" and line[1:] in identifiers:
            name, width = identifiers[line[1:]]
            values[name] = line[0] * width
    snapshot()
    return snapshots

def observation_bits(output_node, signals, nodes, description):
    """Read an observed scalar expression, never a state in a later frame."""
    output = nodes.get(output_node)
    if not output or output[0] != "output":
        raise ValueError(f"malformed {description} observation")
    signal = nodes.get(int(output[1]))
    if not signal or len(signal) < 3:
        raise ValueError(f"missing {description} signal")
    sort = nodes.get(int(signal[1]))
    if not sort or sort[:2] != ["sort", "bitvec"]:
        raise ValueError(f"non-scalar {description} observation")
    bits = signals.get(signal[-1])
    if bits is None or len(bits) != int(sort[2]) or set(bits) - {"0", "1"}:
        raise ValueError(f"missing or unknown {description} observation")
    return bits

def block_events(mapping, pc, signals, nodes):
    """Reconstruct the observed CFG path, including fallthrough-to-join edges.

    Two successors can both execute in one block: the fallthrough executes
    before a later join. The induced forward CFG has a unique topological
    order whenever the active nodes form one actual execution path. Check
    that property and every consecutive edge rather than selecting the first
    active successor or using source-line order.
    """
    blocks = {block["pc"]: block for block in mapping["blocks"]}
    instructions = {entry["instruction_id"]: entry for entry in mapping["instructions"]}
    if pc not in blocks:
        raise ValueError(f"PC {pc} has no block mapping")
    block = blocks[pc]
    active, observations = set(), {}
    for loc in block["instructions"]:
        entry = instructions[loc]
        bits = observation_bits(entry["executed_output"], signals, nodes,
                                f"execution for instruction {loc}")
        if bits not in {"0", "1"}:
            raise ValueError(f"missing or unknown execution observation for instruction {loc}")
        if bits == "1":
            active.add(loc)
            if "value_output" in entry:
                sort = nodes[int(nodes[entry["value_node"]][1])]
                # Array-valued internal updates remain in BtorSim's log; VCD
                # only supplies scalar observations for source return events.
                if sort[:2] == ["sort", "bitvec"]:
                    observations[loc] = observation_bits(
                        entry["value_output"], signals, nodes,
                        f"value for instruction {loc}")
    if not active or block["entry_instruction"] not in active:
        raise ValueError("execution observations do not form a complete block path")
    positions = {loc: index for index, loc in enumerate(block["instructions"])}
    exits = set(block.get("exit_instructions", []))
    successors, indegree = {}, {loc: 0 for loc in active}
    for loc in active:
        edges = set()
        for successor in instructions[loc]["successors"]:
            if successor not in active:
                continue
            # Certified loop backedges leave this transition's acyclic block,
            # even when their destination is the block entry itself.
            if successor == loc or (positions[successor] < positions[loc] and successor in exits):
                continue
            edges.add(successor)
        successors[loc] = edges
        for successor in edges:
            indegree[successor] += 1
    ready = {loc for loc, count in indegree.items() if count == 0}
    ordered = []
    while ready:
        if len(ready) != 1:
            raise ValueError("ambiguous internal CFG path")
        loc = ready.pop()
        if ordered and loc not in successors[ordered[-1]]:
            raise ValueError("execution observations skip a CFG edge")
        ordered.append(loc)
        for successor in successors[loc]:
            indegree[successor] -= 1
            if indegree[successor] == 0:
                ready.add(successor)
    if len(ordered) != len(active) or ordered[0] != block["entry_instruction"]:
        raise ValueError("execution observations do not form a complete block path")
    events = [(instructions[loc], observations.get(loc)) for loc in ordered]
    return events

def expression_input_nodes(root, nodes):
    """Walk BTOR2 value operands, excluding sorts, literals and immediates."""
    leaves = {"zero", "one", "ones", "const", "constd", "consth", "state"}
    unary = {"not", "inc", "dec", "neg", "redand", "redor", "redxor", "slice", "uext", "sext"}
    binary = {"add", "sub", "mul", "sdiv", "udiv", "srem", "urem", "smod",
              "and", "or", "xor", "nand", "nor", "xnor", "eq", "neq", "slt", "ult",
              "slte", "ulte", "sgt", "ugt", "sgte", "ugte", "sll", "srl", "sra",
              "rol", "ror", "concat", "implies", "iff", "read", "saddo", "uaddo",
              "ssubo", "usubo", "smulo", "umulo", "sdivo"}
    inputs, seen, pending = set(), set(), [root]
    while pending:
        node = pending.pop()
        if node in seen:
            continue
        seen.add(node)
        fields = nodes.get(node)
        if not fields:
            raise ValueError(f"missing source nondet value dependency node {node}")
        operation = fields[0]
        if operation == "input":
            inputs.add(node)
            continue
        if operation in leaves:
            continue
        if operation in unary:
            arity = 1
        elif operation in binary:
            arity = 2
        elif operation in {"ite", "write"}:
            arity = 3
        else:
            raise ValueError(f"unsupported source nondet value dependency: {operation}")
        if len(fields) < 2 + arity:
            raise ValueError(f"malformed source nondet value dependency: {operation}")
        pending.extend(int(operand) for operand in fields[2:2 + arity])
    return inputs

def require_source_input_assignments(instruction, time, backend_frames, nodes):
    """Source returns must come from the backend, never simulator defaults.

    Sparse intermediate states and unrelated inputs are still permitted. For
    array dependencies, require an explicit default (a total concrete array);
    inferring a required cell from a partial array needs a stronger evaluator.
    """
    if not instruction.get("value_node"):
        raise ValueError("source nondet call lacks its call-time value node")
    dependencies = expression_input_nodes(instruction["value_node"], nodes)
    if not dependencies:
        raise ValueError("source nondet call has no original input dependency; refusing to guess a return value")
    assigned = backend_frames.get(time, {}).get("inputs", {})
    missing = dependencies - assigned.keys()
    if missing:
        raise ValueError(f"missing backend source nondet input at frame {time}: nodes {sorted(missing)}; "
                         "refusing simulator-completed C return values")
    for node in dependencies:
        sort = nodes[int(nodes[node][1])]
        if sort[:2] == ["sort", "array"] and getattr(assigned[node], "default", None) is None:
            raise ValueError("source nondet array dependency lacks an explicit default; "
                             "partial-cell recovery is unsupported")
    return sorted(dependencies)
