#!/usr/bin/env python3
"""C2Btor translation map -> simulated BTOR2 trace -> SV-COMP YAML 2.0.

Only Python's standard library is required. JSON output is also valid YAML 1.2.
The map is debug/translation metadata; counterexamples use the BTOR2 standard.
"""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import uuid


DEFAULT_SPEC = "CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )"
DEFAULT_FLAGS = ["--inline", "--no-standard-checks", "--no-pointer-check",
                 "--no-bounds-check", "--no-built-in-assertions"]


def error_function(specification):
    match = re.fullmatch(r"CHECK\s*\(\s*init\s*\(main\(\)\)\s*,\s*LTL\s*\(G\s*!\s*call\((\w+)\(\)\)\s*\)\s*\)", specification)
    if match is None:
        raise ValueError("witness translation supports unreach-call properties only")
    return match[1]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def run(command, directory, name, timeout):
    save_json(directory / (name + ".command.json"), command)
    with (directory / (name + ".stdout")).open("w") as stdout, \
            (directory / (name + ".stderr")).open("w") as stderr:
        process = subprocess.Popen(command, stdout=stdout, stderr=stderr,
                                   start_new_session=True)
        try:
            return process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            # CPAchecker's launcher may spawn Java; stop the whole invocation.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            raise


def fresh_directory(path):
    directory = Path(path).resolve()
    directory.mkdir(parents=True, exist_ok=False)
    return directory


def export(args):
    directory = fresh_directory(args.output_dir)
    program = Path(args.program).resolve()
    before = digest(program)
    specification = Path(args.spec).read_text().strip() if args.spec else DEFAULT_SPEC
    model = directory / "model.btor2"
    mapping_path = directory / "model.map.json"
    extra = args.cbmc_args
    if extra[:1] == ["--"]:
        extra = extra[1:]
    if any(flag.split("=")[0] in {"--goto-btor2-out", "--goto-btor2-map-out"}
           for flag in extra):
        raise ValueError("output paths are managed by export")
    command = [str(Path(args.cbmc).resolve()), str(program), *DEFAULT_FLAGS,
               *extra, "--goto-btor2", "--goto-btor2-out", str(model),
               "--goto-btor2-error-function", error_function(specification),
               "--goto-btor2-map-out", str(mapping_path)]
    if run(command, directory, "export", args.timeout):
        raise ValueError(f"C2BTOR conversion failed; see {directory / 'export.stderr'}")
    mapping = json.loads(mapping_path.read_text())
    if before != digest(program):
        raise ValueError("input changed during translation")
    files = {str(program)}
    for instruction in mapping["instructions"]:
        file_name = instruction["source"]["file_name"]
        if file_name and not file_name.startswith("<"):
            source = Path(file_name).resolve()
            if not source.is_file():
                raise ValueError(f"source file is unavailable: {source}")
            instruction["source"]["file_name"] = str(source)
            files.add(str(source))
    mapping["model_sha256"] = digest(model)
    mapping["source_hashes"] = {path: digest(path) for path in sorted(files)}
    mapping["input_files"] = [str(program)]
    mapping["command_line"] = command
    mapping["specification"] = specification
    save_json(mapping_path, mapping)
    print(mapping_path)


def read_model(path):
    nodes, states, bads = {}, [], []
    for line in Path(path).read_text().splitlines():
        fields = line.split(";", 1)[0].split()
        if not fields:
            continue
        node, operation = int(fields[0]), fields[1]
        nodes[node] = fields[1:]
        if operation == "state":
            states.append(node)
        elif operation == "bad":
            bads.append(node)
    return nodes, states, bads


def normalize_witness(text):
    """Strip solver logs without matching UNSAT as SAT or inventing values."""
    text = re.sub(r"\x1b\[[0-9;]*m", "", text)
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    start = next((i for i, line in enumerate(lines) if line.lower() == "sat"), None)
    if start is None or any(line.lower() == "unsat" for line in lines[:start + 1]):
        raise ValueError("no SAT BTOR2 witness (SAFE/UNKNOWN has no violation witness)")
    body = lines[start + 1:]
    while body and body[0].lower() == "sat":
        body.pop(0)
    if not body or not re.fullmatch(r"b\d+(?:\s+b\d+)*", body[0]):
        raise ValueError("expected BTOR2 bad-property indices; raw AIGER/ABC traces need back-translation first")
    try:
        end = body.index(".")
    except ValueError as error:
        raise ValueError("truncated BTOR2 witness (missing '.')") from error
    return "sat\n" + "\n".join(body[:end + 1]) + "\n", [int(x[1:]) for x in body[0].split()]


def read_frames(text):
    """BtorSim uses zero-based state/input ordinals, not BTOR node IDs."""
    frames = {}
    section = None
    time = -1
    for line in text.splitlines():
        line = line.strip()
        if not line or line == ".":
            continue
        if re.fullmatch(r"[#@]\d+", line):
            new_time = int(line[1:])
            if new_time < time:
                raise ValueError("non-monotone witness frames")
            time = new_time
            section = "states" if line[0] == "#" else "inputs"
            frames.setdefault(time, {"states": {}, "inputs": {}})
            continue
        if section is None:
            raise ValueError(f"unexpected BtorSim output: {line}")
        parts = line.split()
        if len(parts) < 2 or not parts[0].isdigit():
            raise ValueError(f"malformed witness assignment: {line}")
        # Array rows remain in the simulator log. This translator reads scalar
        # PC/nondet results only; never interpret an array index as a value.
        if parts[1].startswith("["):
            continue
        if not re.fullmatch(r"[01]+", parts[1]):
            raise ValueError("non-concrete witness value; refusing to replace it with zero")
        index = int(parts[0])
        if index in frames[time][section]:
            raise ValueError("duplicate witness assignment")
        frames[time][section][index] = parts[1]
    if sorted(frames) != list(range(len(frames))) or not frames:
        raise ValueError("witness must contain consecutive frames from zero")
    return frames


def omit_initialized_array_rows(witness, nodes, states):
    """Replay array init expressions from the model, preserving unconstrained data.

    BtorMC --trace-gen-full emits redundant initialized-array rows at #0.
    BtorSim rejects some array-to-array initializers when those rows are given
    explicitly. Standard sparse witnesses may omit them: the simulator derives
    them from init. Inputs, uninitialized arrays and all later rows are retained.
    """
    initialized = {int(fields[2]) for fields in nodes.values() if fields[0] == "init"}
    arrays = {index for index, node in enumerate(states) if node in initialized
              and nodes[int(nodes[node][1])][:2] == ["sort", "array"]}
    section = None
    lines = []
    for line in witness.splitlines():
        if re.fullmatch(r"[#@]\d+", line):
            section = line
        fields = line.split()
        if section == "#0" and fields and fields[0].isdigit() and int(fields[0]) in arrays:
            continue
        lines.append(line)
    return "\n".join(lines) + "\n"


def call_location(source, function, is_return, destination=None):
    """Resolve an unambiguous direct, nullary C call; reject macros/ambiguity.

    CBMC locations need not identify the ')' required by function_return.
    Mask comments/literals without changing offsets, then use the original
    file to recover the precise column. No fuzzy line/column guessing.
    """
    path = Path(source["file_name"])
    text = path.read_text()
    token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\''
    clean = re.sub(token, lambda m: re.sub(r"[^\n]", " ", m[0]), text)
    line = int(source["line"])
    matches = []
    for match in re.finditer(r"\b" + re.escape(function) + r"\s*\(\s*\)", clean):
        if clean.count("\n", 0, match.start()) + 1 == line:
            matches.append(match)
    if len(matches) > 1 and destination:
        # GotoIR proves that this call's result flows directly into this
        # variable. Match only a direct initializer/assignment in the source;
        # never assign columns by the order of unspecified C evaluations.
        prefix = r"(?<![\w.>])\b" + re.escape(destination) + r"\s*=\s*$"
        matches = [match for match in matches
                   if re.search(prefix, clean[:match.start()])]
    if len(matches) != 1:
        raise ValueError(f"cannot locate unique direct call {function} at {path}:{line}")
    offset = matches[0].end() - 1 if is_return else matches[0].start()
    return {"file_name": str(path), "line": clean.count("\n", 0, offset) + 1,
            "column": offset - clean.rfind("\n", 0, offset)}


def translate(args):
    directory = fresh_directory(args.output_dir)
    mapping = json.loads(Path(args.map).read_text())
    if mapping.get("format_version") != "1" or "model_sha256" not in mapping:
        raise ValueError("use the export subcommand to produce a hash-bound map")
    if digest(args.model) != mapping["model_sha256"]:
        raise ValueError("BTOR2 model does not match the translation map")
    for path, expected in mapping["source_hashes"].items():
        if digest(path) != expected:
            raise ValueError(f"source changed since translation: {path}")
    widths = (mapping["int_width"], mapping["long_width"], mapping["pointer_width"])
    data_model = {(32, 32, 32): "ILP32", (32, 64, 64): "LP64"}.get(widths)
    if data_model is None:
        raise ValueError(f"SV-COMP does not describe this data model: {widths}")
    model_nodes, state_nodes, bad_nodes = read_model(args.model)
    state_indices = {node: index for index, node in enumerate(state_nodes)}
    pc_index = state_indices[mapping["pc_node"]]
    witness, bads = normalize_witness(Path(args.witness).read_text())
    if any(index >= len(bad_nodes) for index in bads):
        raise ValueError("witness references a nonexistent bad property")
    auxiliary = {entry["bad_node"]: entry for entry in
                 mapping.get("memory", {}).get("properties", [])}
    reached_auxiliary = [auxiliary[bad_nodes[index]] for index in bads
                         if bad_nodes[index] in auxiliary]
    if reached_auxiliary:
        kinds = sorted({entry["property_class"] for entry in reached_auxiliary})
        save_json(directory / "result.json", {
            "status": "model_limit" if "model_limit" in kinds else "memory_validity",
            "properties": reached_auxiliary,
            "source_violation": False,
            "explanation": "Backend reports an internal memory property; no C violation witness emitted."})
        raise ValueError("internal memory property (" + ", ".join(kinds) +
                         "): not an unreach-call violation witness")
    normalized = directory / "backend.witness"
    (directory / "backend.original.witness").write_text(witness)
    normalized.write_text(omit_initialized_array_rows(witness, model_nodes, state_nodes))
    command = [str(Path(args.btorsim).resolve()), "--states", str(Path(args.model).resolve()), str(normalized)]
    if run(command, directory, "simulation", args.timeout):
        raise ValueError(f"BtorSim rejected the counterexample; see {directory / 'simulation.stderr'}")
    frames = read_frames((directory / "simulation.stdout").read_text())
    # BtorSim omits initialized states at #0. The converter always initializes
    # pc to zero. Verify this from the model rather than filling missing frames.
    pc_initializers = [fields[3] for fields in model_nodes.values()
                       if fields[0] == "init" and int(fields[2]) == mapping["pc_node"]]
    if len(pc_initializers) != 1 or model_nodes[int(pc_initializers[0])][0] != "zero":
        raise ValueError("unsupported PC initialization")
    pc_sort = int(model_nodes[mapping["pc_node"]][1])
    pc_width = int(model_nodes[pc_sort][2])
    frames[0]["states"].setdefault(pc_index, "0" * pc_width)
    instructions = {entry["pc"]: entry for entry in mapping["instructions"]}
    target_function = error_function(mapping["specification"])
    segments, replay = [], []
    reached_target = False
    for time, frame in frames.items():
        bits = frame["states"].get(pc_index)
        if bits is None or len(bits) != pc_width:
            raise ValueError(f"missing or malformed simulated PC at frame {time}")
        pc = int(bits, 2)
        if pc not in instructions:
            raise ValueError(f"PC {pc} has no source mapping")
        instruction = instructions[pc]
        replay.append({"time": time, "pc": pc, "goto_location": instruction["goto_location"],
                       "source": instruction["source"], "states": frame["states"], "inputs": frame["inputs"]})
        # CBMC library models (e.g. malloc success/failure) introduce internal
        # nondet calls that have no call site in the original C program.
        # Retain their circuit trace, but do not fabricate software waypoints.
        if "nondet_function" in instruction and not instruction["source"]["file_name"].startswith("<"):
            result_node = instruction["result_state_node"]
            result_index = state_indices[result_node]
            next_frame = frames.get(time + 1)
            if next_frame is None or result_index not in next_frame["states"]:
                raise ValueError("missing post-state for nondeterministic call")
            value_bits = next_frame["states"][result_index]
            sort = model_nodes[int(model_nodes[result_node][1])]
            if sort[:2] != ["sort", "bitvec"] or len(value_bits) != int(sort[2]):
                raise ValueError("nondet result width mismatch")
            result_type = instruction["result_type"]
            if result_type not in {"signedbv", "unsignedbv", "c_bool", "bool"}:
                raise ValueError(f"unsupported nondet return type: {result_type}")
            value = int(value_bits, 2)
            if result_type == "signedbv" and value_bits[0] == "1":
                value -= 1 << len(value_bits)
            waypoint = {"type": "function_return", "action": "follow",
                        "location": call_location(instruction["source"], instruction["nondet_function"],
                                                  True, instruction.get("result_destination")),
                        "constraint": {"format": "acsl_expression", "value": f"\\result == {value}"}}
            segments.append({"segment": [{"waypoint": waypoint}]})
        # A property can be visited safely earlier in a loop. Only the final
        # simulated violation frame is a target, never its first visit.
        if time == len(frames) - 1:
            if instruction.get("property_class") == "unwind":
                raise ValueError("loop bound exhausted: an unwinding assertion is not a C violation witness")
            if instruction["bad_node"] not in [bad_nodes[index] for index in bads]:
                raise ValueError("final PC does not match a claimed bad property")
            target = {"type": "target", "action": "follow",
                      "location": call_location(instruction["source"], target_function, False)}
            segments.append({"segment": [{"waypoint": target}]})
            reached_target = True
    if not reached_target:
        raise ValueError("no mapped violation target")
    metadata = {"format_version": "2.0", "uuid": str(uuid.uuid4()),
                "creation_time": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                "producer": {"name": "C2Btor", "version": "development", "description": "BtorSim-checked counterexample back-translation"},
                "task": {"input_files": mapping["input_files"],
                         "input_file_hashes": {p: mapping["source_hashes"][p] for p in mapping["input_files"]},
                         "specification": mapping["specification"], "data_model": data_model, "language": "C"}}
    save_json(directory / "trace.json", replay)
    save_json(directory / "witness.yml", [{"entry_type": "violation_sequence", "metadata": metadata, "content": segments}])
    print(directory / "witness.yml")


def validate(args):
    directory = fresh_directory(args.output_dir)
    witness_path = Path(args.witness).resolve()
    witness = json.loads(witness_path.read_text())
    task = witness[0]["metadata"]["task"]
    for path in task["input_files"]:
        if digest(path) != task["input_file_hashes"][path]:
            raise ValueError(f"witness input hash mismatch: {path}")
    specification = directory / "property.prp"
    specification.write_text(task["specification"] + "\n")
    cpachecker = Path(args.cpachecker).resolve()
    config_root = cpachecker.parent.parent / "config"
    component = config_root / "components/violationWitnessValidation.properties"
    common = config_root / "includes/witness-validation.properties"
    if not component.is_file() or not common.is_file():
        raise ValueError("CPAchecker installation lacks the predicate witness-validation configuration")
    # Select the predicate validator explicitly. Do not fall through to a
    # different analysis after solver-load failures: some installations accept
    # even contradictory function_return constraints in their BDD fallback.
    config = directory / "validator.properties"
    config.write_text(f"#include {component}\n#include {common}\n"
                      f"witness.validation.violation.config = {config}\n")
    command = [str(cpachecker), "--config", str(config),
               "--witness", str(witness_path), "--spec", str(specification),
               "--32" if task["data_model"] == "ILP32" else "--64",
               "--heap", "2048M", "--timelimit", str(args.timeout), "--no-output-files",
               "--output-path", str(directory / "cpachecker")]
    if args.solver:
        command += ["--option", "solver.solver=" + args.solver]
    if args.integer_encoding:
        command += ["--option", "cpa.predicate.encodeBitvectorAs=INTEGER",
                    "--option", "cpa.predicate.encodeFloatAs=RATIONAL"]
    elif args.no_floats:
        command += ["--option", "cpa.predicate.encodeFloatAs=UNSUPPORTED"]
    command += task["input_files"]
    try:
        code = run(command, directory, "validation", args.timeout + 15)
    except subprocess.TimeoutExpired:
        save_json(directory / "result.json", {
            "status": "not-confirmed", "validator_verdict": "TIMEOUT",
            "solver": args.solver or "CPAchecker default",
            "encoding": "integer/rational approximation" if args.integer_encoding else "bitvector",
            "witness_sha256": digest(witness_path),
        })
        raise
    output = (directory / "validation.stdout").read_text()
    # FALSE in witness-validation mode means the constrained error execution
    # was confirmed. Successful process exit alone proves nothing.
    confirmed = code == 0 and bool(re.search(r"^Verification result: FALSE\.", output, re.M))
    verdict = re.search(r"^Verification result: (TRUE|FALSE|UNKNOWN)\b", output, re.M)
    save_json(directory / "result.json", {
        "status": "confirmed" if confirmed else "not-confirmed", "returncode": code,
        "validator_verdict": verdict[1] if verdict else "ERROR",
        "solver": args.solver or "CPAchecker default",
        "encoding": "integer/rational approximation" if args.integer_encoding else "bitvector",
        "floats": "disabled" if args.no_floats else "enabled",
        "witness_sha256": digest(witness_path),
    })
    print(directory / "result.json")
    if not confirmed:
        raise ValueError("CPAchecker did not confirm the violation witness; inspect validation logs")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    exp = commands.add_parser("export", help="export model and hash-bound translation map")
    exp.add_argument("--c2btor", "--cbmc", dest="cbmc", metavar="C2BTOR", required=True, help="C2BTOR executable")
    exp.add_argument("--program", required=True)
    exp.add_argument("--spec")
    exp.add_argument("--output-dir", required=True)
    exp.add_argument("--timeout", type=int, default=60)
    exp.add_argument("cbmc_args", metavar="C2BTOR_ARGS", nargs=argparse.REMAINDER)
    exp.set_defaults(action=export)
    trans = commands.add_parser("translate", help="simulate backend counterexample and emit YAML 2.0")
    for name in ("model", "map", "witness", "btorsim", "output-dir"):
        trans.add_argument("--" + name, required=True)
    trans.add_argument("--timeout", type=int, default=60)
    trans.set_defaults(action=translate)
    val = commands.add_parser("validate", help="independently validate the C witness with CPAchecker")
    for name in ("witness", "cpachecker", "output-dir"):
        val.add_argument("--" + name, required=True)
    val.add_argument("--solver", help="CPAchecker solver override, e.g. SMTINTERPOL")
    encoding = val.add_mutually_exclusive_group()
    encoding.add_argument("--integer-encoding", action="store_true",
                     help="explicitly use CPAchecker's integer/rational approximation (for solvers without bitvectors)")
    encoding.add_argument("--no-floats", action="store_true",
                     help="disable float formulas while retaining exact bitvectors, e.g. with PRINCESS")
    val.add_argument("--timeout", type=int, default=90)
    val.set_defaults(action=validate)
    args = parser.parse_args()
    try:
        args.action(args)
    except (OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        parser.exit(1, f"c2btor-witness: {error}\n")


if __name__ == "__main__":
    main()
