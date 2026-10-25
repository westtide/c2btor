# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors

"""Internal YAML 2.1 dummy correctness writer, not an independently checked proof.

TODO: export real Carat inductive invariants and map them to C.
"""
import bisect
import datetime
import json
import os
from pathlib import Path
import re
import shlex
import tempfile
import uuid

from . import trace_recovery as recovery

def check_document(value):
    if len(value) != 1 or value[0]["entry_type"] != "invariant_set" or not value[0]["content"]:
        raise ValueError("correctness witness requires one nonempty invariant_set")
    if value[0]["metadata"]["format_version"] != "2.1":
        raise ValueError("correctness witness requires YAML version 2.1")
    for item in value[0]["content"]:
        inv = item.get("invariant", {})
        if inv.get("type") not in {"loop_invariant", "location_invariant"} or inv.get("format") != "c_expression":
            raise ValueError("supports loop/location invariants in c_expression format only")
    task = value[0]["metadata"]["task"]
    recovery.error_function(task["specification"])
    if task["language"] != "C" or task["data_model"] not in {"ILP32", "LP64"}:
        raise ValueError("unsupported witness target")
    return task

def _source_tokens(path):
    """Tokenize physical C positions for anchors, never evaluate C expressions.

    This is deliberately a lexical subset, not a preprocessor. Line remapping,
    conditionally compiled bodies, and line splicing require frontend anchors.
    Strings, character literals, comments and directives cannot become anchors.
    """
    source = Path(path).read_text()
    if re.search(r"\\\r?\n", source):
        raise ValueError("source anchor discovery does not support line splicing")
    directive = re.compile(r"^[ \t]*#([^\n]*)", re.M)
    directives = list(directive.finditer(source))
    for match in directives:
        if re.match(r"\s*(?:[0-9]|line\b|if\b|ifdef\b|ifndef\b|elif\b|else\b|endif\b)", match[1]):
            raise ValueError("source anchor discovery requires unambiguous physical C locations")
    hidden = [(m.start(), m.end()) for m in directives]
    newlines = [match.start() for match in re.finditer("\n", source)]
    pattern = re.compile(
        r"(?P<space>\s+)|(?P<comment>//[^\n]*|/\*[\s\S]*?\*/)"
        r"|(?P<literal>(?:u8|[LuU])?(?:\"(?:\\[\s\S]|[^\"\\])*\"|'(?:\\[\s\S]|[^'\\])*'))"
        r"|(?P<word>[A-Za-z_]\w*)|(?P<other>.)")
    tokens = []
    for match in pattern.finditer(source):
        if match.lastgroup in {"space", "comment"} or any(a <= match.start() < b for a, b in hidden):
            continue
        offset = match.start()
        newline_index = bisect.bisect_left(newlines, offset)
        line = newline_index + 1
        column = offset - (newlines[newline_index - 1] if newline_index else -1)
        tokens.append((match[0], line, column, match.lastgroup))
    return tokens

def _location(location, task_files, *, loop=False):
    """Check an exact map location against a real source token."""
    filename = str(Path(location["file_name"]).resolve())
    if filename not in task_files:
        raise ValueError("invariant anchor is outside witness task input files")
    tokens = _source_tokens(filename)
    try:
        line = int(location["line"])
        if loop and not location.get("column"):
            # CBMC does not always retain columns. The same physical line must
            # contain exactly one matching loop keyword; never search nearby.
            keywords = {location["kind"]} if location.get("kind") in {"for", "while", "do"} else {"for", "while", "do"}
            possible = [token for token in tokens if token[1] == line and token[0] in keywords and token[3] == "word"]
            if len(possible) != 1:
                raise ValueError("loop source line has no unique keyword anchor")
            column = possible[0][2]
        else:
            column = int(location["column"])
    except (TypeError, ValueError) as error:
        raise ValueError("invariant anchors require explicit integer line and column") from error
    function = location.get("function")
    if line <= 0 or column <= 0 or not isinstance(function, str) or not re.fullmatch(r"[A-Za-z_]\w*", function):
        raise ValueError("invariant anchors require positive positions and a C function name")
    matches = [token for token in tokens if token[1:3] == (line, column)]
    if len(matches) != 1 or matches[0][3] == "literal":
        raise ValueError("invariant anchor does not point to a C token start")
    if loop and matches[0][0] not in {"for", "while", "do"}:
        raise ValueError("loop invariant anchor must point to for, while or do")
    if not loop and matches[0][3] != "word" and matches[0][0] not in {";", "{"}:
        raise ValueError("statement invariant anchor does not point to a statement start")
    return {"file_name": filename, "line": line, "column": column, "function": function}

def _main_statement(path):
    """Find the first statement in an ordinary top-level main definition.

    Match the function declarator and its complete parameter list, then take
    the first token after its opening brace. Never relocate a map position to
    another source line. Unsupported declarations fail closed.
    """
    tokens = _source_tokens(path)
    depth, candidates = 0, []
    for index, token in enumerate(tokens):
        text = token[0]
        if depth == 0 and text == "main" and index + 1 < len(tokens) and tokens[index + 1][0] == "(":
            nesting, end = 1, index + 2
            while end < len(tokens) and nesting:
                nesting += (tokens[end][0] == "(") - (tokens[end][0] == ")")
                end += 1
            if nesting == 0 and end + 1 < len(tokens) and tokens[end][0] == "{":
                first = tokens[end + 1]
                if first[0] != "}" and not (end + 2 < len(tokens) and tokens[end + 2][0] == ":"):
                    candidates.append({"file_name": str(Path(path).resolve()), "line": first[1],
                                       "column": first[2], "function": "main"})
        if token[3] != "literal":
            depth += (text == "{") - (text == "}")
        if depth < 0:
            raise ValueError("unbalanced C source while locating invariant anchor")
    if depth != 0 or len(candidates) != 1:
        raise ValueError("no unique main statement anchor; provide a frontend statement/loop anchor")
    return candidates[0]

def correctness_inputs(model_path, map_path):
    """Check task/model/source identity without restricting true to scalar BV."""
    mapping = json.loads(Path(map_path).read_text())
    if mapping.get("format_version") not in {"1", "2"}:
        raise ValueError("correctness witness requires source map version 1 or 2")
    if recovery.digest(model_path) != mapping.get("model_sha256"):
        raise ValueError("model/map hash mismatch")
    files = mapping.get("input_files")
    hashes = mapping.get("source_hashes")
    if not isinstance(files, list) or not files or not isinstance(hashes, dict):
        raise ValueError("correctness witness requires hash-bound task input files")
    if len(set(files)) != len(files) or any(not Path(path).is_absolute() for path in files):
        raise ValueError("task input paths must be unique absolute paths")
    if any(str(Path(path).resolve()) != path for path in files):
        raise ValueError("task input paths must be canonical")
    for path, expected in hashes.items():
        if recovery.digest(path) != expected:
            raise ValueError(f"source hash mismatch: {path}")
    if any(path not in hashes for path in files):
        raise ValueError("task input file is missing its source hash")
    widths = (mapping["int_width"], mapping["long_width"], mapping["pointer_width"])
    data_model = {(32, 32, 32): "ILP32", (32, 64, 64): "LP64"}.get(widths)
    if data_model is None:
        raise ValueError("correctness witness supports ILP32/LP64 only")
    recovery.error_function(mapping["specification"])
    if any(row["kind"] in {"START_THREAD", "END_THREAD", "ATOMIC_BEGIN", "ATOMIC_END"}
           for row in mapping["instructions"]):
        raise ValueError("correctness witness currently supports sequential C only")
    task = {"input_files": files, "input_file_hashes": {p: hashes[p] for p in files},
            "specification": mapping["specification"], "data_model": data_model, "language": "C"}
    return mapping, task

class InvariantProvider:
    """Source-invariant provider interface, separate from solver verdict parsing."""

    def generate(self, source_map, result, anchor=None):
        raise NotImplementedError

class DummyInvariantProvider(InvariantProvider):
    """Emit valid but uninformative invariants only after explicit unbounded Safe.

    This class does not run Carat and does not infer Safe from an expected YAML
    verdict, a bounded result, a parser check, or the truth of the invariant.
    """
    name = "dummy"

    def generate(self, mapping, result, anchor=None):
        if result != "Safe":
            raise ValueError("dummy correctness witness requires an explicit unbounded Safe verdict")
        files, candidates = set(mapping["input_files"]), []
        for row in mapping["instructions"]:
            for key, kind in (("loop_condition_entry", "loop_invariant"), ("statement_entry", "location_invariant")):
                if key in row:
                    location = _location(row[key], files, loop=kind == "loop_invariant")
                    candidates.append((kind, location))
        # A loop anchor is sufficient and does not require parsing a main body.
        # Acyclic programs need an actual statement inside a compound statement.
        if not candidates or anchor is not None:
            for path in mapping["input_files"]:
                try:
                    candidates.append(("location_invariant", _location(_main_statement(path), files)))
                except ValueError:
                    continue
        if anchor is not None:
            requested = _location(anchor, files)
            candidates = [(kind, location) for kind, location in candidates if location == requested]
            if not candidates:
                raise ValueError("explicit invariant anchor is not a verified statement or loop entry")
        records, seen = [], set()
        for kind, location in candidates:
            identity = (kind, *location.values())
            if identity in seen:
                continue
            seen.add(identity)
            records.append({"invariant": {"type": kind, "location": location,
                                           "value": "1", "format": "c_expression"}})
        if not records:
            raise ValueError("no verified source statement or loop anchor for correctness witness")
        return records

def publish_document(path, document):
    """Check the document structure and publish a complete YAML file."""
    check_document(document)
    path = Path(path)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                         prefix="." + path.name + ".", delete=False) as stream:
            temporary = Path(stream.name)
            recovery.dump_witness(document, stream)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return path

def generate_weak(model_path, map_path, directory, result=None, anchor=None):
    """Export a weak witness after the caller has checked Carat's Safe result.

    The returned path denotes a generated candidate, never independent
    semantic validation. Official format checks run in the test suite.
    """
    if result != "Safe":
        raise ValueError("weak correctness witness requires an explicit unbounded Safe verdict")
    mapping, task = correctness_inputs(model_path, map_path)
    content = DummyInvariantProvider().generate(mapping, result, anchor)
    document = [{"entry_type": "invariant_set", "metadata": {
        "format_version": "2.1", "uuid": str(uuid.uuid4()),
        "creation_time": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "producer": {"name": "C2Btor", "version": mapping.get("producer_version", "development"),
                     "command_line": shlex.join(mapping.get("command_line", [])),
                     "description": "Dummy invariant provider: universally true invariant; independent Safe verdict required"},
        "task": task}, "content": content}]
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    return publish_document(directory / "witness.yml", document)
