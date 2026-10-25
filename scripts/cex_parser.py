# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors

"""Strict, sparse BTOR2/Carat .cexb parsing; no synthesized scalar values."""
from dataclasses import dataclass, field
import io
from pathlib import Path
import re


@dataclass
class ArrayValue:
    default: str | None = None
    entries: dict = field(default_factory=dict)


@dataclass
class Trace:
    bads: list
    frames: dict


def _lines(stream):
    for raw in stream:
        line = re.sub(r"\x1b\[[0-9;]*m", "", raw).strip()
        if line:
            yield line


def _header(lines, model):
    if next(lines, "").lower() != "sat":
        raise ValueError("standard BTOR2 counterexample must start with sat")
    line = next(lines, "")
    if not re.fullmatch(r"b\d+(?:\s+b\d+)*", line):
        raise ValueError("missing BTOR2 bad-property ordinals")
    bads = [int(x[1:]) for x in line.split()]
    if len(set(bads)) != len(bads) or any(x >= len(model.bads) for x in bads):
        raise ValueError("duplicate or nonexistent bad-property ordinal")
    return bads


def _frames(lines, model):
    time, section, frame = -1, None, None
    for line in lines:
        if line == ".":
            if frame is None:
                raise ValueError("counterexample must start at #0 with consecutive frames")
            yield time, frame
            return
        if re.fullmatch(r"[#@]\d+", line):
            next_time = int(line[1:])
            next_section = "states" if line[0] == "#" else "inputs"
            if time == -1:
                if next_time != 0 or next_section != "states":
                    raise ValueError("counterexample must start at #0 with consecutive frames")
            elif next_time == time:
                if section != "states" or next_section != "inputs":
                    raise ValueError("duplicate or non-monotone counterexample frame")
            elif next_time != time + 1:
                raise ValueError("duplicate or non-monotone counterexample frame")
            if next_time != time:
                if frame is not None:
                    yield time, frame
                frame = {"states": {}, "inputs": {}}
            time, section = next_time, next_section
            continue
        if section is None:
            raise ValueError("assignment before a counterexample frame")
        fields = line.split()
        if len(fields) < 2 or not fields[0].isdigit():
            raise ValueError(f"malformed counterexample assignment: {line}")
        declaration = model.declaration(section, int(fields[0]))
        values = frame[section]
        sort = declaration.sort
        if sort.kind == "array":
            if len(fields) < 3 or not re.fullmatch(r"\[(?:\*|[01]+)\]", fields[1]):
                raise ValueError("array assignment requires [index] or [*]")
            index, bits = fields[1][1:-1], fields[2]
            if len(bits) != sort.width or set(bits) - {"0", "1"}:
                raise ValueError("non-concrete or wrong-width array element")
            array = values.setdefault(declaration.node, ArrayValue())
            if index == "*":
                if array.default is not None:
                    raise ValueError("duplicate array default")
                array.default = bits
            else:
                if len(index) != sort.index_width:
                    raise ValueError("wrong-width array index")
                if index in array.entries:
                    raise ValueError("duplicate array index")
                array.entries[index] = bits
        else:
            bits = fields[1]
            if len(bits) != sort.width or set(bits) - {"0", "1"}:
                raise ValueError("non-concrete or wrong-width scalar assignment")
            if declaration.node in values:
                raise ValueError("duplicate scalar assignment")
            values[declaration.node] = bits
    raise ValueError("truncated counterexample (missing '.')")


class CexStream:
    """One frame at a time. Exhaustion checks the terminator and trailing data.

    Values belong to the consumer: pending array-summary groups may keep the
    concrete array values, but the reader never keeps earlier frames.
    """
    def __init__(self, stream, model, allow_trailing_log=False):
        self.lines = _lines(stream)
        self.bads = _header(self.lines, model)
        self._frames = _frames(self.lines, model)
        self.allow_trailing_log = allow_trailing_log
        self.frame_count, self.complete = 0, False

    def __iter__(self):
        return self

    def __next__(self):
        if self.complete:
            raise StopIteration
        try:
            frame = next(self._frames)
        except StopIteration:
            if not self.allow_trailing_log and next(self.lines, None) is not None:
                raise ValueError("data after counterexample terminator")
            self.complete = True
            raise
        self.frame_count += 1
        return frame


def parse_cex(text, model):
    """Compatibility API for small callers; production uses open_cex."""
    reader = CexStream(io.StringIO(text), model)
    return Trace(reader.bads, dict(reader))


def open_cex(path, model):
    """Context manager that validates all input, even if a consumer stops early."""
    from contextlib import contextmanager

    @contextmanager
    def opened():
        with Path(path).open(encoding="utf-8") as stream:
            reader = CexStream(stream, model)
            yield reader
            for _ in reader:
                pass
    return opened()
