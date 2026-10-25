# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors

"""Publish a completed witness atomically, without replacing an older file."""
import json
import os
from pathlib import Path
import tempfile


def publish_file(output, source, *, consume=False):
    """Atomic publication without reading a large completed witness into RAM."""
    import shutil
    output = Path(output).absolute()
    output.parent.mkdir(parents=True, exist_ok=True)
    if consume:
        # Our candidates are created under output.parent, on the same filesystem.
        # Publish the already complete inode atomically, then remove the private
        # name; no second 80 MB copy and no mutable duplicate remains.
        with Path(source).open('rb') as stream:
            os.fsync(stream.fileno())
        os.link(source, output)
        Path(source).unlink()
        return output
    descriptor, temporary = tempfile.mkstemp(prefix=".witness-", dir=output.parent)
    try:
        with os.fdopen(descriptor, "wb") as stream, Path(source).open("rb") as incoming:
            shutil.copyfileobj(incoming, stream, length=1024 * 1024)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, output)
    finally:
        os.unlink(temporary)
    return output


class SequenceWriter:
    """Write YAML 2.1 incrementally, keeping each dynamic call in order.

    The bounded cache reuses serialized text, never events. Official format
    validation belongs to the test suite; replay and source checks run before
    values reach this writer.
    """
    def __init__(self, stream, metadata):
        from .trace_recovery import error_function
        if metadata.get("format_version") != "2.1":
            raise ValueError("expected witness format 2.1")
        error_function(metadata["task"]["specification"])
        self.stream, self.cache, self.count, self.target = stream, {}, 0, False
        stream.write("- entry_type: violation_sequence\n  metadata: ")
        stream.write(json.dumps(metadata, ensure_ascii=False, separators=(",", ":")))
        stream.write("\n  content:\n")

    def append(self, waypoint):
        if self.target:
            raise ValueError("unreach-call target must be the final waypoint")
        if waypoint.get("action") != "follow":
            raise ValueError("streamed safety segment requires exactly one follow waypoint")
        if waypoint.get("type") not in {"function_return", "branching", "target"}:
            raise ValueError("unsupported safety waypoint type")
        location = waypoint.get("location", {})
        if (not isinstance(location.get("file_name"), str) or not location["file_name"] or
                type(location.get("line")) is not int or location["line"] <= 0 or
                ("column" in location and (type(location["column"]) is not int or location["column"] <= 0))):
            raise ValueError("waypoint requires a concrete source location")
        normalized = dict(waypoint)
        value = None
        if "constraint" in waypoint:
            constraint = waypoint["constraint"]
            if not isinstance(constraint, dict) or not isinstance(constraint.get("value"), str):
                raise ValueError("waypoint constraint.value must be a string")
            value = constraint["value"]
            normalized["constraint"] = dict(constraint, value="")
        key = json.dumps(normalized, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        cached = self.cache.get(key)
        if cached is None:
            # Bound memoization independently of the number of source positions.
            if len(self.cache) >= 4096:
                self.cache.clear()
        # Keep only the last serialized value per already memoized shape.
        # Reuse bytes, never events: every dynamic call still writes a segment.
        rendered = (cached[1] if cached is not None and cached[0] == value else
                    json.dumps(waypoint, ensure_ascii=False, separators=(",", ":")))
        self.cache[key] = (value, rendered)
        self.stream.write("    - segment:\n        - waypoint: ")
        self.stream.write(rendered)
        self.stream.write("\n")
        self.count += 1
        self.target = waypoint.get("type") == "target"

    def finish(self):
        if not self.target or not self.count:
            raise ValueError("unreach-call witness must end with exactly one target waypoint")
