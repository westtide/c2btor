# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors

"""Validate and enrich C2Btor maps without changing their existing fields."""
import hashlib
import json
from pathlib import Path

from .btor2_parser import Btor2Model


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def data_model(mapping):
    widths = tuple(mapping.get(key) for key in ("int_width", "long_width", "pointer_width"))
    try:
        return {(32, 32, 32): "ILP32", (32, 64, 64): "LP64"}[widths]
    except KeyError as error:
        raise ValueError(f"unsupported C data model widths: {widths}") from error


def enrich_map(mapping, model_path):
    """Derived indexes refer only to original model nodes and source events.

    This is not an SSA or loop-summary expansion certificate. A zero node ID
    explicitly denotes an observation removed by projection.
    """
    model = Btor2Model(model_path)
    for group in mapping.get("array_loop_summary", {}).get("nondet_summaries", []):
        for source in [call["source"] for call in group["calls"]] + [group.get("loop_condition_entry", {})]:
            name = source.get("file_name", "")
            if name and not name.startswith("<"):
                path = str(Path(name).resolve())
                source["file_name"] = path
                mapping.setdefault("source_hashes", {})[path] = digest(path)
    mapping["schema_version"] = "c2btor-source-map-1"
    mapping["data_model"] = data_model(mapping)
    mapping["model_sha256"] = model.sha256
    return mapping


def load_map(map_path, model_path, source=None, specification=None, expected_data_model=None):
    mapping = json.loads(Path(map_path).read_text())
    if mapping.get("format_version") not in {"1", "2"}:
        raise ValueError("unsupported C2Btor source map format")
    model = Btor2Model(model_path)
    if mapping.get("model_sha256") != model.sha256:
        raise ValueError("model hash missing or mismatched; regenerate with c2btor-verify")
    files, hashes = mapping.get("input_files", []), mapping.get("source_hashes", {})
    if not files or any(path not in hashes for path in files):
        raise ValueError("hash-bound input_files and source_hashes are required")
    for path, expected in hashes.items():
        if digest(path) != expected:
            raise ValueError(f"source hash mismatch: {path}")
    if source is not None and Path(source).resolve() not in {Path(path).resolve() for path in files}:
        raise ValueError("source is not an input of the translation map")
    if specification is not None and mapping.get("specification", "").strip() != specification.strip():
        raise ValueError("property differs from the translation map")
    actual = data_model(mapping)
    if expected_data_model is not None and actual != expected_data_model:
        raise ValueError("data model differs from the translation map")
    if mapping.get("pc_node") not in {d.node for d in model.states}:
        raise ValueError("PC node is not an original BTOR2 state")
    return mapping, model
