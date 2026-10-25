# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors

"""Read original BTOR2 declaration order separately from node identifiers."""
from dataclasses import dataclass
import hashlib
from pathlib import Path


@dataclass(frozen=True)
class Sort:
    kind: str
    width: int = 0
    index_width: int = 0


@dataclass(frozen=True)
class Declaration:
    node: int
    ordinal: int
    kind: str
    sort: Sort
    name: str


class Btor2Model:
    """Declaration reader; full parser/type checking remains catbtor's job."""

    def __init__(self, path):
        self.path = Path(path).resolve()
        raw = self.path.read_bytes()
        self.sha256 = hashlib.sha256(raw).hexdigest()
        self.nodes, self.sorts = {}, {}
        self.states, self.inputs, self.bads = [], [], []
        self.initialized, self.successors = set(), {}
        for line_number, line in enumerate(raw.decode().splitlines(), 1):
            fields = line.split(";", 1)[0].split()
            if not fields:
                continue
            try:
                node = int(fields[0])
                if node <= 0 or node in self.nodes or len(fields) < 2:
                    raise ValueError("duplicate or invalid node identifier")
                operation = fields[1]
                if operation == "sort":
                    if fields[2] == "bitvec" and len(fields) == 4:
                        width = int(fields[3])
                        if width <= 0:
                            raise ValueError("nonpositive bit width")
                        sort = Sort("bitvec", width)
                    elif fields[2] == "array" and len(fields) == 5:
                        index, element = (self.sorts[int(x)] for x in fields[3:5])
                        if index.kind != "bitvec" or element.kind != "bitvec":
                            raise ValueError("nested or non-bitvector arrays are unsupported")
                        sort = Sort("array", element.width, index.width)
                    else:
                        raise ValueError("malformed sort")
                    self.sorts[node] = sort
                elif operation in {"state", "input"}:
                    declarations = self.states if operation == "state" else self.inputs
                    sort = self.sorts[int(fields[2])]
                    declarations.append(Declaration(node, len(declarations), operation, sort,
                                                    " ".join(fields[3:])))
                elif operation == "bad":
                    self.bads.append(node)
                elif operation == "init":
                    self.initialized.add(int(fields[3]))
                elif operation == "next":
                    self.successors[int(fields[3])] = int(fields[4])
                self.nodes[node] = fields[1:]
            except (ValueError, KeyError, IndexError) as error:
                raise ValueError(f"BTOR2 declaration at {self.path}:{line_number}: {error}") from error
        self.by_node = {d.node: d for d in self.states + self.inputs}
        if not self.nodes:
            raise ValueError("empty BTOR2 model")

    def declaration(self, section, ordinal):
        declarations = self.states if section == "states" else self.inputs
        if ordinal < 0 or ordinal >= len(declarations):
            raise ValueError(f"{section} declaration ordinal {ordinal} is out of range")
        return declarations[ordinal]
