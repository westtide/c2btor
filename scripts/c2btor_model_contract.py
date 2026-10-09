"""Preserve the boundary obligations required to interpret C2Btor UNSAT.

Suppression of auxiliary bads changes reporting, never the frozen execution
semantics. Solver adapters must check these obligations before accepting an
unbounded model result. A bounded absence remains bounded_no_violation.
"""
from pathlib import Path
import re

CONTRACT = '; c2btor-proof-contract 1'
OBLIGATION = re.compile(r'^; c2btor-proof-obligation (model_limit|memory_validity) (\d+)$')


def read_contract(model):
    lines = Path(model).read_text().splitlines()
    obligations = []
    for line in lines:
        match = OBLIGATION.fullmatch(line)
        if match:
            obligations.append((match[1], int(match[2])))
    return lines, CONTRACT in lines, obligations


def property_model(model, destination, *, boundaries_only=False):
    """Copy the same transition system and replace its bad property list.

    Nodes, initial states, inputs, constraints and next functions are kept.
    The copy is a solver query artifact, not a source-witness export model.
    """
    lines, known, obligations = read_contract(model)
    if not known:
        raise ValueError('model has no C2Btor proof contract; regenerate it before interpreting C safety')
    groups = {}
    if not boundaries_only:
        groups['complete_model'] = [int(line.split()[2]) for line in lines
                                    if re.match(r'^\d+ bad ', line)]
    for kind, node in obligations:
        groups.setdefault(kind if boundaries_only else 'complete_model', []).append(node)
    rows = [line.split() for line in lines if line and line[0].isdigit()]
    last = max(int(row[0]) for row in rows)
    boolean = next(int(row[0]) for row in rows if row[1:] == ['sort', 'bitvec', '1'])
    output = [line for line in lines if not re.match(r'^\d+ bad ', line)]
    indices = []
    for kind, nodes in groups.items():
        nodes = list(dict.fromkeys(nodes))
        if not nodes:
            continue
        condition = nodes[0]
        for node in nodes[1:]:
            last += 1
            output.append(f'{last} or {boolean} {condition} {node}')
            condition = last
        last += 1
        output.append(f'{last} bad {condition} proof_{kind}')
        indices.append(kind)
    if not indices:
        last += 1
        output.append(f'{last} zero {boolean}')
        output.append(f'{last+1} bad {last} proof_empty')
    Path(destination).write_text('\n'.join(output) + '\n')
    return indices


def solver_verdict(text):
    values = {line.strip().lower() for line in text.splitlines()}
    if 'sat' in values:
        return 'sat'
    if 'unsat' in values:
        return 'unsat'
    return 'unknown'


def unsat_status(model, engine, *, all_properties=False):
    """Return a conclusive model classification or request a boundary query."""
    lines, known, obligations = read_contract(model)
    if not known:
        return 'unverified_unsat'
    reported = {int(line.split()[2]) for line in lines if re.match(r'^\d+ bad ', line)}
    # Some backends (including a portfolio prepass and Pono's default p0)
    # may select one property. Check a single OR query before accepting all.
    if not all_properties and len(reported) > 1:
        return 'full_check_required'
    covered = all_properties and all(node in reported for _, node in obligations)
    if not obligations or covered:
        return 'bounded_no_violation' if engine in {'bmc', 'wl-bmc'} else 'model_unsat'
    return 'boundary_check_required'


def boundary_status(text, indices, engine):
    verdict = solver_verdict(text)
    if verdict == 'unsat':
        return 'bounded_no_violation' if engine in {'bmc', 'wl-bmc'} else 'model_unsat'
    if verdict == 'sat':
        claimed = re.search(r'^b(\d+)(?:\s|$)', text, re.M)
        if claimed and int(claimed[1]) < len(indices):
            return indices[int(claimed[1])]
        return 'model_boundary'
    return 'boundary_unknown'
