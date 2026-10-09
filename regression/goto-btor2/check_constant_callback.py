#!/usr/bin/env python3
"""Semantic regression: CBMC reference versus C2Btor + rIC3, with controls.

Usage: python3 regression/goto-btor2/check_constant_callback.py OUTPUT_DIR
OUTPUT_DIR must be new. Set RIC3/CATBTOR to override checker executables.
"""
import json
import os
from pathlib import Path
import subprocess
import sys

repo = Path(__file__).resolve().parents[2]
out = Path(sys.argv[1]).resolve()
out.mkdir(parents=True, exist_ok=False)
env = os.environ.copy()
if sys.platform == 'darwin':
    env['PATH'] = '/usr/bin:/bin:' + env['PATH']
ric3 = os.environ.get('RIC3', 'ric3')
catbtor = os.environ.get('CATBTOR', 'catbtor')
base = [str(repo / 'build/bin/c2btor'), str(Path(__file__).with_name('constant_callback.c')),
        '--inline', '--no-standard-checks', '--no-pointer-check',
        '--no-bounds-check', '--no-built-in-assertions']

def run(label, cmd, timeout=45):
    (out / (label + '.command.json')).write_text(json.dumps(cmd, indent=2))
    result = subprocess.run(cmd, env=env, cwd=repo, capture_output=True,
                            text=True, timeout=timeout)
    text = result.stdout + result.stderr
    (out / (label + '.log')).write_text(text)
    return result.returncode, text

cases = [
    ('constant', [], 'UNSAT'),
    ('negative', ['NEGATIVE_CONTROL'], 'SAT'),
    ('alias', ['ALIAS_WRITE'], 'UNSAT'),
    ('dynamic', ['DYNAMIC_TARGET', 'NO_DISTRACTOR'], 'UNSAT'),
    ('dynamic-negative', ['DYNAMIC_TARGET', 'NO_DISTRACTOR', 'NEGATIVE_CONTROL'], 'SAT'),
    ('loop', ['LOOP_TARGET', 'NO_DISTRACTOR'], 'UNSAT'),
]
summary = []
for label, definitions, expected in cases:
    cmd = base + ['-D' + d for d in definitions]
    rc, log = run(label + '-reference', cmd + ['--unwind', '4', '--unwinding-assertions'])
    assert rc == (0 if expected == 'UNSAT' else 10), (label, rc, log)
    model = out / (label + '.btor2')
    rc, log = run(label + '-convert', cmd + ['--goto-btor2', '--goto-btor2-out', str(model)])
    assert rc == 0, (label, rc, log)
    assert '__unknown_' not in model.read_text() and '; ERROR:' not in model.read_text()
    rc, log = run(label + '-syntax', [catbtor, str(model)])
    assert rc == 0, (label, log)
    rc, log = run(label + '-ric3', [ric3, 'check', str(model), 'portfolio', '--time-limit', '30'])
    assert expected in log.split(), (label, rc, log)
    summary.append({'case': label, 'reference': expected, 'btor2': expected})
    print(label, expected, flush=True)

# A call that may overwrite the context must discard the previously known target.
# The missing body is intentionally not given a model: conversion must fail closed.
model = out / 'unknown-store.btor2'
rc, log = run('unknown-store', base + ['-DUNKNOWN_WRITE', '--goto-btor2',
                                    '--goto-btor2-out', str(model)])
assert rc != 0 and 'Unsupported call' in log and 'unknown_write' in log, (rc, log)
summary.append({'case': 'unknown-store', 'conversion': 'rejected'})

# Wider byte views introduced for the distractor now retain source bits and
# nondeterministic padding. Check both dynamic targets, without pruning either.
for negative in [False, True]:
    label = 'dynamic-with-distractor' + ('-negative' if negative else '')
    cmd = base + ['-DDYNAMIC_TARGET'] + (['-DNEGATIVE_CONTROL'] if negative else [])
    expected = 'SAT' if negative else 'UNSAT'
    rc, log = run(label + '-reference', cmd + ['--unwind', '4', '--unwinding-assertions'])
    assert rc == (10 if negative else 0), (label, rc, log)
    model = out / (label + '.btor2')
    rc, log = run(label + '-convert', cmd + ['--goto-btor2', '--goto-btor2-out', str(model)])
    assert rc == 0, (label, rc, log)
    assert '__unknown_' not in model.read_text()
    rc, log = run(label + '-syntax', [catbtor, str(model)])
    assert rc == 0, (label, log)
    rc, log = run(label + '-ric3', [ric3, 'check', str(model), 'portfolio', '--time-limit', '30'])
    assert expected in log.split(), (label, rc, log)
    summary.append({'case': label, 'reference': expected, 'btor2': expected})
(out / 'results.json').write_text(json.dumps(summary, indent=2))
print('All callback regression checks passed.', flush=True)
