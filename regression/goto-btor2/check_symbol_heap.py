#!/usr/bin/env python3
"""Check assembler aliases and allocation-site identity against CBMC and rIC3.

Usage: python3 regression/goto-btor2/check_symbol_heap.py NEW_OUTPUT_DIRECTORY
"""
import json
import os
from pathlib import Path
import re
import subprocess
import sys

repo = Path(__file__).resolve().parents[2]
out = Path(sys.argv[1]).resolve()
out.mkdir(parents=True, exist_ok=False)
env = os.environ.copy()
if sys.platform == 'darwin':
    env['PATH'] = '/usr/bin:/bin:' + env['PATH']
flags = ['--inline', '--no-standard-checks', '--no-pointer-check',
         '--no-bounds-check', '--no-built-in-assertions']


def run(label, command, timeout=60):
    (out / (label + '.command.json')).write_text(json.dumps(command, indent=2))
    result = subprocess.run(command, env=env, cwd=repo, capture_output=True,
                            text=True, timeout=timeout)
    log = result.stdout + result.stderr
    (out / (label + '.log')).write_text(log)
    return result.returncode, log


results = []
for source in ['darwin_asm_connect', 'malloc_program_points', 'darwin_asm_raw']:
    if source == 'darwin_asm_raw' and sys.platform != 'darwin':
        continue
    for negative in ([False] if source == 'darwin_asm_raw' else [False, True]):
        label = source + ('-negative' if negative else '')
        expected = 'SAT' if negative else 'UNSAT'
        command = [str(repo / 'build/bin/c2btor'),
                   str(Path(__file__).with_name(source + '.c'))] + flags
        if source == 'malloc_program_points' and not negative:
            command += ['-DIDENTITY_ONLY']
        if negative:
            command += ['-DNEGATIVE_CONTROL']
        rc, log = run(label + '-reference', command + ['--unwind', '9', '--unwinding-assertions'])
        assert rc == (10 if negative else 0), (label, rc, log)
        model = out / (label + '.btor2')
        rc, log = run(label + '-convert', command + ['--goto-btor2',
                     '--goto-btor2-warn-comments', '--goto-btor2-out', str(model)])
        assert rc == 0, (label, rc, log)
        text = model.read_text()
        assert '__unknown_' not in text and '; ERROR:' not in text, label
        if source == 'malloc_program_points':
            assert '__next_heap_object' in text and '__memory_state_' in text
            assert '__heap_malloc_' not in text
        rc, log = run(label + '-syntax', [os.environ.get('CATBTOR', 'catbtor'), str(model)])
        assert rc == 0, (label, rc, log)
        rc, log = run(label + '-ric3', [os.environ.get('RIC3', 'ric3'), 'check', str(model),
                                      'ic3', '--frts', 'false', '--scorr', 'false',
                                      '--time-limit', '30'])
        assert expected in log.split(), (label, expected, rc, log)
        results.append({'case': label, 'cbmc': expected, 'ric3': expected})
        print(label, expected, flush=True)

for source in ['real_recursion', 'loop_malloc_summary']:
    model = out / (source + '.btor2')
    command = [str(repo / 'build/bin/c2btor'), str(Path(__file__).with_name(source + '.c'))]
    rc, log = run(source, command + flags + ['--goto-btor2', '--goto-btor2-out', str(model)])
    if source == 'real_recursion':
        assert rc != 0 and 'does not support recursive call' in log, (rc, log)
        result = 'rejected'
    else:
        assert rc == 0, (rc, log)
        assert '__next_heap_object' in model.read_text()
        assert 'model_limit_at_' in model.read_text()
        result = 'fresh allocation with explicit capacity'
    results.append({'case': source, 'result': result})
    print(source, result, flush=True)

(out / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
