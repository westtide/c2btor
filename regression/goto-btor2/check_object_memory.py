#!/usr/bin/env python3
"""Object-local alias, lifetime, capacity and structural regressions.

All models are generated from C. Positive cases also have completion controls;
bounded absence is never reported as an unbounded safety proof.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
FLAGS = ['--inline', '--no-standard-checks', '--no-pointer-check',
         '--no-bounds-check', '--no-built-in-assertions']
NEGATIVE = {4: 'memory_validity', 6: 'unsupported', 7: 'model_limit',
            8: 'model_limit', 9: 'memory_validity'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--c2btor', '--cbmc', dest='cbmc', default=str(ROOT / 'build/bin/c2btor'))
    parser.add_argument('--catbtor', default='catbtor')
    parser.add_argument('--btormc', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cases', default=','.join(map(str, range(1, 11))))
    parser.add_argument('--timeout', type=int, default=60)
    parser.add_argument('--bound', type=int, default=400)
    parser.add_argument('--target', choices=['32', '64'], default='64')
    parser.add_argument('--big-endian', action='store_true')
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--include-dir', action='append', default=[])
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    source = Path(__file__).with_name('object_memory.c')
    snapshot = args.output / 'cbmc.snapshot'
    shutil.copy2(args.cbmc, snapshot)
    args.cbmc = str(snapshot.resolve())
    manifest = {'target': args.target, 'big_endian': args.big_endian,
                'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                'cbmc_sha256': hashlib.sha256(snapshot.read_bytes()).hexdigest(),
                'timeout': args.timeout, 'bound': args.bound}
    (args.output / 'manifest.json').write_text(json.dumps(manifest, indent=2))

    def run(directory, stage, command):
        (directory / (stage + '.command.json')).write_text(json.dumps(command, indent=2))
        with (directory / (stage + '.log')).open('w') as stream:
            result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT, timeout=args.timeout)
        return result.returncode, (directory / (stage + '.log')).read_text()

    def check(task):
        case, mode, completion = task
        name = f'{case}-{mode}' + ('-completion' if completion else '')
        directory = args.output / name
        directory.mkdir()
        expected = 'source' if completion else NEGATIVE.get(case, 'bounded_no_violation')
        record = {'test': name, 'expected': expected}
        try:
            model, mapping = directory / 'model.btor2', directory / 'map.json'
            command = [args.cbmc, str(source), '-DCASE=' + str(case), *FLAGS,
                       '--' + args.target, '--memory', 'object', '--array', mode,
                       '--goto-btor2', '--goto-btor2-out', str(model),
                       '--goto-btor2-map-out', str(mapping), '--goto-btor2-heap-objects', '2']
            if case == 7:
                command += ['--memory-object-max-bytes', '1024']
            command += ['-I' + path for path in args.include_dir]
            if completion:
                command.append('-DCOMPLETE')
            if args.big_endian:
                command += ['--big-endian', '-DBIG_ENDIAN']
            code, log = run(directory, 'conversion', command)
            if code:
                record['actual'] = 'unsupported' if not model.exists() or not model.read_text().strip() else 'partial_model'
                assert case == 6 and 'integer' in log.lower(), log[-1500:]
            else:
                assert expected != 'unsupported', 'unsupported cast unexpectedly accepted'
                data = json.loads(mapping.read_text())['memory']
                assert data['memory_encoding'] == 'object'
                assert 'memory_state' not in data and 'packed_layout' not in data
                fields = [line.split() for line in model.read_text().splitlines() if line and not line.startswith(';')]
                sorts = {x[0]: x[2:] for x in fields if x[1] == 'sort'}
                nodes = {x[0]: x for x in fields}
                arrays = {key for key, value in sorts.items() if value[0] == 'array'}
                if mode == 'bv':
                    assert not arrays
                for x in fields:
                    if x[1] == 'init' and x[2] in arrays:
                        assert nodes[x[4]][2] == x[2], 'constant-array initializer remains'
                storage = data['object_storage']
                for obj in storage:
                    for name_, state in obj['states'].items():
                        if name_ != 'data':
                            assert nodes[str(state)][2] not in arrays
                if case == 1:
                    roots = {o['tag'] for o in data['objects'] if o['symbol'] in ('main::1::a', 'main::1::b')}
                    selected = [o for o in storage if o['tag'] in roots]
                    assert len(selected) == 2, data['objects']
                    assert all(o['capacity_bytes'] == 12 and o['element_bits'] == 32 and o['elements'] == 3 for o in selected)
                    assert len({o['states']['data'] for o in selected}) == 2
                code, log = run(directory, 'parser', [args.catbtor, str(model)])
                assert code == 0, log[-1500:]
                bound = max(args.bound, 1600) if case in (3, 10) else args.bound
                command = [args.btormc, '--bound-max=' + str(bound), '-v', str(model)]
                if expected == 'bounded_no_violation':
                    command.insert(1, '--checkall')
                code, log = run(directory, 'solver', command)
                assert code == 0, log[-1500:]
                match = re.search(r'^b(\d+)(?:\s|$)', log, re.M)
                if match:
                    bads = [int(x[0]) for x in fields if x[1] == 'bad']
                    kinds = {p['bad_node']: p['property_class'] for p in data['properties']}
                    record['actual'] = ('unexpected_violation' if expected == 'bounded_no_violation'
                                        else kinds.get(bads[int(match[1])], 'source'))
                else:
                    assert f'bound k = {bound}' in log, log[-1500:]
                    record['actual'] = 'bounded_no_violation'
                record['bound'] = bound
            record['passed'] = record['actual'] == expected
        except (subprocess.TimeoutExpired, AssertionError, ValueError) as error:
            record.update(actual='incomplete', passed=False, error=str(error))
        (directory / 'result.json').write_text(json.dumps(record, indent=2))
        print(record['test'], record['actual'], 'PASS' if record['passed'] else 'FAIL', flush=True)
        return record

    tasks = [(case, mode, complete) for case in map(int, args.cases.split(','))
             for mode in ('array', 'bv')
             for complete in ([False] if case in NEGATIVE else [False, True])]
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(check, tasks))
    (args.output / 'results.json').write_text(json.dumps(results, indent=2))
    print(f"{sum(x['passed'] for x in results)}/{len(results)} passed", flush=True)
    raise SystemExit(0 if all(x['passed'] for x in results) else 1)

if __name__ == '__main__':
    main()
