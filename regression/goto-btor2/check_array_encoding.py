#!/usr/bin/env python3
"""Compare native-array and pure-BV storage on the same C semantic rules.

BMC absence is reported as bounded_no_violation. Every positive case also has
an independently reachable completion property to rule out vacuous success.
Artifacts include exact commands, tool hashes, model sorts and bad classes.
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
NEGATIVE = {10: 'memory_validity', 11: 'memory_validity',
            14: 'memory_validity', 15: 'model_limit'}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--c2btor', '--cbmc', dest='cbmc', default=str(ROOT / 'build/bin/c2btor'))
    parser.add_argument('--catbtor', default='catbtor')
    parser.add_argument('--btormc', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cases', default=','.join(map(str, range(1, 17))))
    parser.add_argument('--timeout', type=int, default=45)
    parser.add_argument('--bound', type=int, default=250)
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--include-dir', action='append', default=[])
    parser.add_argument('--target', choices=['32', '64'], default='64')
    parser.add_argument('--big-endian', action='store_true')
    parser.add_argument('--memory', choices=['global', 'object'], default='global')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    source = Path(__file__).with_name('array_encoding.c')
    snapshot = args.output / 'cbmc.snapshot'
    shutil.copy2(args.cbmc, snapshot)
    args.cbmc = str(snapshot.resolve())
    manifest = {'source_sha256': digest(source),
                'tools': {name: {'path': getattr(args, name), 'sha256': digest(getattr(args, name))}
                          for name in ['cbmc', 'catbtor', 'btormc']},
                'target': args.target, 'big_endian': args.big_endian, 'memory': args.memory,
                'bound': args.bound, 'timeout_seconds': args.timeout}
    (args.output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')

    def execute(directory, stage, command):
        (directory / (stage + '.command.json')).write_text(json.dumps(command, indent=2) + '\n')
        with (directory / (stage + '.log')).open('w') as stream:
            code = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT,
                                  timeout=args.timeout).returncode
        return code, (directory / (stage + '.log')).read_text()

    def check(task):
        case, mode, completion, bug = task
        name = f'{case}-{mode}' + ('-completion' if completion else '') + ('-bug' if bug else '')
        directory = args.output / name
        directory.mkdir()
        expected = NEGATIVE.get(case, 'bounded_no_violation')
        if case == 11 and args.target == '32':
            expected = 'model_limit'
        if (mode == 'bv' or args.memory == 'object') and case in (12, 13):
            expected = 'model_limit'
        if completion or bug:
            expected = 'source'
        record = {'case': case, 'mode': mode, 'test': name, 'expected': expected}
        try:
            model, mapping = directory / 'model.btor2', directory / 'map.json'
            command = [args.cbmc, str(source), '-DCASE=' + str(case), *FLAGS,
                       '--' + args.target, '--array', mode, '--memory', args.memory, '--goto-btor2',
                       '--goto-btor2-out', str(model), '--goto-btor2-map-out', str(mapping)]
            if args.memory == 'object':
                command += ['--memory-object-max-bytes', '16']
            if mode == 'bv':
                command += ['--array-bv-max-object-bytes', '16']
            command += ['--goto-btor2-heap-objects', '2']
            command += ['-I' + path for path in args.include_dir]
            if completion:
                command += ['-DCOMPLETE']
            if bug:
                command += ['-DBUG']
            if args.big_endian:
                command += ['--big-endian', '-DBIG_ENDIAN']
            code, log = execute(directory, 'conversion', command)
            assert code == 0, log[-1500:]
            content = model.read_text()
            record['array_sorts'] = len(re.findall(r'^\d+ sort array ', content, re.M))
            record['model_bytes'] = model.stat().st_size
            record['bv_state_bits'] = 0
            sorts = {}
            for line in content.splitlines():
                fields = line.split()
                if len(fields) >= 4 and fields[1:3] == ['sort', 'bitvec']:
                    sorts[fields[0]] = int(fields[3])
                elif len(fields) >= 3 and fields[1] == 'state':
                    record['bv_state_bits'] += sorts.get(fields[2], 0)
            if mode == 'bv':
                assert record['array_sorts'] == 0
                assert not re.search(r'^\d+ (read|write) ', content, re.M)
            else:
                assert record['array_sorts'] > 0
            code, log = execute(directory, 'parser', [args.catbtor, str(model)])
            assert code == 0, log[-1500:]
            data = json.loads(mapping.read_text())
            assert data['memory']['array_encoding'] == mode
            assert data['memory']['memory_encoding'] == args.memory
            bound = max(args.bound, 600) if case == 8 else args.bound
            command = [args.btormc, '--bound-max=' + str(bound), '-v', str(model)]
            if expected == 'bounded_no_violation':
                command.insert(1, '--checkall')
            code, log = execute(directory, 'solver', command)
            assert code == 0, log[-1500:]
            match = re.search(r'^b(\d+)(?:\s|$)', log, re.M)
            if match:
                bads = [int(line.split()[0]) for line in content.splitlines()
                        if re.match(r'^\d+ bad ', line)]
                categories = {p['bad_node']: p['property_class']
                              for p in data['memory']['properties']}
                record['actual'] = ('unexpected_violation' if expected == 'bounded_no_violation'
                                    else categories.get(bads[int(match[1])], 'source'))
            else:
                assert f'bound k = {bound}' in log, log[-1500:]
                record['actual'] = 'bounded_no_violation'
            record['passed'] = expected == record['actual']
        except (subprocess.TimeoutExpired, AssertionError, ValueError) as error:
            record.update(passed=False, actual='incomplete', error=str(error))
        (directory / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
        print(f"{name}: {record['actual']} {'PASS' if record['passed'] else 'FAIL'}", flush=True)
        return record

    tasks = []
    for case in map(int, args.cases.split(',')):
        for mode in ['array', 'bv']:
            tasks.append((case, mode, False, False))
            if case not in NEGATIVE and not (case in (12, 13) and (mode == 'bv' or args.memory == 'object')):
                tasks.append((case, mode, True, False))
            if case == 1:
                tasks.append((case, mode, False, True))
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(check, tasks))
    (args.output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f"{sum(r['passed'] for r in results)}/{len(results)} checks passed", flush=True)
    raise SystemExit(0 if all(r['passed'] for r in results) else 1)


if __name__ == '__main__':
    main()
