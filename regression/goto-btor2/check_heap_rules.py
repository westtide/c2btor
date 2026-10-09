#!/usr/bin/env python3
"""Bounded semantic-rule regressions. No bounded absence is called SAFE.

Provide --btormc or --ric3 and a fresh --output directory. Every supported model is parsed;
positive cases also have a reachable completion control to reject vacuity.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import shutil
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from c2btor_solver import ric3_command

ROOT = Path(__file__).resolve().parents[2]
FLAGS = ['--inline', '--no-standard-checks', '--no-pointer-check',
         '--no-bounds-check', '--no-built-in-assertions']
EXPECTED = {4: 'memory_validity', 5: 'memory_validity', 6: 'memory_validity',
            17: 'model_limit', 18: 'model_limit', 19: 'memory_validity',
            20: 'source', 21: 'unsupported', 25: 'memory_validity'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    backend = parser.add_mutually_exclusive_group(required=True)
    backend.add_argument('--btormc')
    backend.add_argument('--ric3', help='IC3 for UNSAT controls; BMC for reachable faults/completion')
    parser.add_argument('--safety-engine', choices=['ic3','kind','wl-kind'], default='ic3')
    parser.add_argument('--reachability-engine', choices=['bmc','wl-bmc'], default='bmc')
    parser.add_argument('--btorsim', default='btorsim')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cases', default=','.join(str(i) for i in range(1, 26)))
    parser.add_argument('--bound', type=int, default=1200)
    parser.add_argument('--timeout', type=int, default=30)
    parser.add_argument('--c2btor', '--cbmc', dest='cbmc', default=str(ROOT / 'build/bin/c2btor'))
    parser.add_argument('--catbtor', default='catbtor')
    parser.add_argument('--include-dir', action='append', default=[])
    parser.add_argument('--array', choices=['array', 'bv'], default='bv')
    parser.add_argument('--array-bv-max-object-bytes', type=int)
    parser.add_argument('--heap-objects', type=int)
    parser.add_argument('--target', choices=['32', '64'])
    parser.add_argument('--memory', choices=['global', 'object'], default='object')
    parser.add_argument('--memory-object-max-bytes', type=int)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    snapshot = args.output / 'cbmc.snapshot'
    shutil.copy2(args.cbmc, snapshot)
    args.cbmc = str(snapshot.resolve())
    results = []

    def run(directory, stage, command):
        (directory / (stage + '.command.json')).write_text(json.dumps(command, indent=2))
        with (directory / (stage + '.log')).open('w') as output:
            result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT,
                                    timeout=args.timeout)
        return result.returncode, (directory / (stage + '.log')).read_text()

    for case in map(int, args.cases.split(',')):
        expected = EXPECTED.get(case, 'bounded_no_violation')
        for completion in ([False, True] if expected == 'bounded_no_violation' else [False]):
            name = str(case) + ('-completion' if completion else '')
            directory = args.output / name
            directory.mkdir()
            model, mapping = directory / 'model.btor2', directory / 'map.json'
            command = [args.cbmc, str(Path(__file__).with_name('heap_rules.c')),
                       '-DCASE=' + str(case), *FLAGS, '--goto-btor2',
                       '--goto-btor2-out', str(model), '--goto-btor2-map-out', str(mapping)]
            command += ['-I' + path for path in args.include_dir]
            if completion:
                command.append('-DCOMPLETE')
            command += ['--array', args.array, '--memory', args.memory]
            if args.target:
                command += ['--' + args.target]
            if args.memory_object_max_bytes is not None:
                command += ['--memory-object-max-bytes', str(args.memory_object_max_bytes)]
            if args.array_bv_max_object_bytes is not None:
                command += ['--array-bv-max-object-bytes', str(args.array_bv_max_object_bytes)]
            if case == 17 or args.heap_objects is not None:
                command += ['--goto-btor2-heap-objects', str(1 if case == 17 else args.heap_objects)]
            if case == 16:
                command += ['--malloc-may-fail', '--malloc-fail-null']
            bound = max(args.bound, 1000) if case == 13 else args.bound
            record = {'case': name, 'expected': 'source' if completion else expected,
                      'bound': bound}
            if args.ric3 and expected == 'bounded_no_violation' and not completion:
                record['expected'] = 'model_unsat'
            try:
                code, log = run(directory, 'conversion', command)
                if code:
                    record['actual'] = 'unsupported' if not model.exists() or not model.read_text() else 'failed_nonempty_model'
                else:
                    code, log = run(directory, 'parser', [args.catbtor, str(model)])
                    assert code == 0, log[-1000:]
                    combined = expected == 'bounded_no_violation' and not completion
                    solver = [args.btormc, '--bound-max=' + str(bound),
                              *(['--checkall'] if combined else []), '-v', str(model)]
                    if args.ric3:
                        engine = args.safety_engine if combined else args.reachability_engine
                        solver = ric3_command(args.ric3, model, engine, args.timeout, bound)
                        if engine in {'ic3','kind','bmc'}:
                            solver += ['--frts', 'false', '--scorr', 'false']
                    code, log = run(directory, 'solver', solver)
                    assert code == 0, log[-1000:]
                    data = json.loads(mapping.read_text())
                    auxiliary = {p['bad_node']: p['property_class']
                                 for p in data['memory']['properties']}
                    bads = [int(line.split()[0]) for line in model.read_text().splitlines()
                            if re.match(r'^\d+ bad ', line)]
                    match = re.search(r'^b(\d+)(?:\s|$)', log, re.M)
                    if args.ric3 and match:
                        witness = directory / 'witness.txt'
                        witness.write_text(log[log.index('sat\n'):])
                        code, replay = run(directory, 'replay', [args.btorsim, '-c', str(model), str(witness)])
                        assert code == 0, replay[-1000:]
                    record['actual'] = (('unexpected_violation' if combined else
                        auxiliary.get(bads[int(match[1])], 'source')) if match else 'bounded_no_violation')
                    if not match:
                        if args.ric3:
                            assert combined and re.search(r'^UNSAT$',log,re.M), log[-1000:]
                            record['actual'] = 'model_unsat'
                        else:
                            assert f'bound k = {bound}' in log, log[-1000:]
                record['passed'] = record['actual'] == record['expected']
            except (subprocess.TimeoutExpired, AssertionError) as error:
                record.update(actual='incomplete', passed=False, error=str(error))
            results.append(record)
            (args.output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
            print(name, record['actual'], 'OK' if record['passed'] else 'FAIL', flush=True)
    if not all(result['passed'] for result in results):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
