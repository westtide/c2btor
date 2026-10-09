#!/usr/bin/env python3
"""Check default/overridden BV capacity and distinguish model limits from OOB."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


SOURCE = '''
extern unsigned __VERIFIER_nondet_uint(void);
extern void *malloc(__CPROVER_size_t);
int main(void) {
  unsigned n = __VERIFIER_nondet_uint();
  __CPROVER_assume(n == SIZE);
#if HEAP
  unsigned char *a = malloc(n);
#elif FIXED
  unsigned char a[SIZE];
#else
  unsigned char a[n];
#endif
  a[n - 1 + OOB] = 7;
  __CPROVER_assert(0, "capacity-completion");
}
'''


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--c2btor', '--cbmc', dest='cbmc', default=str(root / 'build/bin/c2btor'))
    parser.add_argument('--catbtor', required=True)
    parser.add_argument('--btormc', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    source = args.output / 'capacity.c'
    source.write_text(SOURCE)
    results = []

    def run(directory, stage, command):
        (directory / (stage + '.command.json')).write_text(json.dumps(command))
        result = subprocess.run(command, capture_output=True, text=True, timeout=45)
        log = result.stdout + result.stderr
        (directory / (stage + '.log')).write_text(log)
        assert result.returncode == 0, log[-2000:]
        return log

    # Each valid access must reach an intentional completion assertion. Faults
    # must instead reach the corresponding internal property, not completion.
    for target in (32, 64):
        for heap in (0, 1):
            for label, size, capacity, oob, fixed, expected in [
                ('default', 1024, None, 0, 0, 'source'),
                ('explicit-default', 1024, 1024, 0, 0, 'source'),
                ('automatic-large', 5000, None, 0, 0, 'source'),
                ('override', 16, 16, 0, 0, 'source'),
                ('override-excess', 17, 16, 0, 0, 'model_limit'),
                ('actual-bounds', 7, None, 1, 0, 'memory_validity'),
                *([] if heap else [('fixed-exact', 1025, 16, 0, 1, 'source')]),
            ]:
                name = f'{target}-{heap}-{label}'
                directory = args.output / name
                directory.mkdir()
                model, mapping = directory / 'model.btor2', directory / 'map.json'
                record = {'name': name, 'expected': expected}
                try:
                    command = [args.cbmc, str(source), '--inline', '--no-standard-checks',
                               '--no-pointer-check', '--no-bounds-check',
                               '--no-built-in-assertions', '--' + str(target),
                               '--array', 'bv', '--goto-btor2', '--goto-btor2-heap-objects', '1',
                               '--goto-btor2-out', str(model), '--goto-btor2-map-out', str(mapping),
                               f'-DSIZE={size}', f'-DHEAP={heap}', f'-DOOB={oob}', f'-DFIXED={fixed}']
                    if capacity is not None:
                        command += ['--array-bv-max-object-bytes', str(capacity)]
                    log = run(directory, 'conversion', command)
                    effective = capacity
                    assert ('capacity: automatic (GotoIR bounds)' if effective is None else f'capacity: {effective} bytes per object') in log
                    content = model.read_text()
                    assert not re.search(r'^\d+ (sort array|read|write) ', content, re.M)
                    data = json.loads(mapping.read_text())['memory']
                    assert data['max_object_bytes'] == effective
                    if label == 'explicit-default':
                        original = args.output / f'{target}-{heap}-default' / 'model.btor2'
                        assert model.read_bytes() == original.read_bytes()
                    run(directory, 'parser', [args.catbtor, str(model)])
                    log = run(directory, 'solver', [args.btormc, '--bound-max=150', str(model)])
                    match = re.search(r'^b(\d+)(?:\s|$)', log, re.M)
                    assert match, 'No reachable completion/fault within 150 steps'
                    bads = [int(line.split()[0]) for line in content.splitlines()
                            if re.match(r'^\d+ bad ', line)]
                    categories = {p['bad_node']: p['property_class'] for p in data['properties']}
                    actual = categories.get(bads[int(match[1])], 'source')
                    record.update(actual=actual, passed=actual == expected)
                except (AssertionError, subprocess.TimeoutExpired, ValueError) as error:
                    record.update(passed=False, error=str(error))
                results.append(record)
                print(name, 'PASS' if record['passed'] else 'FAIL', flush=True)
    report = {'cbmc_sha256': hashlib.sha256(Path(args.cbmc).read_bytes()).hexdigest(),
              'results': results}
    (args.output / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f"{sum(r['passed'] for r in results)}/{len(results)} checks passed")
    raise SystemExit(0 if all(r['passed'] for r in results) else 1)


if __name__ == '__main__':
    main()
