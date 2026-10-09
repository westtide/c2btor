#!/usr/bin/env python3
"""Check inferred storage capacities and replay concrete C executions.

The chosen input traces check endpoints, alias writes and machine arithmetic.
Replay success is a regression observation, not a proof over all C inputs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
FLAGS = ['--inline', '--no-standard-checks', '--no-pointer-check',
         '--no-bounds-check', '--no-built-in-assertions']
PRELUDE = '''extern unsigned __VERIFIER_nondet_uint(void);
extern unsigned short __VERIFIER_nondet_ushort(void);
extern void *__VERIFIER_nondet_pointer(void);
extern void *malloc(__CPROVER_size_t);
extern void *calloc(__CPROVER_size_t, __CPROVER_size_t);
extern void *realloc(void *, __CPROVER_size_t);
'''
CHECK = 'a[0]=3; a[n-1]=7; __CPROVER_assert(a[0]==3 && a[n-1]==7,"values");'
CASES = {
    'large-vla': ('unsigned n=10000; int a[n]; ' + CHECK, {'a': 40000}, [0]),
    'fixed-exact': ('unsigned n=10000; int a[10000]; ' + CHECK, {'a': 40000}, [0]),
    'independent': ('unsigned n=10000,m=500; int a[n]; unsigned char b[m]; '
                    'b[m-1]=9; ' + CHECK + '__CPROVER_assert(b[m-1]==9,"other");',
                    {'a': 40000, 'b': 500}, [0]),
    'assumed-range': ('unsigned n=__VERIFIER_nondet_uint(); '
                     '__CPROVER_assume(n>=2 && n<=10000); int a[n]; ' + CHECK,
                     {'a': 40000}, [2, 10000]),
    'variable-bound': ('unsigned maximum=10000; unsigned n=__VERIFIER_nondet_uint(); '
                       '__CPROVER_assume(n>=2 && n<=maximum); int a[n]; ' + CHECK,
                       {'a': 40000}, [2, 10000]),
    'branch-join': ('unsigned n; if(__VERIFIER_nondet_uint()&1) n=10000; '
                    'else n=20000; int a[n]; ' + CHECK, {'a': 80000}, [0, 1]),
    'masked-range': ('unsigned n=10000+(__VERIFIER_nondet_uint()&3); int a[n]; '
                     + CHECK, {'a': 40012}, [0, 3]),
    'bool-bound': ('unsigned raw=__VERIFIER_nondet_uint(); _Bool selected=(_Bool)raw; '
                   '_Bool signed_selected=(_Bool)(int)raw; '
                   '__CPROVER_assert((unsigned)selected==(raw!=0) && '
                   'signed_selected==selected,"boolean"); '
                   'unsigned n=2+selected; int a[n]; ' + CHECK,
                   {'a': 12}, [0, 2, 256, 4294967295]),
    'narrowing': ('unsigned short n=(unsigned short)__VERIFIER_nondet_uint(); '
                 '__CPROVER_assume(n>=2); int a[n]; ' + CHECK,
                 {'a': 262140}, [65535, 131071]),
    'unsigned-wrap': ('unsigned short n=__VERIFIER_nondet_ushort(); '
                     'n=(unsigned short)(n-1); int a[n]; ' + CHECK,
                     {'a': 262140}, [0]),
    'alias-write': ('unsigned short n=4; unsigned short *p=&n; *p=5000; '
                    'int a[n]; ' + CHECK, {'a': 262140}, [0]),
    'loop-widening': ('unsigned short n=0; while(n<3) ++n; int a[n]; '
                      + CHECK, {'a': 262140}, [0]),
    'large-malloc': ('unsigned n=5000; unsigned char *a=malloc(n); ' + CHECK,
                     {'heap': 5000}, [0]),
    'heap-join': ('unsigned n; if(__VERIFIER_nondet_uint()&1) n=5000; '
                  'else n=9000; unsigned char *a=malloc(n); ' + CHECK,
                  {'heap': 9000}, [0, 1]),
    'calloc-large': ('unsigned n=2000; int *a=calloc(n,sizeof(int)); '
                     '__CPROVER_assert(a[0]==0 && a[n-1]==0,"zero"); ' + CHECK,
                     {'heap': 8000}, [0]),
    'calloc-range': ('unsigned n=2000+(__VERIFIER_nondet_uint()&3); '
                     'int *a=calloc(n,sizeof(int)); ' + CHECK,
                     {'heap': 8012}, [0, 3]),
    'captured-size': ('unsigned n=10; unsigned char *p=malloc(n); n=2; '
                      'unsigned m=__CPROVER_OBJECT_SIZE(p); unsigned char a[m]; '
                      'a[m-1]=7; __CPROVER_assert(m==10 && a[m-1]==7,"latched");',
                      {'a': 10, 'heap': 10}, [0]),
    'vla-captured': ('unsigned n=10000; int original[n]; n=2; int *p=original; '
                     'unsigned m=__CPROVER_OBJECT_SIZE(p); unsigned char a[m]; '
                     'a[m-1]=7; __CPROVER_assert(m==40000 && a[m-1]==7,"vla-size");',
                     {'original': 40000, 'a': 40000}, [0]),
    'calloc-overflow': ('void *p=calloc((__CPROVER_size_t)-1,2); '
                        '__CPROVER_assert(p==0,"overflow-null");', {}, [0]),
    'member-bound': ('struct { unsigned maximum; } limits={10000}; '
                     'unsigned n=__VERIFIER_nondet_uint(); '
                     '__CPROVER_assume(n>=2 && n<=limits.maximum); int a[n]; ' + CHECK,
                     {'a': 40000}, [2, 10000]),
    'aggregate-pointer-store': ('struct { unsigned short maximum; } limits={4}; '
                                'unsigned short *p=__VERIFIER_nondet_pointer(); *p=5000; '
                                'unsigned n=limits.maximum; int a[n]; ' + CHECK,
                                {'a': 262140}, ['limits-pointer']),
    'realloc-prefix': ('unsigned n=2; int *p=malloc(n*sizeof(int)); p[0]=3; p[1]=7; '
                       'int *a=realloc(p,3*sizeof(int)); '
                       '__CPROVER_assert(a[0]==3 && a[1]==7,"prefix");',
                       {'heap': 12}, [0]),
    'explicit-excess': ('unsigned n=17; unsigned char a[n]; ' + CHECK,
                        {'a': 16}, [0]),
    'actual-bounds': ('unsigned n=5000; unsigned char a[n]; a[n]=7;',
                      {'a': 5000}, [0]),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--c2btor', '--cbmc', dest='cbmc', type=Path, default=ROOT / 'build/bin/c2btor')
    parser.add_argument('--catbtor', type=Path, required=True)
    parser.add_argument('--btorsim', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cases', help='comma-separated case names; default: all')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    snapshot = args.output / 'cbmc.snapshot'
    shutil.copy2(args.cbmc, snapshot)
    args.cbmc = snapshot.resolve()
    results = []

    def run(directory, stage, command):
        command = [str(x) for x in command]
        (directory / (stage + '.command.json')).write_text(json.dumps(command, indent=2))
        with (directory / (stage + '.log')).open('w') as stream:
            result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT, timeout=45)
        assert result.returncode == 0, (directory / (stage + '.log')).read_text()[-1200:]
        return (directory / (stage + '.log')).read_text()

    cases = CASES if not args.cases else {name: CASES[name] for name in args.cases.split(',')}
    for target in (32, 64):
        for name, (body, capacities, inputs) in cases.items():
            # Keep all four representation combinations exercised on the
            # large VLA; other tests omit both switches to check the default.
            modes = [(None, None)]
            if name == 'large-vla':
                modes += [('object', 'array'), ('global', 'bv'), ('global', 'array')]
            for memory, array in modes:
                label = f'{target}-{name}-{memory or "default"}-{array or "default"}'
                directory = args.output / label
                directory.mkdir()
                record = {'case': label, 'expected_capacities': capacities}
                try:
                    source = directory / 'source.c'
                    source.write_text(PRELUDE + 'int main(void) {' + body +
                                      '__CPROVER_assert(0,"completion");}\n')
                    model, mapping = directory / 'model.btor2', directory / 'map.json'
                    command = [args.cbmc.resolve(), source, *FLAGS, '--' + str(target),
                               '--goto-btor2', '--goto-btor2-out', model,
                               '--goto-btor2-map-out', mapping, '--goto-btor2-heap-objects',
                               '2' if name == 'realloc-prefix' else '1']
                    if memory:
                        command += ['--memory', memory, '--array', array]
                    if name in ('fixed-exact', 'explicit-excess'):
                        command += ['--memory-object-max-bytes', '16']
                    run(directory, 'conversion', command)
                    data = json.loads(mapping.read_text())['memory']
                    assert data['memory_encoding'] == (memory or 'object')
                    assert data['array_encoding'] == (array or 'bv')
                    bounded = data['memory_encoding'] == 'object' or data['array_encoding'] == 'bv'
                    if bounded:
                        assert data['max_object_bytes'] == (16 if name in ('fixed-exact', 'explicit-excess') else None)
                        roots = {o['symbol'].split('::')[-1]: o['tag'] for o in data['objects']}
                        layout = data.get('object_storage', data.get('packed_layout'))
                        for symbol, capacity in capacities.items():
                            tag = data['first_heap_tag'] if symbol == 'heap' else roots[symbol]
                            selected = [o for o in layout if o['tag'] == tag]
                            assert len(selected) == 1, (symbol, tag, layout)
                            actual = selected[0]['capacity_bytes']
                            assert actual == capacity, (symbol, capacity, actual)
                        if name == 'calloc-overflow':
                            assert data['allocation_capacity_bytes'] == 0
                        if name == 'realloc-prefix':
                            assert all(o['capacity_bytes'] <= 12 for o in layout)
                    fields = [line.split() for line in model.read_text().splitlines()
                              if line and line[0].isdigit()]
                    if data['array_encoding'] == 'bv':
                        assert not re.search(r'^\d+ (sort array|read|write) ', model.read_text(), re.M)
                    run(directory, 'parser', [args.catbtor.resolve(), model])
                    bads = [int(x[0]) for x in fields if x[1] == 'bad']
                    auxiliary = {p['bad_node']: p['property_class'] for p in data['properties']}
                    category = {'explicit-excess': 'model_limit', 'actual-bounds': 'memory_validity'}.get(name, 'source')
                    if category == 'source':
                        properties = json.loads(mapping.read_text())['source_properties']
                        claimed = bads.index(properties[-1]['bad_node'])
                    else:
                        claimed = next(i for i, node in enumerate(bads) if auxiliary.get(node) == category)
                    sorts = {x[0]: int(x[3]) for x in fields if x[1:3] == ['sort', 'bitvec']}
                    input_nodes = [x for x in fields if x[1] == 'input']
                    for value in inputs:
                        chosen = roots['limits'] << data['offset_width'] if value == 'limits-pointer' else value
                        witness = directory / f'input-{value}.witness'
                        # Standard BTOR2 input trace. Initialized states come
                        # from the model; arbitrary data starts at simulator defaults.
                        witness.write_text('sat\nb' + str(claimed) + '\n#0\n' +
                            ''.join('@' + str(step) + '\n' + ''.join(
                                f'{i} {format((chosen & ((1 << sorts[x[2]]) - 1)) if x[-1].startswith("nondet_") else 0, "0" + str(sorts[x[2]]) + "b")}\n'
                                for i, x in enumerate(input_nodes)) for step in range(600 if name == "realloc-prefix" else 160)) + '.\n')
                        log = run(directory, f'replay-{value}', [args.btorsim.resolve(), '-c', '-v', model, witness])
                        reached = {int(i) for i in re.findall(r'b(\d+)@\d+', log)}
                        assert claimed in reached
                        assert {auxiliary.get(bads[i], 'source') for i in reached} == {category}, reached
                        if category == 'source':
                            assert reached == {claimed}, 'numerical assertion failed before completion'
                    record.update(passed=True, classification=category, replays=len(inputs))
                except (AssertionError, subprocess.TimeoutExpired, ValueError) as error:
                    record.update(passed=False, error=str(error))
                results.append(record)
                print(label, 'PASS' if record['passed'] else 'FAIL', flush=True)
                (args.output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    report = {'cbmc_sha256': hashlib.sha256(args.cbmc.read_bytes()).hexdigest(),
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'results': results}
    (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'{sum(r["passed"] for r in results)}/{len(results)} cases passed')
    raise SystemExit(0 if all(r['passed'] for r in results) else 1)


if __name__ == '__main__':
    main()
