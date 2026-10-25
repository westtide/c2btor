#!/usr/bin/env python3
"""Check lifetime dispatch optimization with symbolic DAG comparison, without a solver.

Canonical references erase node numbering and duplicate pure terms, while input
and state ordinals remain distinct. Equality of all init/next/property/constraint
and output roots checks the optimization without relying on a solver timeout.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import subprocess

UNARY = {'not', 'neg', 'redand', 'redor', 'redxor', 'inc', 'dec'}
BINARY = {'add', 'sub', 'mul', 'sdiv', 'udiv', 'srem', 'urem', 'smod',
          'and', 'or', 'xor', 'nand', 'nor', 'xnor', 'eq', 'neq', 'slt',
          'ult', 'slte', 'ulte', 'sgt', 'ugt', 'sgte', 'ugte', 'sll',
          'srl', 'sra', 'rol', 'ror', 'concat', 'implies', 'iff', 'read',
          'saddo', 'uaddo', 'ssubo', 'usubo', 'smulo', 'umulo', 'sdivo'}
ROOTS = {'init', 'next', 'bad', 'constraint', 'output', 'fair', 'justice'}


def fingerprint(path, simplify_literals=False, pc_value=None):
    terms, roots = {}, collections.defaultdict(list)
    count = collections.Counter()
    widths, literals = {}, {}

    def digest(value):
        return hashlib.sha256(json.dumps(value, separators=(',', ':')).encode()).hexdigest()

    def ref(value):
        return digest(['inverted', terms[value[1:]]]) if value.startswith('-') else terms[value]

    for line in path.read_text().splitlines():
        line = line.split(';', 1)[0].strip()
        if not line:
            continue
        nid, op, *a = line.split()
        count[op] += 1
        if op == 'sort':
            value = [op, *a] if a[0] == 'bitvec' else [op, 'array', ref(a[1]), ref(a[2])]
            if a[0] == 'bitvec':
                widths[nid] = int(a[1])
        elif op in {'input', 'state'}:
            # Names may contain the old BTOR node ID (e.g. __memory_state_N).
            # Sort and declaration ordinal identify distinct symbolic values.
            value = [op, ref(a[0]), count[op]]
        elif op in {'zero', 'one', 'ones', 'const', 'constd', 'consth'}:
            value = [op, ref(a[0]), a[1:]]
        elif op in UNARY | {'slice', 'sext', 'uext'}:
            value = [op, ref(a[0]), ref(a[1]), a[2:]]
        elif op in BINARY | {'init', 'next'}:
            value = [op, ref(a[0]), ref(a[1]), ref(a[2]), a[3:]]
        elif op in {'ite', 'write'}:
            value = [op, ref(a[0]), ref(a[1]), ref(a[2]), ref(a[3]), a[4:]]
        elif op in {'bad', 'constraint', 'output', 'fair'}:
            value = [op, ref(a[0]), a[1:]]
        elif op == 'justice':
            n = int(a[0])
            value = [op, [ref(v) for v in a[1:n+1]], a[n+1:]]
        else:
            raise AssertionError('unhandled BTOR2 operation: ' + op)
        alias = None
        if simplify_literals:
            literal = None
            if op in {'zero', 'one', 'ones', 'const', 'constd', 'consth'}:
                width = widths[a[0]]
                literal = (0 if op == 'zero' else 1 if op == 'one' else
                           (1 << width) - 1 if op == 'ones' else
                           int(a[1], {'const': 2, 'constd': 10, 'consth': 16}[op]))
                literal %= 1 << width
            elif op in {'eq', 'neq'} and a[1] in literals and a[2] in literals:
                literal = int((literals[a[1]] == literals[a[2]]) == (op == 'eq'))
            elif op == 'and':
                for constant, other in [(a[1], a[2]), (a[2], a[1])]:
                    if constant in literals:
                        if literals[constant] == 0:
                            literal = 0
                        elif literals[constant] == (1 << widths[a[0]]) - 1:
                            alias = other
                        break
            elif op == 'ite' and a[1] in literals:
                alias = a[2] if literals[a[1]] != 0 else a[3]
            elif op == 'ite' and ref(a[2]) == ref(a[3]):
                alias = a[2]
            elif op == 'state' and a[1:] == ['pc'] and pc_value is not None:
                literal = pc_value
            if literal is not None:
                literals[nid] = literal
                value = ['literal', ref(a[0]), literal]
            elif alias is not None and alias in literals:
                literals[nid] = literals[alias]
        terms[nid] = ref(alias) if alias is not None else digest(value)
        if op in ROOTS | {'input', 'state'}:
            roots[op].append(terms[nid])
    return dict(roots), dict(count)


def pc_cases(path):
    """Partition all PC values by the converter's literal equality guards.

    This is syntactic constant substitution, with all source states and inputs
    left symbolic. One extra value represents the class matching no guard.
    Reject any unsupported use of PC rather than assuming a finite partition.
    """
    constants, cases, pc = {}, set(), None
    for line in path.read_text().splitlines():
        a = line.split(';', 1)[0].split()
        if not a:
            continue
        nid, op, *args = a
        if op == 'state' and args[1:] == ['pc']:
            pc = nid
        elif op in {'zero', 'one', 'constd'}:
            constants[nid] = 0 if op == 'zero' else 1 if op == 'one' else int(args[1])
        if pc and pc in args:
            if op in {'eq', 'neq'}:
                other = args[2] if args[1] == pc else args[1]
                assert other in constants, 'nonliteral PC comparison'
                cases.add(constants[other])
            elif op in {'init', 'next'}:
                assert args[1] == pc, 'PC used as a data operand'
            elif op == 'ite':
                assert args[3] == pc and args[2] in constants, 'nonliteral PC update'
            else:
                raise AssertionError('unsupported PC use: ' + line)
    assert pc is not None
    return cases | {max(cases, default=0) + 1}


CASES = {
    'byte-alias': '''int main(void) {
  signed char a[2] = {-1, -128}; unsigned char b[2] = {128, 255};
  _Bool choice;
  unsigned char *p = choice ? (unsigned char *)a : b;
  signed char *q = choice ? (signed char *)b : a;
  __CPROVER_assert(p[1] == (choice ? 128 : 255), "read");
  q[0] = -2;
  __CPROVER_assert(choice ? b[0] == 254 : a[0] == -2, "write");
}''',
    'object-dispatch': '''extern int __VERIFIER_nondet_int(void);
int main(void) {
  int a[3] = {1,2,3}, b[3] = {4,5,6};
  int choose = __VERIFIER_nondet_int(), i = __VERIFIER_nondet_int();
  __CPROVER_assume(i >= 0 && i < 3);
  int *p = choose ? &a[0] : &b[0]; p[i] = 77;
  __CPROVER_assert(p[i] == 77 && (choose ? b[i] == i+4 : a[i] == i+1), "frame");
}''',
    'fresh-inputs': '''extern unsigned __VERIFIER_nondet_uint(void);
int main(void) {
  unsigned a = __VERIFIER_nondet_uint(), b = __VERIFIER_nondet_uint();
  unsigned low_a = (unsigned char)a, low_b = (unsigned char)b;
  __CPROVER_assert(a != b || low_a == low_b, "same-low-bits");
  __CPROVER_assert(a == b, "independent-inputs");
}''',
}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--before', type=Path, required=True)
    p.add_argument('--after', type=Path, required=True)
    p.add_argument('--catbtor', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    results = []
    for case, source in CASES.items():
        program = args.output / (case + '.c')
        program.write_text(source + '\n')
        for target in ['32', '64']:
            for encoding in ['bv', 'array', 'mixed']:
                for lbe in [False, True]:
                    name = f'{case}-{target}-{encoding}-lbe{int(lbe)}'
                    item = args.output / name
                    item.mkdir()
                    signatures, sizes, models = [], [], []
                    for version, converter in [('before', args.before), ('after', args.after)]:
                        model = item / (version + '.btor2')
                        cmd = [str(converter.resolve()), str(program.resolve()),
                               '--goto-btor2', '--inline', '--' + target,
                               '--memory', 'object', '--array', encoding,
                               '--goto-btor2-out', str(model.resolve())]
                        if not lbe:
                            cmd.append('--goto-btor2-no-lbe')
                        (item / (version + '.command.json')).write_text(json.dumps(cmd, indent=2))
                        with (item / (version + '.conversion.log')).open('w') as log:
                            subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT,
                                           check=True, timeout=60)
                        with (item / (version + '.parser.log')).open('w') as log:
                            subprocess.run([str(args.catbtor.resolve()), str(model.resolve())],
                                           stdout=log, stderr=subprocess.STDOUT,
                                           check=True, timeout=30)
                        signature, counts = fingerprint(model, True)
                        signatures.append(signature)
                        sizes.append(sum(counts.values()))
                        models.append(model)
                    # Initial values and symbolic inputs/states must match even
                    # when PC is not specialized. Never merge fresh inputs.
                    for root in ['state', 'input', 'init']:
                        assert signatures[0].get(root) == signatures[1].get(root), (name, root)
                    equal = signatures[0] == signatures[1]
                    checked_classes = 0
                    if not equal:
                        cases = pc_cases(models[0]) | pc_cases(models[1])
                        equal = all(fingerprint(models[0], True, pc)[0] ==
                                    fingerprint(models[1], True, pc)[0]
                                    for pc in sorted(cases))
                        checked_classes = len(cases)
                    record = dict(test=name, equal_transition_and_property_roots=equal,
                                  pc_classes_checked=checked_classes,
                                  nodes_before=sizes[0], nodes_after=sizes[1],
                                  model_checking_run=False)
                    results.append(record)
                    (args.output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
                    print(name, equal, sizes, flush=True)
                    assert equal, name


if __name__ == '__main__':
    main()


