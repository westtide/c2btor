#!/usr/bin/env python3
"""Numerical IEEE circuit and C鈫払TOR2 regressions; retain all evidence."""
import argparse
import csv
import hashlib
import json
import platform
import re
import subprocess
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from c2btor_solver import ric3_command


# Each program evaluates an operation on local runtime state. The final false
# assertion is a completion marker: reaching it proves earlier checks were
# executed and the path was not silently frozen by an assume/model boundary.
INTEGRATION = {
    'f_add_equal': 'float a=1.5f; float b=a+a; __CPROVER_assert(b==3.0f,"value");',
    'f_sub': 'float a=1.5f, b=1.0f; float c=a-b; __CPROVER_assert(c==0.5f,"value");',
    'd_add_equal': 'double a=1.5; double b=a+a; __CPROVER_assert(b==3.0,"value");',
    'f_div': 'float a=1.5f, b=3.0f; float c=a/b; __CPROVER_assert(c==0.5f,"value");',
    'd_div': 'double a=3.0, b=1.5; double c=a/b; __CPROVER_assert(c==2.0,"value");',
    'f_subnormal_mul': 'float a=0x1p-126f, b=0.5f; float c=a*b; __CPROVER_assert(c==0x1p-127f,"value");',
    'f_subnormal_div_tie': 'float a=0x1.8p-148f, b=2.0f; float c=a/b; __CPROVER_assert(c==0x1p-148f,"value");',
    'd_subnormal_div_tie': 'double a=0x1.8p-1073, b=2.0; double c=a/b; __CPROVER_assert(c==0x1p-1073,"value");',
    'f2d': 'float a=1.5f; double b=a; __CPROVER_assert(b==1.5,"value");',
    'f2d_subnormal': 'float a=0x1p-149f; double b=a; __CPROVER_assert(b==0x1p-149,"value");',
    'd2f': 'double a=1.5; float b=a; __CPROVER_assert(b==1.5f,"value");',
    'd2f_subnormal': 'double a=0x1p-149; float b=a; __CPROVER_assert(b==0x1p-149f,"value");',
    'd2f_overflow': 'double a=0x1p128; float b=a; __CPROVER_assert(__CPROVER_isinff(b),"value");',
    'int_rne': 'int a=16777217; float b=a; __CPROVER_assert(b==16777216.0f,"value");',
    'uint_rne_carry': 'unsigned a=0xffffffffu; float b=a; __CPROVER_assert(b==0x1p32f,"value");',
    'i8_double': 'signed char a=-128; double b=a; __CPROVER_assert(b==-128.0,"value");',
    'u64_double': 'unsigned long long a=18446744073709551615ULL; double b=a; __CPROVER_assert(b==0x1p64,"value");',
    'f_i64': 'float a=0x1p40f; long long b=a; __CPROVER_assert(b==1099511627776LL,"value");',
    'd_i32': 'double a=3.9; int b=a; __CPROVER_assert(b==3,"value");',
    'd_i8_min_fraction': 'double a=-128.75; signed char b=a; __CPROVER_assert(b==-128,"value");',
    'f_u32_negative_fraction': 'float a=-0.75f; unsigned b=a; __CPROVER_assert(b==0,"value");',
    'd_i64_min': 'double a=-0x1p63; long long b=a; __CPROVER_assert(b==(-9223372036854775807LL-1),"value");',
    'signed_zero_relation': 'float a=-0.0f, b=0.0f; __CPROVER_assert(a==b && !(a<b) && a>=b,"value");',
    'negative_zero_sum': 'float a=-0.0f; float b=a+a, c=1.0f/b; __CPROVER_assert(c<0.0f && __CPROVER_isinff(c),"value");',
    'nan_inf_priority': 'float z=0.0f; float n=z/z, i=1.0f/z, r=n+i; __CPROVER_assert(r!=r,"value");',
    'inf_minus_inf': 'double z=0.0; double i=1.0/z, r=i-i; __CPROVER_assert(r!=r,"value");',
    'inf_times_zero': 'float z=0.0f; float i=1.0f/z, r=i*z; __CPROVER_assert(r!=r,"value");',
    'restored_rounding': '__CPROVER_rounding_mode=1; __CPROVER_rounding_mode=0; float a=1.5f, b=a+a; __CPROVER_assert(b==3.0f,"value");',
}
INTEGRATION.update({
    'round_down_cancel': '__CPROVER_rounding_mode=1; float a=1.0f, b=a-a, c=1.0f/b; __CPROVER_assert(__CPROVER_isinff(c) && c<0,"minus-zero");',
    'round_up': '__CPROVER_rounding_mode=2; float a=1.0f,b=0x1p-25f,c=a+b; __CPROVER_assert(c==0x1.000002p0f,"up");',
    'round_zero_overflow': '__CPROVER_rounding_mode=3; float a=0x1.fffffep127f,b=2.0f,c=a*b; __CPROVER_assert(c==a,"finite-overflow");',
    'round_away_tie': '__CPROVER_rounding_mode=4; float a=1.0f,b=0x1p-24f,c=a+b; __CPROVER_assert(c==0x1.000002p0f,"away");',
    'round_int_up': '__CPROVER_rounding_mode=2; unsigned a=16777217; float b=a; __CPROVER_assert(b==16777218.0f,"int-up");',
    'round_cast_down': '__CPROVER_rounding_mode=1; double a=1.0+0x1p-24; float b=a; __CPROVER_assert(b==1.0f,"cast-down");',
    'sqrt_exact': 'extern double sqrt(double); double a=4.0,b=sqrt(a); __CPROVER_assert(b==2.0,"sqrt");',
    'sqrt_subnormal': 'extern float sqrtf(float); float a=0x1p-148f,b=sqrtf(a); __CPROVER_assert(b==0x1p-74f,"sqrt-subnormal");',
    'sqrt_negative_zero': 'extern double sqrt(double); double a=-0.0,b=sqrt(a),c=1.0/b; __CPROVER_assert(__CPROVER_isinfd(c) && c<0,"sqrt-zero");',
    'sqrt_negative': 'extern double sqrt(double); double a=-4.0,b=sqrt(a); __CPROVER_assert(b!=b,"sqrt-nan");',
    'fma_fused': 'extern float fmaf(float,float,float); float a=0x1.000002p0f,b=0x1.fffffcp-1f,c=-1.0f,r=fmaf(a,b,c); __CPROVER_assert(r==-0x1p-46f,"single-rounding");',
    'fma_overflow_cancel': 'extern double fma(double,double,double); double a=0x1.fffffffffffffp1023,b=2.0,c=-a,r=fma(a,b,c); __CPROVER_assert(r==a,"unrounded-product");',
    'remainder_tie_even': 'extern double remainder(double,double); double a=7.0,b=2.0,c=remainder(a,b); __CPROVER_assert(c==-1.0,"tie-even");',
    'remainder_small': 'extern float remainderf(float,float); float a=0.75f,b=1.0f,c=remainderf(a,b); __CPROVER_assert(c==-0.25f,"small");',
    'remainder_extreme': 'extern double remainder(double,double); double a=0x1p1023,b=0x1.8p-1072,c=remainder(a,b); __CPROVER_assert(c==0x1p-1073,"extreme");',
    'fmod_sign': 'extern double fmod(double,double); double a=-7.0,b=2.0,c=fmod(a,b); __CPROVER_assert(c==-1.0,"truncation");',
    'fenv_up': 'fesetround(FE_UPWARD); float a=1.0f,b=0x1p-25f,c=a+b; __CPROVER_assert(c==0x1.000002p0f && fegetround()==FE_UPWARD,"fenv");',
    'fenv_sqrt_down': 'extern double sqrt(double); fesetround(FE_DOWNWARD); double a=2.0,b=sqrt(a); __CPROVER_assert(b==0x1.6a09e667f3bccp0,"sqrt-down");',
    'fenv_fma_up': 'extern double fma(double,double,double); fesetround(FE_UPWARD); double a=1.0,b=0x1p-54,c=fma(a,a,b); __CPROVER_assert(c==0x1.0000000000001p0,"fma-up");',
    'user_sqrt': 'extern double sqrt(double); double b=sqrt(4.0); __CPROVER_assert(b==9.0,"user-body");',
})
BOUNDARIES = {
    'changed_rounding': '__CPROVER_rounding_mode=5; float a=1.5f, b=a+a;',
    'float_int_overflow': 'double a=0x1p31; int b=a;',
    'negative_unsigned': 'float a=-1.0f; unsigned b=a;',
    'nan_int': 'float z=0.0f; float a=z/z; int b=a;',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--c2btor', '--cbmc', dest='cbmc', type=Path, required=True)
    parser.add_argument('--catbtor', type=Path, required=True)
    parser.add_argument('--btorsim', type=Path, required=True)
    parser.add_argument('--ric3', type=Path, help='optional symbolic backend checks')
    parser.add_argument('--build-dir', type=Path, default=Path('build'))
    parser.add_argument('--cxx', default='c++')
    parser.add_argument('--include-dir', action='append', default=[])
    parser.add_argument('--numeric-from', type=Path, help='reuse unchanged circuit fixtures and completed numeric checks')
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    commands = []

    def run(command, stem, allow_failure=False):
        command = [str(arg) for arg in command]
        result = subprocess.run(command, cwd=root, capture_output=True, text=True, timeout=120)
        (out / (stem + '.stdout')).write_text(result.stdout)
        (out / (stem + '.stderr')).write_text(result.stderr)
        commands.append({'command': command, 'exit_code': result.returncode})
        (out / 'commands.json').write_text(json.dumps(commands, indent=2))
        if result.returncode and not allow_failure:
            raise RuntimeError(f'{stem} failed: {result.stderr[-1000:]}')
        return result

    if args.numeric_from:
        previous = args.numeric_from.resolve()
        commands_data = json.loads((previous / 'commands.json').read_text())
        generate = next(r for r in commands_data if r['command'][0].endswith('float_circuits') and len(r['command']) == 2)
        assert generate['exit_code'] == 0
        assert json.loads((previous / 'mismatches.json').read_text()) == []
        cases = list(csv.DictReader((previous / 'cases.tsv').open(), delimiter='\t'))
        assert len(list(previous.glob('batch_*.sim.stdout'))) == (len(cases)+127)//128
        # The immutable source manifest is written before generation below.
        hashes = json.loads((previous / 'numeric-sources.json').read_text())
        assert all(hashlib.sha256((root / name).read_bytes()).hexdigest() == digest for name,digest in hashes.items())
    else:
        numeric_sources = ['src/goto-btor2/ieee754_arith.cpp', 'src/goto-btor2/ieee754_math.cpp', 'regression/goto-btor2/float_circuits.cpp']
        (out / 'numeric-sources.json').write_text(json.dumps({f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in numeric_sources},indent=2))
        fixture = out / 'float_circuits'
        build = args.build_dir.resolve()
        run([args.cxx, '-std=c++17', '-O2', '-fno-fast-math', '-ffp-contract=off',
             '-frounding-math', '-I' + str(root / 'src'),
             root / 'regression/goto-btor2/float_circuits.cpp',
             root / 'src/goto-btor2/ieee754_arith.cpp',
             root / 'src/goto-btor2/ieee754_math.cpp',
             root / 'src/goto-btor2/btor2_builder.cpp',
             build / 'lib/libutil.a', build / 'lib/libbig-int.a', '-o', fixture], 'compile')
        run([fixture, out], 'generate')
        cases = list(csv.DictReader((out / 'cases.tsv').open(), delimiter='\t'))
        checked = {}
        models = sorted(out.glob('batch_*.btor2'), key=lambda p: int(p.stem.split('_')[1]))

        def mismatches(model, stem):
            run([args.catbtor.resolve(), model], stem + '.parser')
            vcd = out / (stem + '.vcd')
            run([args.btorsim.resolve(), '--vcd', vcd, '-r', '1', model], stem + '.sim')
            text = vcd.read_text()
            names = {code: int(case) for code, case in re.findall(
                r'\$var wire 1 (\S+) case_(\d+) \$end', text)}
            values = {names[code]: int(value) for value, code in re.findall(
                r'^([01])(\S+)$', text, re.M) if code in names}
            return values

        for model in models:
            values = mismatches(model, model.stem)
            expected_count = min(128, len(cases) - int(model.stem.split('_')[1]) * 128)
            if len(values) != expected_count:
                raise RuntimeError(f'{model.name}: missing simulator observations')
            checked.update(values)
        failed = [cases[i] for i, mismatch in checked.items() if mismatch]
        (out / 'mismatches.json').write_text(json.dumps(failed, indent=2))
        if len(checked) != len(cases) or failed:
            raise RuntimeError(f'{len(failed)} numerical mismatches; see {out / "mismatches.json"}')

        # A deliberately wrong oracle bit must be detected by the same simulator.
        lines = models[0].read_text().splitlines()
        nodes = {int(line.split()[0]): (i, line.split())
                 for i, line in enumerate(lines) if line.split() and line.split()[0].isdigit()}
        init = next(line.split() for line in lines if ' init ' in line)
        mismatch = nodes[int(init[4])][1]
        equal = nodes[int(mismatch[3])][1]
        expected_index, fields = nodes[int(equal[4])]
        fields[3] = '1'  # first case is +0 + +0; change its expected value to min subnormal
        lines[expected_index] = ' '.join(fields)
        control = out / 'wrong_oracle.btor2'
        control.write_text('\n'.join(lines) + '\n')
        if mismatches(control, 'wrong_oracle').get(0) != 1:
            raise RuntimeError('negative control was not detected')

    integration = []
    for case, body in {**INTEGRATION, **BOUNDARIES}.items():
        # Cover both C target pointer/long layouts; IEEE format comes from
        # float/double, not from the target's pointer width.
        for target in (32, 64):
            stem = f'{case}_{target}'
            source = out / (stem + '.c')
            prefix = ('double sqrt(double x) { return 9.0; }\n' if case == 'user_sqrt'
                      else '#include <fenv.h>\n' if case.startswith('fenv_') else '')
            source.write_text(prefix + 'int main(void) {\n' + body +
                              '\n__CPROVER_assert(0,"completion");\n}\n')
            model, mapping = out / (stem + '.btor2'), out / (stem + '.map.json')
            run([args.cbmc.resolve(), source, '--' + str(target), '--inline',
                 '--goto-btor2', '--array', 'bv', *['-I'+p for p in args.include_dir], '--no-standard-checks',
                 '--no-pointer-check', '--no-bounds-check', '--no-built-in-assertions',
                 '--goto-btor2-out', model, '--goto-btor2-map-out', mapping], stem + '.convert')
            run([args.catbtor.resolve(), model], stem + '.parser')
            sim = run([args.btorsim.resolve(), '-v', '-r', '80', '--vcd',
                       out / (stem + '.vcd'), model], stem + '.sim')
            reached = {int(i) for i in re.findall(r'b(\d+)@\d+', sim.stdout)}
            bad_nodes = [int(line.split()[0]) for line in model.read_text().splitlines()
                         if len(line.split()) > 1 and line.split()[1] == 'bad']
            data = json.loads(mapping.read_text())
            if case in BOUNDARIES:
                expected = {i for i, node in enumerate(bad_nodes) if node in {
                    p['bad_node'] for p in data['memory']['properties']
                    if p['property_class'] == 'model_limit'}}
                if not reached or not reached <= expected:
                    raise RuntimeError(f'{stem}: expected model boundary, got {reached}')
            else:
                marker = data['source_properties'][-1]['bad_node']
                if reached != {bad_nodes.index(marker)}:
                    raise RuntimeError(f'{stem}: numerical assertion or missing completion: {reached}')
            integration.append({'case': stem, 'reached_bad_indices': sorted(reached),
                                'classification': 'model_limit' if case in BOUNDARIES else 'completed'})
    # An unsupported source format must fail conversion with no usable model.
    source = out / 'unsupported_long_double.c'
    source.write_text('int main(void) { long double a=1.5L; long double b=a+a; __CPROVER_assert(b==3.0L,"value"); }\n')
    model = out / 'unsupported_long_double.btor2'
    rejected = run([args.cbmc.resolve(), source, '--32', '--inline', '--goto-btor2',
                    '--array', 'bv', '--no-standard-checks', '--no-built-in-assertions',
                    '--goto-btor2-out', model], 'unsupported_long_double.convert', allow_failure=True)
    if not rejected.returncode or (model.exists() and model.stat().st_size):
        raise RuntimeError('unsupported long double was accepted')
    (out / 'integration.json').write_text(json.dumps(integration, indent=2))

    backend = []
    if args.ric3:
        symbolic = {
            'symbolic_add_safe': ('a>=1.0f && a<=2.0f', 'b>=2.0f && b<=4.0f', 'UNSAT'),
            'symbolic_add_unsafe': ('a==1.5f', 'b<3.0f', 'SAT'),
        }
        for name, (assumption, assertion, expected) in symbolic.items():
            source, model = out / (name + '.c'), out / (name + '.btor2')
            source.write_text('extern float __VERIFIER_nondet_float(void);\n'
                              'int main(void) { float a=__VERIFIER_nondet_float(); '
                              f'__CPROVER_assume({assumption}); float b=a+a; '
                              f'__CPROVER_assert({assertion},"range"); }}\n')
            run([args.cbmc.resolve(), source, '--32', '--inline', '--goto-btor2',
                 '--array', 'bv', '--no-standard-checks', '--no-pointer-check',
                 '--no-bounds-check', '--no-built-in-assertions',
                 '--goto-btor2-out', model], name + '.convert')
            run([args.catbtor.resolve(), model], name + '.parser')
            solver = run(ric3_command(args.ric3.resolve(), model, 'ic3', 30) +
                         ['--frts', 'false', '--scorr', 'false'], name + '.solver')
            if not re.search(r'^'+expected+r'$', solver.stdout, re.M):
                raise RuntimeError(f'{name}: expected {expected}, got {solver.stdout[:100]}')
            if expected == 'SAT':
                witness = out / (name + '.witness')
                witness.write_text(solver.stdout[solver.stdout.index('sat\n'):])
                run([args.btorsim.resolve(), '-v', '--vcd', out / (name + '.vcd'),
                     model, witness], name + '.replay')
            backend.append({'case': name, 'result': expected, 'replayed': expected == 'SAT'})
        (out / 'backend.json').write_text(json.dumps(backend, indent=2))

    summary = {'numeric_cases': len(cases), 'numeric_mismatches': 0,
               'negative_control': 'detected', 'seed': 20261003,
               'integration_cases': len(integration), 'unsupported_format': 'rejected',
               'backend': backend, 'platform': platform.platform(),
               'tool_sha256': {str(p.resolve()): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in [args.cbmc, args.catbtor, args.btorsim] +
                               ([args.ric3] if args.ric3 else [])},
               'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               'source_sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in [root / 'src/goto-btor2/ieee754_arith.cpp',
         root / 'src/goto-btor2/ieee754_math.cpp',
                                           root / 'src/goto-btor2/expr_to_btor2_float.cpp',
                                           Path(__file__), root / 'regression/goto-btor2/float_circuits.cpp']}}
    (out / 'summary.json').write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
