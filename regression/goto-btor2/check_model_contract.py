#!/usr/bin/env python3
"""Check hidden-boundary UNSAT classification with actual solver queries."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from c2btor_model_contract import property_model, unsat_status, boundary_status
from c2btor_witness import normalize_witness
from c2btor_solver import ric3_command


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--c2btor', '--cbmc', dest='cbmc', default=str(ROOT/'build/bin/c2btor'))
    p.add_argument('--ric3', default='ric3')
    p.add_argument('--catbtor', default='catbtor')
    p.add_argument('--btorsim', default='btorsim')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    results = []
    def run(directory, name, cmd):
        cmd = list(map(str, cmd))
        (directory/(name+'.command.json')).write_text(json.dumps(cmd,indent=2))
        proc = subprocess.run(cmd,capture_output=True,text=True,timeout=25)
        text = proc.stdout + proc.stderr
        (directory/(name+'.log')).write_text(text)
        assert proc.returncode == 0, (name,text[-800:])
        return text
    for name, body, expected in [
        ('hidden_limit','unsigned n=17; char a[n]; reach_error();','model_limit'),
        ('hidden_float_mode','__CPROVER_rounding_mode=5; float a=1.0f,b=a+a; reach_error();','model_limit'),
        ('hidden_invalid','char a[2]; a[2]=1; reach_error();','memory_validity'),
        ('safe','char a[2]; a[0]=3; if(a[0]!=3) reach_error();','model_unsat')]:
        d=args.output/name;d.mkdir();source=d/'source.c'
        source.write_text('void reach_error(void) { __CPROVER_assert(0,"target"); }\nint main(void) {'+body+'}\n')
        model=d/'model.btor2';mapping=d/'map.json'
        run(d,'conversion',[args.cbmc,source,'--32','--inline','--goto-btor2',
          '--goto-btor2-out',model,'--goto-btor2-map-out',mapping,'--memory-object-max-bytes','16',
          '--goto-btor2-error-function','reach_error','--goto-btor2-reach-only','--goto-btor2-no-heap-guards',
          '--no-standard-checks','--no-pointer-check','--no-bounds-check','--no-built-in-assertions'])
        run(d,'parser',[args.catbtor,model])
        raw=run(d,'source-solver',ric3_command(args.ric3,model,'ic3',20) + ['--preproc','false'])
        assert re.search(r'^UNSAT$',raw,re.M),raw[-500:]
        assert unsat_status(model,'ic3',all_properties=True)=='boundary_check_required'
        assert not json.loads(mapping.read_text())['memory']['properties']
        probe=d/'boundary.btor2';indices=property_model(model,probe,boundaries_only=True)
        run(d,'boundary-parser',[args.catbtor,probe])
        query=run(d,'boundary-solver',ric3_command(args.ric3,probe,'ic3',20) + ['--preproc','false'])
        status=boundary_status(query,indices,'ic3');assert status==expected,(name,status)
        if expected!='model_unsat':
            witness=d/'boundary.witness';witness.write_text(normalize_witness(query)[0])
            run(d,'boundary-replay',[args.btorsim,'-c',probe,witness])
        else:
            assert boundary_status(query,indices,'bmc')=='bounded_no_violation'
        complete=d/'complete.btor2';property_model(model,complete)
        run(d,'complete-parser',[args.catbtor,complete])
        full=run(d,'complete-solver',ric3_command(args.ric3,complete,'ic3',20) + ['--preproc','false'])
        assert bool(re.search(r'^UNSAT$',full,re.M)) == (expected=='model_unsat')
        legacy=d/'legacy.btor2';legacy.write_text('\n'.join(line for line in model.read_text().splitlines() if not line.startswith('; c2btor-proof-'))+'\n')
        assert unsat_status(legacy,'ic3',all_properties=True)=='unverified_unsat'
        results.append({'case':name,'raw_source_result':'UNSAT','classified':status,'BtorSim':expected!='model_unsat','passed':True})
        (args.output/'results.json').write_text(json.dumps(results,indent=2))
        print(name,status,'PASS',flush=True)

    # A backend selecting p0 must not miss a later property. Also provide an
    # explicit false query for a model with no bads, without inventing a fault.
    for name, properties, verdict in [
        ('multiple_properties', '4 bad 2 first\n5 bad 3 second\n', 'sat'),
        ('zero_properties', '', 'unsat')]:
        d=args.output/name;d.mkdir();model=d/'model.btor2'
        model.write_text('; c2btor-proof-contract 1\n1 sort bitvec 1\n2 zero 1\n3 one 1\n'+properties)
        if properties:
            assert unsat_status(model,'portfolio')=='full_check_required'
        complete=d/'complete.btor2';property_model(model,complete)
        run(d,'parser',[args.catbtor,complete])
        query=run(d,'solver',ric3_command(args.ric3,complete,'ic3',20)+['--preproc','false'])
        assert re.search(r'^'+verdict+r'$',query,re.M|re.I),query
        if verdict=='sat':
            witness=d/'witness';witness.write_text(normalize_witness(query)[0])
            run(d,'replay',[args.btorsim,'-c',complete,witness])
        results.append({'case':name,'complete_query':verdict,'passed':True})
    (args.output/'results.json').write_text(json.dumps(results,indent=2))

if __name__=='__main__':main()
