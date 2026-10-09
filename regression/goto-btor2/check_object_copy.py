#!/usr/bin/env python3
"""Replay C byte-copy rules across packed and array memory encodings.

These concrete executions check values, overlap, untouched bytes and copied
initialization metadata. They are not an unbounded source-safety proof.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
CASES = {
    'forward_overlap': ('unsigned char a[5]={1,2,3,4,5}; memmove(a+1,a,4); '
                        '__CPROVER_assert(a[0]==1 && a[1]==1 && a[4]==4,"snapshot");', 'completion'),
    'backward_overlap': ('unsigned char a[5]={1,2,3,4,5}; memmove(a,a+1,4); '
                         '__CPROVER_assert(a[0]==2 && a[3]==5 && a[4]==5,"tail");', 'completion'),
    'unaligned_alias': ('unsigned a[2]={0x12345678,0xabcdef01}; unsigned char *p=(void*)a; '
                        'memmove(p+1,p+4,3); __CPROVER_assert(a[0]==0xcdef0178 && a[1]==0xabcdef01,"aliases");', 'completion'),
    'calloc_prefix': ('unsigned char *p=calloc(4,1), q[6]={1,2,3,4,5,6}; p[1]=9; '
                       'memcpy(q+1,p,4); __CPROVER_assert(q[0]==1 && q[1]==0 && q[2]==9 && q[4]==0 && q[5]==6,"zero-and-tail");', 'completion'),
    'zero_size': ('char a[2]={3,4}; memmove(a+1,a,0); __CPROVER_assert(a[0]==3 && a[1]==4,"empty");', 'completion'),
    'undefined_bytes': ('int *p=malloc(sizeof(int)), q=1; memcpy(&q,p,sizeof(q)); '
                        '__CPROVER_assert(q==0,"indeterminate");', 'model_limit'),
    'overlap_memcpy': ('char a[4]={1,2,3,4}; memcpy(a+1,a,3);', 'memory_validity'),
    'readonly': ('const char *p="ab"; char a[3]={1,2,3}; memcpy((void*)p,a,3);', 'memory_validity'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--c2btor', '--cbmc', dest='cbmc', default=str(ROOT / 'build/bin/c2btor'))
    parser.add_argument('--catbtor', default='catbtor')
    parser.add_argument('--btorsim', default='btorsim')
    parser.add_argument('--include-dir', action='append', default=[])
    parser.add_argument('--target', choices=['32','64'], default='32')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    results = []
    for memory, array in [('object','bv'), ('object','array'), ('global','bv')]:
        for name, (body, expected) in CASES.items():
            directory = args.output / (memory+'-'+array+'-'+name)
            directory.mkdir()
            source, model, mapping = [directory / f for f in ['source.c','model.btor2','map.json']]
            source.write_text('extern void *malloc(__CPROVER_size_t); extern void *calloc(__CPROVER_size_t,__CPROVER_size_t); '
              'extern void *memcpy(void*,const void*,__CPROVER_size_t); extern void *memmove(void*,const void*,__CPROVER_size_t); '
              'int main(void) {'+body+' __CPROVER_assert(0,"completion");}\n')
            def run(stage, command):
                command = list(map(str, command))
                (directory/(stage+'.command.json')).write_text(json.dumps(command,indent=2))
                proc = subprocess.run(command,capture_output=True,text=True,timeout=30)
                (directory/(stage+'.log')).write_text(proc.stdout+proc.stderr)
                assert proc.returncode==0,(name,stage,proc.stderr[-500:])
                return proc.stdout
            run('conversion',[args.cbmc,source,'--'+args.target,'--inline','--goto-btor2','--memory',memory,'--array',array,
              '--goto-btor2-heap-objects','2','--goto-btor2-out',model,'--goto-btor2-map-out',mapping,
              '--no-standard-checks','--no-pointer-check','--no-bounds-check','--no-built-in-assertions',
              *['-I'+p for p in args.include_dir]])
            run('parser',[args.catbtor,model])
            text = run('simulation',[args.btorsim,'-v','-r','1000',model])
            reached = {int(i) for i in re.findall(r'b(\d+)@\d+',text)}
            bads = [int(line.split()[0]) for line in model.read_text().splitlines() if re.match(r'^\d+ bad ',line)]
            data = json.loads(mapping.read_text())
            if expected=='completion':
                wanted = {bads.index(data['source_properties'][-1]['bad_node'])}
            else:
                wanted = {bads.index(p['bad_node']) for p in data['memory']['properties'] if p['property_class']==expected}
            assert reached and reached<=wanted,(directory.name,reached,wanted)
            results.append({'case':directory.name,'classification':expected,'passed':True})
            (args.output/'results.json').write_text(json.dumps(results,indent=2))
            print(directory.name,'PASS',flush=True)


if __name__=='__main__':
    main()
