"""Focused artifact replay and public-result regressions (no task scheduler)."""
import argparse
from contextlib import redirect_stderr, redirect_stdout
import io
import json
import os
import runpy
import signal
import time
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.btor2_parser import Btor2Model
from scripts.carat import classify, race
from scripts.cex_parser import parse_cex
from scripts import trace_recovery as tool
entry = runpy.run_path(str(Path(__file__).resolve().parents[2] / "c2btor-verify"))
main, parser, run = (entry[name] for name in ("main", "parser", "run"))
from scripts.source_map import digest, enrich_map
from scripts.trace_recovery import check_counter, read_complete_trace, recover
from scripts.yaml21_writer import SequenceWriter
from scripts.tests.test_yaml_io import check_schema


class WitnessV2Tests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name).resolve()
        self.addCleanup(self.temporary.cleanup)

    def fixture(self, frames=1):
        source = self.directory / "test.c"
        source.write_text("int main(){ int x=__VERIFIER_nondet_int(); __VERIFIER_error(); int y=__VERIFIER_nondet_int(); }\n")
        model = self.directory / "model.btor2"
        model.write_text("""1 sort bitvec 1
2 sort bitvec 8
3 sort bitvec 32
4 zero 1
5 state 1 pc
6 init 1 5 4
7 next 1 5 5
8 input 3 first
9 input 3 after_error
10 one 1 __c2btor_exec_10
11 output 10
12 one 1 __c2btor_exec_11
13 output 12
14 one 1 __c2btor_exec_12
15 output 14
16 zero 2
17 state 2 count_before
18 state 2 count_after
19 init 2 17 16
20 init 2 18 16
21 inc 2 17
22 inc 2 18
23 next 2 17 21
24 next 2 18 22
25 one 1 __c2btor_bad_11
26 output 25
27 bad 25
28 or 3 8 8 __c2btor_value_10
29 output 28
30 or 3 9 9 __c2btor_value_12
31 output 30
""")
        source_location = dict(file_name=str(source), line="1", function="main")
        def event(identity, **kwargs):
            return dict(instruction_id=identity, pc=0, goto_location=identity, source=source_location, kind="FUNCTION_CALL",
                        successors=[identity + 1] if identity != 12 else [],
                        executed_output={10:11,11:13,12:15}[identity], **kwargs)
        before = event(10,nondet_function="__VERIFIER_nondet_int",result_type="signedbv",result_width=32,
                       result_destination="x",value_node=8,value_output=29,counter_node=17,counter_width=8,executed_node=10)
        after = event(12,nondet_function="__VERIFIER_nondet_int",result_type="signedbv",result_width=32,
                      result_destination="y",value_node=9,value_output=31,counter_node=18,counter_width=8,executed_node=14)
        mapping=dict(format_version="2",witness_counter_format="post-counter-1",int_width=32,long_width=32,pointer_width=32,
                     pc_node=5,input_files=[str(source)],source_hashes={str(source):digest(source)},
                     specification="CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )",
                     instructions=[before,event(11,bad_node=27,bad_condition_output=26,property_class="unreach-call"),after],
                     blocks=[dict(pc=0,instructions=[10,11,12],entry_instruction=10,exit_instructions=[12])])
        map_path=self.directory/'model.map.json';map_path.write_text(json.dumps(enrich_map(mapping,model)))
        cex=self.directory/'model.cex'
        lines=['sat','b0']
        for t in range(frames):
            lines += [f'#{t}','0 0',f'1 {t:08b}',f'2 {t:08b}',f'@{t}',f'0 {7:032b}',f'1 {999:032b}']
        cex.write_text('\n'.join(lines+['.'])+'\n')
        return model,map_path,cex

    def test_standard_original_ordinals_and_strict_syntax(self):
        model,_,cex=self.fixture()
        trace=parse_cex(cex.read_text(),Btor2Model(model))
        self.assertEqual(trace.frames[0]['inputs'][8],f'{7:032b}')
        for content in ('event-json\n'+cex.read_text(),cex.read_text().replace('sat\nb0','sat\nsat\nb0')):
            with self.assertRaises(ValueError):parse_cex(content,Btor2Model(model))

    def test_omitted_input_rejected_before_simulator(self):
        model,mapping,cex=self.fixture()
        cex.write_text(cex.read_text().replace(f'1 {999:032b}\n',''))
        with patch('scripts.trace_recovery.replay') as simulator:
            with self.assertRaisesRegex(ValueError,'missing concrete input node 9'):
                recover(model,mapping,cex,self.directory/'witness.yml')
            simulator.assert_not_called()

    def test_free_state_requires_explicit_value(self):
        model,_,cex=self.fixture()
        model.write_text(model.read_text()+'32 state 3 free\n')
        with self.assertRaisesRegex(ValueError,'missing concrete state node 32'):
            read_complete_trace(cex,Btor2Model(model))

    def test_state_without_next_needs_each_frame_assignment(self):
        model,_,cex=self.fixture(frames=2)
        model.write_text(model.read_text()+'32 state 3 free\n')
        cex.write_text(cex.read_text().replace('@0\n','3 '+f'{0:032b}'+'\n@0\n'))
        with self.assertRaisesRegex(ValueError,'missing concrete state node 32 at frame 1'):
            read_complete_trace(cex,Btor2Model(model))

    def test_counter_wrap_and_mismatch(self):
        model,_,_=self.fixture()
        event=dict(counter_width=8,counter_node=17)
        observations={255:{'count_before':'11111111'},256:{'count_before':'00000000'}}
        check_counter(event,255,observations,Btor2Model(model),True)
        with self.assertRaisesRegex(ValueError,'counter/execution mismatch'):
            check_counter(event,255,observations,Btor2Model(model),False)

    def test_source_cache_preserves_certified_same_line_calls_and_loop(self):
        source = self.directory / 'calls.c'
        text = ('/* __VERIFIER_nondet_int() */\n'
                'int main(){ for(;;){ int x=__VERIFIER_nondet_int(); '
                'int y=__VERIFIER_nondet_int(); __VERIFIER_error(); }}\n')
        source.write_text(text)
        location = dict(file_name=str(source),line='2',column='',function='main')
        calls = list(__import__('re').finditer(r'__VERIFIER_nondet_int\(\)', text))[-2:]
        events = [dict(source=location,original_event_ids=[index],nondet_function='__VERIFIER_nondet_int',
                       call_return_location=dict(format='c2btor-c-call-site-1',file_name=str(source),line=2,
                                                 column=call.end()-1-text.rfind('\n',0,call.end()-1)))
                  for index,call in enumerate(calls)]
        expected = [tool.call_location(location,event['nondet_function'],True,
                                      call_return_location=event['call_return_location']) for event in events]
        loop = dict(location,kind='for')
        expected_loop = tool.loop_location(loop)
        cache = tool.SourceLocations()
        with patch.object(tool,'_masked_source',wraps=tool._masked_source) as parsed:
            for _ in range(20):
                actual = [cache.call(event,event['nondet_function'],True) for event in events]
                self.assertEqual(actual,expected)
                self.assertEqual(cache.loop(loop),expected_loop)
            self.assertEqual(parsed.call_count,1,'one source read/mask per recovery task')
        self.assertNotEqual(expected[0]['column'],expected[1]['column'])
        malformed = dict(events[0],call_return_location=dict(events[0]['call_return_location'],column=1))
        with self.assertRaisesRegex(ValueError,'certificate does not identify'):
            cache.call(malformed,malformed['nondet_function'],True)
        unavailable = dict(events[0],call_return_location_unavailable='macro expansion')
        with self.assertRaisesRegex(ValueError,'could not certify'):
            cache.call(unavailable,unavailable['nondet_function'],True)

    def test_source_cache_lives_for_one_recovery_only(self):
        source = self.directory / 'calls.c'
        source.write_text('int main(){ __VERIFIER_error(); }\n')
        event = dict(source=dict(file_name=str(source),line='1'),original_event_ids=[1])
        first = tool.SourceLocations().call(event,'__VERIFIER_error',False)
        source.write_text('int main(){   __VERIFIER_error(); }\n')
        second = tool.SourceLocations().call(event,'__VERIFIER_error',False)
        self.assertEqual(second['column'],first['column']+2)

    def test_source_cache_cannot_bypass_certificate_type_checks(self):
        source=self.directory/'calls.c'
        text='int main(){ __VERIFIER_error(); }\n';source.write_text(text)
        certificate=dict(format='c2btor-c-call-site-1',file_name=str(source),line=1,
                         column=text.index(')',text.index('__VERIFIER_error'))+1)
        event=dict(source=dict(file_name=str(source),line='1'),original_event_ids=[1],
                   call_return_location=certificate)
        cache=tool.SourceLocations();cache.call(event,'__VERIFIER_error',False)
        for malformed in (dict(certificate,line=True),sorted(certificate.items())):
            with self.subTest(certificate=malformed):
                with self.assertRaisesRegex(ValueError,'invalid frontend'):
                    cache.call(dict(event,call_return_location=malformed),'__VERIFIER_error',False)

    def test_stream_writer_preserves_repeated_calls_and_changing_values(self):
        model,mapping,_=self.fixture()
        value=json.loads(mapping.read_text())
        metadata=dict(format_version='2.1',uuid='48a6bb39-a6f8-4c29-b31d-3312033564a8',
                      creation_time='2026-10-18T12:00:00+00:00',producer=dict(name='C2Btor',version='test'),
                      task={key:value[key] for key in ('input_files','source_hashes','specification','data_model')})
        metadata['task']['input_file_hashes']=metadata['task'].pop('source_hashes')
        metadata['task']['language']='C'
        outgoing=io.StringIO();writer=SequenceWriter(outgoing,metadata)
        location=dict(file_name=str(self.directory/'test.c'),line=1,column=1)
        for number in (7,7,8,7):
            writer.append(dict(type='function_return',action='follow',location=location,
                               constraint=dict(format='ext_c_expression',value=f'\\result == {number}')))
        writer.append(dict(type='target',action='follow',location=location));writer.finish()
        document=tool.yaml_module().safe_load(outgoing.getvalue())
        check_schema(document)
        points=[segment['segment'][0]['waypoint'] for segment in document[0]['content']]
        self.assertEqual([point['constraint']['value'] for point in points[:-1]],
                         ['\\result == 7','\\result == 7','\\result == 8','\\result == 7'])
        self.assertEqual(len(points),5,'repeated dynamic calls must never be removed')

    @unittest.skipUnless(os.environ.get('BTORSIM'),'set BTORSIM for independent model replay')
    def test_final_frame_call_and_first_bad_prefix(self):
        for frames in (1,2):
            with self.subTest(frames=frames):
                model,mapping,cex=self.fixture(frames)
                output=self.directory/f'witness{frames}.yml'
                recover(model,mapping,cex,output)
                document=tool.load_witness(output)
                check_schema(document)
                points=[s['segment'][0]['waypoint'] for s in document[0]['content']]
                self.assertEqual([p['type'] for p in points],['function_return','target'])
                self.assertEqual(points[0]['constraint']['value'],'\\result == 7')
                self.assertFalse(list(self.directory.glob('.c2btor-replay-*')))

    @unittest.skipUnless(os.environ.get('BTORSIM'),'set BTORSIM for independent model replay')
    def test_replay_rejects_contradictory_state_annotation(self):
        model,mapping,cex=self.fixture()
        cex.write_text(cex.read_text().replace('#0\n0 0','#0\n0 1'))
        with self.assertRaisesRegex(ValueError,'replay failed'):
            recover(model,mapping,cex,self.directory/'witness.yml')

    def test_cli_minimal_and_result_classification(self):
        actions={a.dest for a in parser()._actions}
        self.assertEqual(actions,{'help','program','property','data_model','witness_output','keep_intermediates','version'})
        self.assertEqual(classify('Safe\n','ic3',0),'Safe')
        for log,algorithm,code in [('','ic3',0),('Safe\nUnsafe\n','ic3',0),('Safe\n','bmc',0),('Safe\n','ic3',9)]:
            self.assertEqual(classify(log,algorithm,code),'Unknown')

    def test_wrapper_unknown_and_crash_and_unsafe_delivery_error(self):
        model,mapping,_=self.fixture()
        args=argparse.Namespace(program=str(self.directory/'test.c'),property=str(self.directory/'unreach.prp'),
                                data_model='ILP32',witness_output=str(self.directory/'witness.yml'),keep_intermediates=None)
        Path(args.property).write_text(json.loads(mapping.read_text())['specification'])
        for verdict,expected in [('Unknown','UNKNOWN'),('crash','Carat crashed'),('Unsafe','violation witness delivery failed')]:
            with self.subTest(verdict=verdict):
                def convert(command,**kwargs):
                    Path(command[command.index('--goto-btor2-out')+1]).write_bytes(model.read_bytes())
                    Path(command[command.index('--goto-btor2-map-out')+1]).write_bytes(mapping.read_bytes())
                    return subprocess.CompletedProcess(command,0,'','')
                def backend(*args):
                    if verdict == 'crash': raise ValueError('Carat crashed')
                    return verdict,'test'
                with patch.dict(run.__globals__,executable=lambda name:name,race=backend),patch('subprocess.run',side_effect=convert) as calls:
                    if verdict != 'Unknown':
                        with self.assertRaisesRegex(ValueError,expected): run(args)
                    else: self.assertEqual(run(args),expected)
                    self.assertEqual(calls.call_count,1,'convert only once; race is called separately')

    def fake_carat(self, plan):
        script=self.directory/'fake-carat'
        script.with_suffix('.json').write_text(json.dumps(plan))
        script.write_text(r"""#!/usr/bin/env python3
import json, os, signal, subprocess, sys, time
from pathlib import Path
script=Path(__file__)
plan=json.loads(script.with_suffix('.json').read_text())
name=Path(sys.argv[sys.argv.index('-w')+1]).name
options=plan.get(name,{})
def record(pid):
    with script.with_suffix('.pids').open('a') as stream: stream.write(str(pid)+'\n')
record(os.getpid())
if options.get('child'):
    child=subprocess.Popen([sys.executable,'-c','import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)'])
    record(child.pid)
if options.get('verbose'): print('worker log\n'*100000,flush=True)
result=options.get('result','Unknown')
if options.get('early'): print(result,flush=True)
time.sleep(options.get('delay',0.02))
if result == 'Unsafe' and not options.get('missing'):
    work=Path(sys.argv[sys.argv.index('-w')+1])
    (work/'model.cexb').write_text('sat\nb0\n@0\n.\n')
if not options.get('early'): print(result,flush=True)
if options.get('code'): print('worker failed',file=sys.stderr)
sys.exit(options.get('code',0))
""")
        script.chmod(0o755)
        return script

    def assert_workers_stopped(self, script):
        pid_file=script.with_suffix('.pids')
        pids=list(map(int,pid_file.read_text().split())) if pid_file.exists() else []
        def alive(pid):
            try: os.kill(pid,0)
            except ProcessLookupError: return False
            # An orphan already killed in a container may await PID1 reaping.
            stat=Path(f'/proc/{pid}/stat')
            if stat.exists() and stat.read_text().split(') ',1)[1].split()[0]=='Z': return False
            return True
        until=time.monotonic()+2
        while any(alive(pid) for pid in pids) and time.monotonic()<until: time.sleep(0.02)
        self.assertFalse([pid for pid in pids if alive(pid)],'no surviving worker or descendant')

    def test_race_waits_for_complete_winning_trace_and_kills_losers(self):
        model,_,_=self.fixture()
        script=self.fake_carat({'0_cegar_ic3_ctg':dict(result='Unsafe',early=True,delay=0.3),
                                '1_cegar_ic3':dict(delay=60,child=True),
                                '2_cegar_ic3_all':dict(delay=60,verbose=True),'6_wlbmc':dict(delay=60)})
        start=time.monotonic()
        self.assertEqual(race(script,model,self.directory,start+5),('Unsafe','0_cegar_ic3_ctg'))
        self.assertGreaterEqual(time.monotonic()-start,0.25,'do not select a log line before exit/export')
        self.assertEqual((self.directory/'model.cex').read_text(),'sat\nb0\n@0\n.\n')
        self.assertFalse(list(self.directory.glob('.carat-*')))
        self.assert_workers_stopped(script)

    def test_bounded_safe_and_crash_do_not_win(self):
        model,_,_=self.fixture()
        script=self.fake_carat({'6_wlbmc':dict(result='Safe'), '0_cegar_ic3_ctg':dict(code=2),
                                '1_cegar_ic3':dict(result='Unknown'),'2_cegar_ic3_all':dict(result='Unsafe',delay=0.15)})
        with redirect_stderr(io.StringIO()):
            self.assertEqual(race(script,model,self.directory,time.monotonic()+5),('Unsafe','2_cegar_ic3_all'))
        self.assert_workers_stopped(script)

    def test_race_timeout_reaps_every_worker(self):
        model,_,_=self.fixture()
        script=self.fake_carat({name:dict(delay=60) for name in ('0_cegar_ic3_ctg','1_cegar_ic3','2_cegar_ic3_all','6_wlbmc')})
        with self.assertRaises(TimeoutError): race(script,model,self.directory,time.monotonic()+0.2)
        self.assert_workers_stopped(script)

    def test_race_unknown_all_crashes_and_missing_trace(self):
        model,_,_=self.fixture()
        script=self.fake_carat({})
        with redirect_stderr(io.StringIO()):
            self.assertEqual(race(script,model,self.directory,time.monotonic()+5),('Unknown',None))
            script=self.fake_carat({name:dict(code=2) for name in ('0_cegar_ic3_ctg','1_cegar_ic3','2_cegar_ic3_all','6_wlbmc')})
            with self.assertRaisesRegex(ValueError,'all Carat workers crashed'):
                race(script,model,self.directory,time.monotonic()+5)
            script=self.fake_carat({'0_cegar_ic3_ctg':dict(result='Unsafe',missing=True),
                                    '1_cegar_ic3':dict(delay=60),'2_cegar_ic3_all':dict(delay=60),'6_wlbmc':dict(delay=60)})
            with self.assertRaisesRegex(ValueError,'Unsafe without'):
                race(script,model,self.directory,time.monotonic()+5)
        self.assert_workers_stopped(script)

    def test_safe_writer_needs_no_schema_runtime(self):
        from scripts.correctness import generate_weak
        model,mapping,_=self.fixture()
        # Keep PyYAML loaded across patch.dict's sys.modules restoration.
        # Reimporting it while LibYAML still holds the previous resolver classes
        # can leave C loader nodes without tags; this test removes schemas only.
        tool.yaml_module()
        with patch.dict(sys.modules, jsonschema=None, referencing=None):
            output=generate_weak(model,mapping,self.directory/'safe',result='Safe')
        document=tool.load_witness(output)
        check_schema(document,'correctness-witness-schema.yml')
        self.assertTrue(all(row['invariant']['value']=='1' for row in document[0]['content']))

    def test_sigterm_to_entry_cleans_worker_process_groups(self):
        model,mapping,_=self.fixture()
        prop=self.directory/'unreach.prp';prop.write_text(json.loads(mapping.read_text())['specification'])
        converter=self.directory/'fake-c2btor'
        converter.write_text('#!/usr/bin/env python3\nimport shutil,sys\n'
                             f'shutil.copyfile({str(model)!r},sys.argv[sys.argv.index("--goto-btor2-out")+1])\n'
                             f'shutil.copyfile({str(mapping)!r},sys.argv[sys.argv.index("--goto-btor2-map-out")+1])\n')
        converter.chmod(0o755)
        script=self.fake_carat({name:dict(delay=60,child=True) for name in ('0_cegar_ic3_ctg','1_cegar_ic3','2_cegar_ic3_all','6_wlbmc')})
        env=dict(os.environ,C2BTOR=str(converter),CARAT=str(script))
        process=subprocess.Popen([sys.executable,str(Path(__file__).resolve().parents[2]/'c2btor-verify'),
                                  str(self.directory/'test.c'),'--property',str(prop),'--data-model','ILP32'],
                                  cwd=self.directory,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        try:
            until=time.monotonic()+5
            while not script.with_suffix('.pids').exists() and time.monotonic()<until:
                if process.poll() is not None: break
                time.sleep(0.02)
            self.assertTrue(script.with_suffix('.pids').exists())
            time.sleep(0.1)
            process.send_signal(signal.SIGTERM)
            stdout,stderr=process.communicate(timeout=5)
            self.assertIn('Verification result: UNKNOWN',stdout,stderr)
            self.assertNotIn('Verification result: TRUE',stdout)
        finally:
            if process.poll() is None: process.kill();process.wait()
            process.stdout.close()
            process.stderr.close()
        self.assert_workers_stopped(script)


if __name__=='__main__':unittest.main()
