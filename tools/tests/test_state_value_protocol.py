import argparse
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import reports
from evaluation.state_values import protocol as sv
from report_fixture import fixture
from test_state_memory import HEADER


class StateValueProtocol(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.clang = shutil.which(os.environ.get('NIRVANA_CLANG', 'clang'))
        cls.solver = shutil.which(os.environ.get('NIRVANA_Z3', 'z3'))
        if not cls.clang or not cls.solver: raise unittest.SkipTest('requires Clang and Z3')

    def ast(self, source, name):
        p = subprocess.run([self.clang, '-std=c11', '-Werror', '-fsyntax-only', '-Xclang', '-ast-dump=json',
                            '-Xclang', '-ast-dump-filter=' + name, '-x', 'c', '-'], input=HEADER+source,
                           capture_output=True, text=True, timeout=10)
        self.assertEqual(p.returncode, 0, p.stderr)
        return p.stdout

    def prepare(self, root, *, unsupported=False, unknown=False, bound=False):
        source = ('switch(state[0]){case 1:return 1;}return state[2];' if unsupported
                  else 'uint64_t count=state[0];while(count)--count;return state[2];' if bound
                  else 'return state[2];')
        a = self.ast('uint64_t fixture(uint64_t *state){'+source+'}', 'fixture')
        b = self.ast('uint64_t nirvana_readable(uint64_t address,uint8_t *memory,uint64_t base,uint64_t size)'
                     '{struct nirvana_memory m={memory,base,size};return nirvana_load(&m,address+16,8);}', 'nirvana_readable')
        (root/'source_ast.stdout.txt').write_text(a); (root/'generated_ast.stdout.txt').write_text(b)
        # Protocol-only fixture: the outer report tests bind actual probe JSON.
        row = {'function':'fixture', 'c_footprint':{'status':'measured'},
               'semantics':{'prepare_stdout_sha256':'bound-by-outer-protocol','profile':dict(sv.MEMORY_PROFILE)},
               'stage_checks':{'selected_c':{'parameter_registers':[7]}}}
        args = argparse.Namespace(state_values=True, value_solver='/nonexistent/state-values-z3' if unknown else self.solver, value_seconds=2)
        sv.attach(args, row, root)
        return row

    def test_replay_rebuilds_values_queries_and_precise_metadata(self):
        for variant in ['intact','float','count','profile','query','graph','solver','binding','abi','layout']:
            with self.subTest(variant=variant), tempfile.TemporaryDirectory() as directory:
                root=Path(directory); row=self.prepare(root)
                self.assertEqual(row['state_values']['status'],'equivalent_under_model')
                value=row['state_values']
                if variant=='float': value['source']['modeled_return_paths']=1.0
                elif variant=='count': value['source']['reachable_value_nodes']+=1
                elif variant=='profile': value['profile']['state_bytes']=31
                elif variant in ['query','graph','solver']:
                    record=value['artifacts'][variant]; path=root/record['file']
                    if variant=='query': path.write_text(path.read_text()+'; rebound query change\n')
                    else:
                        raw=json.loads(path.read_text())
                        if variant=='graph': raw['source_outputs'][0]=0
                        else: raw[0]['stdout']='sat\n'
                        path.write_text(json.dumps(raw))
                    record['sha256']=sv.sha(path)  # A matching hash is insufficient.
                elif variant=='binding': row['semantics'].clear()
                elif variant=='abi': row['stage_checks']['selected_c']['parameter_registers']=[1,7]
                elif variant=='layout': row['semantics']['profile']['state_pointer']+=8
                if variant=='intact': self.assertEqual(sv.replay(root,row),'equivalent_under_model')
                else:
                    with self.assertRaises((ValueError,KeyError)): sv.replay(root,row)

    def test_unavailable_solver_and_unsupported_control_retain_distinct_outcomes(self):
        for unsupported,unknown in [(True,False),(False,True)]:
            with tempfile.TemporaryDirectory() as directory:
                root=Path(directory); row=self.prepare(root,unsupported=unsupported,unknown=unknown)
                expected='unsupported' if unsupported else 'unknown'
                self.assertEqual(row['state_values']['status'],expected)
                self.assertEqual(sv.replay(root,row),expected)
                row['state_values']['reason']='altered reason'
                if unsupported:
                    with self.assertRaises(ValueError): sv.replay(root,row)

    def test_enabled_report_retains_every_state_value_profile(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); report=fixture(root)
            report['state_values']={'model':sv.MODEL,'enabled':True}
            row=report['rows'][0]; row['state_values']={'model':sv.MODEL,'status':'unavailable'}
            report['summary']['state_values']={'unavailable':1}
            reports.index(report)
            for variant in ['missing','count']:
                broken=copy.deepcopy(report)
                if variant=='missing': del broken['rows'][0]['state_values']
                else: broken['summary']['state_values']={}
                with self.assertRaises(reports.Incompatible): reports.index(broken)

    def test_incomplete_guards_and_their_input_witness_are_rebuilt(self):
        for variant in ['intact','witness','guard','profile']:
            with self.subTest(variant=variant), tempfile.TemporaryDirectory() as directory:
                root=Path(directory);row=self.prepare(root,bound=True)
                self.assertEqual(row['state_values']['status'],'unknown')
                self.assertEqual(row['state_values']['reason'],'loop_bound_exhausted')
                if variant=='witness': row['state_values']['bound_witness']['input_words'][0]=0
                elif variant=='guard':
                    path=root/sv.NAMES['graph'];graph=json.loads(path.read_text());graph['source_incomplete']=0
                    path.write_text(json.dumps(graph));row['state_values']['artifacts']['graph']['sha256']=sv.sha(path)
                elif variant=='profile': row['state_values']['profile']['loop_iterations']=15
                if variant=='intact': self.assertEqual(sv.replay(root,row),'unknown')
                else:
                    with self.assertRaises(ValueError): sv.replay(root,row)
