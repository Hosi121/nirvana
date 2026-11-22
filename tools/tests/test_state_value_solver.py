import ctypes
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation.state_values import measure
from test_state_memory import HEADER


class StateValueProofs(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.clang = shutil.which(os.environ.get('NIRVANA_CLANG', 'clang'))
        cls.solver = shutil.which(os.environ.get('NIRVANA_Z3', 'z3'))
        if not cls.clang or not cls.solver: raise unittest.SkipTest('requires Clang and Z3')

    def sources(self, a, b):
        return ['uint64_t fixture(uint64_t *state){' + a + '}',
                'uint64_t nirvana_readable(uint64_t address,uint8_t *memory,uint64_t base,uint64_t size)'
                '{struct nirvana_memory m={memory,base,size};' + b + '}']

    def ast(self, source, name):
        result = subprocess.run([self.clang, '-std=c11', '-Werror', '-fsyntax-only', '-Xclang',
                                 '-ast-dump=json', '-Xclang', '-ast-dump-filter=' + name, '-x', 'c', '-'],
                                input=HEADER + source, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def compare(self, a, b, solver=None):
        a, b = self.sources(a, b)
        return measure(self.ast(a, 'fixture'), self.ast(b, 'nirvana_readable'), 'fixture', [7], solver or self.solver)

    def test_values_agree_across_different_storage_names_and_partial_writes(self):
        a = 'state[0]=(state[0]&~UINT64_C(65280))|UINT64_C(768);return state[0];'
        b = 'nirvana_store(&m,address+1,1,3);return nirvana_load(&m,address,8);'
        result = self.compare(a, b)
        self.assertEqual(result.report['status'], 'equivalent_under_model')
        self.assertEqual(result.report['profile']['state_bytes'], 32)
        self.assertEqual(result.solver_outputs[0]['stdout'].strip(), 'unsat')
        self.assertEqual(len(result.graph['source_outputs']), 5)
        json.dumps(result.graph)
        self.assertIn('(assert (or ', result.query)

    def test_different_cast_widths_yield_a_concrete_value_counterexample(self):
        result = self.compare('return (uint8_t)state[0];', 'return (uint16_t)nirvana_load(&m,address,8);')
        self.assertEqual(result.report['status'], 'counterexample_under_model')
        witness = result.report['witness']
        self.assertNotEqual(witness['source'][0], witness['generated'][0])
        self.assertEqual(witness['source'][1:], witness['generated'][1:])

    def test_missing_solver_stays_unknown_with_a_retained_query(self):
        result = self.compare('return state[0];', 'return nirvana_load(&m,address,8);', '/nonexistent/z3-state-values')
        self.assertEqual(result.report['status'], 'unknown')
        self.assertEqual(result.report['reason'], 'solver_unavailable')
        self.assertIsNone(result.report['witness'])
        self.assertTrue(result.query)

    def test_forward_cleanup_gotos_match_a_structured_continuation(self):
        a = ('uint64_t v;if(state[0]&1)goto fail;v=state[1]+state[2];state[2]=v;goto done;'
             'fail:state[0]|=2;done:state[3]+=state[2];return state[3];')
        b = ('uint64_t a=nirvana_load(&m,address,8);'
             'if(!(a&1))nirvana_store(&m,address+16,8,nirvana_load(&m,address+8,8)+nirvana_load(&m,address+16,8));'
             'else nirvana_store(&m,address,8,a|2);'
             'nirvana_store(&m,address+24,8,nirvana_load(&m,address+24,8)+nirvana_load(&m,address+16,8));'
             'return nirvana_load(&m,address+24,8);')
        result = self.compare(a,b)
        self.assertEqual(result.report['status'],'equivalent_under_model')
        self.assertEqual(result.report['model'],'nirvana-state4-values-v5')

    def test_loop_completion_is_proved_over_all_words_including_wraparound(self):
        a = ('while(1){++state[1];if(state[0]&1){state[2]=200;break;}'
             'if(state[1]>=3){state[2]=100;break;}}return state[2]+state[1];')
        b = ('uint64_t count=nirvana_load(&m,address+8,8)+1;'
             'uint64_t flag=nirvana_load(&m,address,8),result;'
             'if(flag&1)result=200;else{for(;count<=2;++count){}result=100;}'
             'nirvana_store(&m,address+8,8,count);nirvana_store(&m,address+16,8,result);return count+result;')
        result = self.compare(a,b)
        self.assertEqual(result.report['status'],'equivalent_under_model')
        self.assertEqual(result.report['profile']['completion'],'all-inputs')
        self.assertEqual(result.report['profile']['loop_iterations'],16)
        self.assertIn('source_incomplete',result.graph)
        self.assertIsNone(result.report['bound_witness'])

    def test_same_outputs_at_the_unroll_limit_do_not_establish_equivalence(self):
        for body in ['while(state[0])--state[0];return 0;', 'for(;;){}']:
            generated = body.replace('state[0]', 'counter')
            if 'counter' in generated: generated = 'uint64_t counter=nirvana_load(&m,address,8);'+generated
            result = self.compare(body,generated)
            self.assertEqual(result.report['status'],'unknown')
            self.assertEqual(result.report['reason'],'loop_bound_exhausted')
            self.assertIsNone(result.report['witness'])
            witness=result.report['bound_witness']
            self.assertTrue(any(witness['incomplete'].values()))
            if 'while' in body: self.assertGreater(witness['input_words'][0],16)

    def test_a_completed_loop_value_difference_yields_a_replayed_countermodel(self):
        result=self.compare('for(uint64_t i=0;i<4;++i)state[0]+=i;return state[0];',
                            'uint64_t value=nirvana_load(&m,address,8)+7;nirvana_store(&m,address,8,value);return value;')
        self.assertEqual(result.report['status'],'counterexample_under_model')
        self.assertIsNone(result.report['bound_witness'])

    def test_each_iteration_uses_its_current_index_and_byte_aliases(self):
        result=self.compare('for(uint64_t i=0;i<4;++i){state[i]+=i;state[3-i]^=state[i];}return state[0];',
                            'for(uint64_t index=0;index<4;++index){uint64_t offset=index*8;'
                            'uint64_t value=nirvana_load(&m,address+offset,8)+index;'
                            'nirvana_store(&m,address+offset,8,value);'
                            'nirvana_view_store(&m,nirvana_view_index(nirvana_location_address(address),3-index,8,0),8,'
                            'nirvana_load(&m,address+(3-index)*8,8)^value);}'
                            'return nirvana_load(&m,address,8);')
        self.assertEqual(result.report['status'],'equivalent_under_model')

    def test_signed_ranges_and_their_definedness_are_proved_without_assuming_the_intervals(self):
        a=('int32_t low=(uint8_t)state[0];int32_t product=(low-200)*3;'
           'state[1]=(uint64_t)(product/-7);state[2]=(uint64_t)(product%-7);'
           'return (uint64_t)(-product);')
        b=('int32_t low=(int32_t)(nirvana_load(&m,address,8)&255);int32_t negative=600-low*3;'
           'nirvana_store(&m,address+8,8,(uint64_t)(negative/7));'
           'nirvana_store(&m,address+16,8,(uint64_t)(-(negative%7)));return (uint64_t)negative;')
        result=self.compare(a,b)
        self.assertEqual(result.report['status'],'equivalent_under_model')
        self.assertEqual(result.report['profile']['definedness'],'all-modeled-values')
        self.assertTrue(result.graph['definedness'])
        self.assertIsNone(result.report['definedness_witness'])

    def test_a_rare_branch_countermodel_replays_in_actual_source_and_generated_c(self):
        compiler = shutil.which('cc')
        if not compiler: self.skipTest('requires C compiler')
        a = 'if(state[0]==UINT64_C(1311768467463790320))return 2;return state[1];'
        b = 'if(nirvana_load(&m,address,8)==UINT64_C(1311768467463790320))return 3;return nirvana_load(&m,address+8,8);'
        result = self.compare(a, b)
        self.assertEqual(result.report['status'], 'counterexample_under_model')
        witness = result.report['witness']
        self.assertEqual(witness['input_words'][0], 0x123456789abcdef0)
        runtime = '''
#include <stdlib.h>
uint64_t nirvana_load(struct nirvana_memory *m,uint64_t address,unsigned width) {
    if(address<m->base || width>8 || address-m->base>m->size-width)abort();
    uint64_t result=0;
    for(unsigned i=0;i<width;++i)result|=(uint64_t)m->bytes[address-m->base+i]<<(8*i);
    return result;
}
'''
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); source = root / 'both.c'; shared = root / 'both.so'
            source.write_text(HEADER + runtime + '\n'.join(self.sources(a, b)))
            subprocess.run([compiler, '-std=c11', '-O2', '-shared', '-fPIC', str(source), '-o', str(shared)],
                           check=True, capture_output=True, timeout=10)
            library = ctypes.CDLL(str(shared))
            original = library.fixture
            original.argtypes, original.restype = [ctypes.POINTER(ctypes.c_uint64)], ctypes.c_uint64
            generated = library.nirvana_readable
            generated.argtypes = [ctypes.c_uint64, ctypes.POINTER(ctypes.c_uint8), ctypes.c_uint64, ctypes.c_uint64]
            generated.restype = ctypes.c_uint64
            words = witness['input_words']
            state = (ctypes.c_uint64 * 4)(*words)
            memory = (ctypes.c_uint8 * 512)()
            for n, word in enumerate(words):
                for i, byte in enumerate(word.to_bytes(8, 'little')): memory[128+n*8+i] = byte
            self.assertEqual([original(state), *state], witness['source'])
            value = generated(4224, memory, 4096, 512)
            final = [int.from_bytes(bytes(memory[128+n*8:136+n*8]), 'little') for n in range(4)]
            self.assertEqual([value, *final], witness['generated'])
