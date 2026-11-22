"""C storage snapshots and byte aliases are checked against native C separately."""
import ctypes
import os
from pathlib import Path
import random
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation.state_values.terms import Graph, Unsupported
from evaluation.state_values.ast import observe
from test_state_memory import HEADER


class StateValueAST(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.clang = shutil.which(os.environ.get('NIRVANA_CLANG', 'clang'))
        if not cls.clang: raise unittest.SkipTest('requires Clang 18; set NIRVANA_CLANG')

    def ast(self, source, name):
        result = subprocess.run([self.clang, '-std=c11', '-Werror', '-fsyntax-only', '-Xclang',
                                 '-ast-dump=json', '-Xclang', '-ast-dump-filter=' + name, '-x', 'c', '-'],
                                input=HEADER + source, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def model(self, graph, body, *, source=True, context='memory,base,size'):
        if source:
            code = 'uint64_t fixture(uint64_t *state){' + body + '}'
            return observe(graph, self.ast(code, 'fixture'), 'fixture')
        code = ('uint64_t nirvana_readable(uint64_t address,uint8_t *memory,uint64_t base,uint64_t size)'
                '{struct nirvana_memory m={' + context + '};' + body + '}')
        return observe(graph, self.ast(code, 'nirvana_readable'), 'nirvana_readable', source=False)

    def test_snapshots_follow_values_across_aliasing_source_updates(self):
        g = Graph()
        a = self.model(g, 'uint64_t old=state[0];state[0]+=7;state[1]=old;return old^state[0];')
        b = self.model(g, 'uint64_t x=nirvana_load(&m,address,8);'
                         'nirvana_store(&m,address,8,x+7);nirvana_store(&m,address+8,8,x);'
                         'return x^nirvana_load(&m,address,8);', source=False)
        for x in [0, 1, 2**64 - 1, 1 << 63]:
            expected = [(x ^ ((x + 7) % 2**64)), (x + 7) % 2**64, x, 3, 4]
            self.assertEqual(g.evaluate(a.outputs, [x, 2, 3, 4]), expected)
            self.assertEqual(g.evaluate(b.outputs, [x, 2, 3, 4]), expected)

    def test_partial_stores_match_masked_words_and_opaque_view_spellings(self):
        g = Graph()
        a = self.model(g, 'state[0]=(state[0]&~UINT64_C(65280))|UINT64_C(768);return state[0];')
        b = self.model(g, 'const struct {struct nirvana_view field_999;} v={{address+1}};'
                         'nirvana_view_store(&m,v.field_999,1,3);return nirvana_load(&m,address,8);', source=False)
        for x in [0, 0xffff, 2**64 - 1, 0x8877665544332211]:
            self.assertEqual(g.evaluate(a.outputs, [x, 2, 3, 4]), g.evaluate(b.outputs, [x, 2, 3, 4]))

    def test_uninitialized_values_unknown_effects_control_and_addresses_are_rejected(self):
        for body in ['uint64_t x;return x;', 'return opaque(state[0]);', 'switch(state[0]){case 1:return 1;}return 0;',
                     'again:if(state[0]){--state[0];goto again;}return state[0];',
                     'if(state[0]){inside:state[1]++;}if(state[2])goto inside;return state[1];',
                     'return state[state[0]&3];', 'return state[4];',
                     'int64_t x=(int64_t)state[0];return (uint64_t)(x+1);']:
            with self.subTest(body=body), self.assertRaises(Unsupported): self.model(Graph(), body)

    def test_context_mutation_and_unused_faulting_record_setup_are_not_ignored(self):
        for body in ['m.base=0;return nirvana_load(&m,address,8);',
                     'const struct {struct nirvana_view field;} v={{nirvana_load(&m,address-4096,8)}};return 0;',
                     'return *(uint64_t*)(memory+128);']:
            with self.subTest(body=body), self.assertRaises(Unsupported): self.model(Graph(), body, source=False)
        with self.assertRaises(Unsupported):
            self.model(Graph(), 'return nirvana_load(&m,address,8);', source=False, context='memory,size,base')

    def test_generic_conversions_use_only_the_selected_location_adapter(self):
        g = Graph()
        body = ('const struct {struct nirvana_view strange;} v={{address+16}};'
                'return nirvana_view_load(&m,_Generic(v.strange,struct nirvana_view:nirvana_location_view,'
                'default:nirvana_location_address)(v.strange),8);')
        model = self.model(g, body, source=False)
        self.assertEqual(g.evaluate(model.outputs, [1, 2, 3, 4]), [3, 1, 2, 3, 4])

    def test_source_models_match_native_c_across_widths_paths_and_snapshots(self):
        compiler = shutil.which('cc')
        if not compiler: self.skipTest('requires C compiler')
        bodies = [
            'uint8_t low=(uint8_t)state[0];uint64_t old=state[1];state[2]=old+(uint64_t)low;'
            'if(low&1){state[0]^=state[2];return state[0];}state[1]+=state[3];return state[2];',
            'const int8_t n=-1;state[3]=(uint64_t)n;return state[0]+state[3];',
            'if(state[0]&1)state[1]+=state[2];else state[2]^=state[3];return state[1]+state[2];',
            'state[0]=(state[0]&~UINT64_C(65280))|UINT64_C(768);return state[0];',
            'uint64_t v;if(state[0]&1)goto fail;v=state[1]+state[2];state[2]=v;goto done;'
            'fail:state[0]|=2;done:state[3]+=state[2];return state[3];',
            'while(1){++state[1];if(state[0]&1){state[2]=200;break;}'
            'if(state[1]>=3){state[2]=100;break;}}return state[2]+state[1];',
            'for(uint64_t i=0;i<16;++i){uint64_t snapshot=state[0];state[0]+=i;state[1]^=snapshot;}return state[1];',
            'uint64_t i=0;do{++i;if(i==2)continue;state[2]+=i;}while(i<4);return state[2];',
            'for(uint64_t i=0;i<3;++i){for(uint64_t j=0;j<4;++j){'
            'if(j==1)continue;if(i==2)break;state[0]+=i+j;}}return state[0];',
            'for(uint64_t i=0;i<4;++i){uint64_t old=state[i];state[3-i]^=old+i;state[i]+=i;}return state[0]+state[3];',
            'int32_t low=(uint8_t)state[0];int32_t product=(low-200)*3;'
            'int8_t small=(int8_t)(low&127);state[1]=(uint64_t)(product/-7);'
            'state[2]=(uint64_t)(product%-7);state[3]=(uint64_t)(low<<3);'
            'return (uint64_t)(-product)+(uint64_t)small;',
        ]
        rng = random.Random(17)
        vectors = [[0]*4, [2**64-1]*4, [1<<63,1,2,3], [1,2,3,4]] + [[rng.getrandbits(64) for _ in range(4)] for _ in range(16)]
        for body in bodies:
            g = Graph(); model = self.model(g, body)
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory); source = root / 'input.c'; library = root / 'oracle.so'
                source.write_text('#include <stdint.h>\nuint64_t fixture(uint64_t *state){' + body + '}')
                subprocess.run([compiler, '-std=c11', '-O2', '-shared', '-fPIC', str(source), '-o', str(library)],
                               check=True, capture_output=True, timeout=10)
                function = ctypes.CDLL(str(library)).fixture
                function.argtypes = [ctypes.POINTER(ctypes.c_uint64)]
                function.restype = ctypes.c_uint64
                for words in vectors:
                    state = (ctypes.c_uint64 * 4)(*words)
                    value = function(state)
                    self.assertEqual(g.evaluate(model.outputs, words), [value, *state], body)
                    self.assertEqual(g.evaluate([model.incomplete], words), [0], body)

    def test_current_indices_do_not_re_evaluate_captured_view_initializers(self):
        body=('uint64_t i=0;const struct {struct nirvana_view saved;} v={{address+i*8}};'
              '++i;return nirvana_view_load(&m,v.saved,8);')
        with self.assertRaises(Unsupported): self.model(Graph(),body,source=False)
        for body in ['uint64_t i=4;return state[i];','int i=-1;return state[i];',
                     'return *(state+100-100);','return *(state-1+1);']:
            with self.assertRaises(Unsupported): self.model(Graph(),body)
        model=self.model(Graph(),'return *(state+4-4);')  # A one-past pointer may move back.
        self.assertEqual(model.paths,1)
