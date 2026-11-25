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
        self.assert_native_bodies(bodies)

    def assert_native_bodies(self, bodies):
        compiler = shutil.which('cc')
        if not compiler: self.skipTest('requires C compiler')
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

    def test_scoped_forward_labels_and_outer_loop_headers_match_native_c(self):
        self.assert_native_bodies([
            '{uint64_t saved=state[0];if(state[1]&1)goto local;state[0]+=7;'
            'local:state[2]=saved;}return state[0]^state[2];',
            'for(uint64_t i=0;i<(state[0]&1)+2;++i){for(uint64_t j=0;j<3;++j){'
            'state[1]+=i*4+j;if(state[2]&1)goto tail;state[3]++;}'
            'state[3]+=100;tail:state[3]+=i+1;}return state[1]^state[3];',
            'uint64_t saved=state[1];for(uint64_t i=0;i<3;++i){for(uint64_t j=0;j<2;++j){'
            'state[0]+=i+j;if(state[2]&1)goto cleanup;state[1]++;}state[3]++;}'
            'cleanup:state[2]=saved;return state[0]+state[1];',
            'for(uint64_t i=0;i<4;++i){if((state[0]>>i)&1)goto select;state[1]+=10;'
            'select:if(i==1)continue;if(i==3)break;state[2]+=i;}return state[1]+state[2];',
            'uint64_t i=0;do{++i;{if(state[0]&1)goto step;state[1]+=9;'
            'step:state[2]+=i;}if(i==2)continue;state[3]+=i;}while(i<4);return state[2]+state[3];',
            'uint64_t i=0;while(i<3){++i;if(state[0]&1)goto end;state[1]+=i;'
            'end:if(i==2)continue;state[2]+=i;}return state[1]+state[2];',
            'uint64_t i=0;again:;for(;i<4;){++i;for(uint64_t j=0;j<2;++j){'
            'state[1]+=i+j;if(state[0]&1)goto again;}state[2]+=i;}return state[1]^state[2];',
            'uint64_t x=state[0];{uint64_t x=state[1];if(state[2]&1)goto inner;'
            'x+=3;inner:state[3]=x;}return x^state[3];',
            'if(state[0]&1)goto set;uint64_t x=3;set:x=state[1];return x;',
        ])

    def test_persistent_storage_is_not_treated_as_fresh_automatic_state(self):
        for body in ['static uint64_t count=0;++count;state[0]=count;return count;',
                     'extern uint64_t shared;return shared;']:
            with self.subTest(body=body), self.assertRaisesRegex(Unsupported, 'automatic local'):
                self.model(Graph(), body)

    def test_skipped_initializers_cannot_reuse_prior_activation_values(self):
        for body in [
            'for(uint64_t i=0;i<2;++i){if(i)goto use;uint64_t x=state[0];'
            'use:state[1]=x;}return state[1];',
            'if(state[0]&1)goto use;uint64_t x=state[1];use:return x;',
        ]:
            with self.subTest(body=body), self.assertRaisesRegex(Unsupported, 'defined local value'):
                self.model(Graph(), body)
        body = ('for(uint64_t i=0;i<2;++i){if(i)goto use;'
                'const struct {struct nirvana_view saved;} v={{address}};'
                'use:nirvana_store(&m,address+8,8,nirvana_view_load(&m,v.saved,8));}return 0;')
        with self.assertRaises(Unsupported): self.model(Graph(), body, source=False)

    def test_other_backward_jumps_loop_entries_and_vlas_remain_unsupported(self):
        bodies = [
            'uint64_t i=0;again:;for(;i<3;++i){if(state[0]&1)goto again;}return i;',
            'uint64_t i=0;again:;for(i=0;i<3;){++i;if(state[0]&1)goto again;}return i;',
            'uint64_t i=0;again:;for(;i<3;){++i;}if(state[0]&1)goto again;return i;',
            'if(state[0]&1)goto inside;for(uint64_t i=0;i<2;++i){inside:state[1]++;}return state[1];',
            'if(state[0]&1)goto inside;{inside:state[1]++;}return state[1];',
            '{inside:state[1]++;}{if(state[0]&1)goto inside;}return state[1];',
            'uint64_t n=(state[0]&3)+1;uint64_t a[n];return state[1];',
        ]
        for body in bodies:
            with self.subTest(body=body), self.assertRaises(Unsupported): self.model(Graph(), body)

    def test_context_initialization_is_path_local_and_fresh_each_activation(self):
        code = ('uint64_t nirvana_readable(uint64_t address,uint8_t *memory,uint64_t base,uint64_t size){'
                'struct nirvana_memory initial={memory,base,size};'
                'if(nirvana_load(&initial,address,8)&1)goto use;struct nirvana_memory m={memory,base,size};'
                'use:return nirvana_load(&m,address,8);}')
        with self.assertRaisesRegex(Unsupported, 'context differs'):
            observe(Graph(), self.ast(code, 'nirvana_readable'), 'nirvana_readable', source=False)
        code = ('uint64_t nirvana_readable(uint64_t address,uint8_t *memory,uint64_t base,uint64_t size){'
                'for(uint64_t i=0;i<2;++i){if(i)goto use;struct nirvana_memory m={memory,base,size};'
                'use:(void)nirvana_load(&m,address,8);}return 0;}')
        with self.assertRaisesRegex(Unsupported, 'context differs'):
            observe(Graph(), self.ast(code, 'nirvana_readable'), 'nirvana_readable', source=False)

    def test_label_joins_keep_mixed_partial_and_unaligned_byte_origins(self):
        g=Graph()
        source=self.model(g,'uint64_t flag=state[3]&1;if(flag){'
            'state[0]=(state[0]&~UINT64_C(65280))|UINT64_C(43520);'
            'state[1]=(state[1]&~UINT64_C(255))|UINT64_C(18);'
            'state[0]=(state[0]&UINT64_C(72057594037927935))|UINT64_C(3746994889972252672);'
            '}else state[0]^=255;state[2]=state[0]^state[1];return state[2];')
        generated=self.model(g,'if(nirvana_load(&m,address+24,8)&1)goto write;'
            'nirvana_store(&m,address,8,nirvana_load(&m,address,8)^255);goto done;'
            'write:nirvana_store(&m,address+1,1,170);nirvana_store(&m,address+7,2,0x1234);'
            'done:nirvana_store(&m,address+16,8,nirvana_load(&m,address,8)^nirvana_load(&m,address+8,8));'
            'return nirvana_load(&m,address+16,8);',source=False)
        for flag in [0,1]:
            for words in [[0,0,0,flag],[2**64-1,0x8877665544332211,3,flag]]:
                self.assertEqual(g.evaluate(source.outputs,words),g.evaluate(generated.outputs,words))

    def test_forward_label_joins_preserve_captured_record_addresses(self):
        g=Graph();model=self.model(g,'uint64_t flag=nirvana_load(&m,address+24,8)&1;'
            'uint64_t sum=0;for(uint64_t i=0;i<2;++i){'
            'const struct {struct nirvana_view saved;} v={{address+i*8}};'
            'if(flag)goto use;nirvana_store(&m,address+16,8,99);'
            'use:sum+=nirvana_view_load(&m,v.saved,8);}return sum;',source=False)
        for flag in [0,1]:
            self.assertEqual(g.evaluate(model.outputs,[11,22,33,flag]),[33,11,22,33 if flag else 99,flag])

    def test_current_indices_do_not_re_evaluate_captured_view_initializers(self):
        body=('uint64_t i=0;const struct {struct nirvana_view saved;} v={{address+i*8}};'
              '++i;return nirvana_view_load(&m,v.saved,8);')
        g=Graph();captured=self.model(g,body,source=False)
        self.assertEqual(g.evaluate(captured.outputs,[11,22,33,44]),[11,11,22,33,44])
        for body in ['uint64_t i=4;return state[i];','int i=-1;return state[i];',
                     'return *(state+100-100);','return *(state-1+1);']:
            with self.assertRaises(Unsupported): self.model(Graph(),body)
        model=self.model(Graph(),'return *(state+4-4);')  # A one-past pointer may move back.
        self.assertEqual(model.paths,1)

    def test_loop_record_and_scalar_address_declarations_capture_each_iteration(self):
        bodies=[
            'uint64_t sum=0;for(uint64_t i=0;i<4;){'
            'const struct {struct nirvana_view saved;} v={{address+i*8}};'
            '++i;sum+=nirvana_view_load(&m,v.saved,8);}return sum;',
            'uint64_t sum=0;for(uint64_t i=0;i<4;){uint64_t saved=address+i*8;'
            '++i;sum+=nirvana_load(&m,saved,8);}return sum;',
            'uint64_t i=0;const struct {struct nirvana_view saved;} original={{address+i*8}};'
            'const struct {struct nirvana_view saved;} copy={original.saved};'
            'i=3;return nirvana_view_load(&m,copy.saved,8);',
        ]
        for body,expected in zip(bodies,[110,110,11]):
            g=Graph();model=self.model(g,body,source=False)
            self.assertEqual(g.evaluate(model.outputs,[11,22,33,44]),[expected,11,22,33,44])

    def test_signed_helper_call_is_lowered_under_an_explicit_runtime_contract(self):
        g=Graph()
        source=self.model(g,'uint64_t low=state[0]&65535;return low<32768?low:low-UINT64_C(65536);')
        code=('uint64_t nirvana_sext16(uint64_t);'
              'uint64_t nirvana_readable(uint64_t address,uint8_t *memory,uint64_t base,uint64_t size)'
              '{struct nirvana_memory m={memory,base,size};return nirvana_sext16(nirvana_load(&m,address,8));}')
        generated=observe(g,self.ast(code,'nirvana_readable'),'nirvana_readable',source=False)
        for value in [0,32767,32768,65535,2**64-1]:
            self.assertEqual(g.evaluate(source.outputs,[value,1,2,3]),g.evaluate(generated.outputs,[value,1,2,3]))
