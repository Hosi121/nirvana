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
