"""Generated helper contracts agree with the actual portable C implementations."""
import ctypes
import json
import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tools'))
from evaluation.state_values import helpers
from evaluation.state_values.terms import Graph,Type,Unsupported


class IntegerHelperContracts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cc=shutil.which('cc')
        if not cc: raise unittest.SkipTest('requires C compiler')
        cls.directory=tempfile.TemporaryDirectory(prefix='nirvana-helper-model-')
        cls.addClassCleanup(cls.directory.cleanup)
        integer=(ROOT/'src/codegen/emit/integer.rs').read_text()
        word=(ROOT/'src/transform/word_signed_division.rs').read_text()
        definitions=[]
        for name,text in [('SHIFT_HELPER',integer),('DIVIDE_HELPER',word),('REMAINDER_HELPER',word)]:
            definitions.append(re.search(r'const '+name+r': &str = r#"(.*?)"#;',text,re.S)[1])
        for line in integer.splitlines():
            if 'static inline uint64_t nirvana_sext' in line:
                definitions.append(json.loads(line.strip().removesuffix(',')))
        wrappers='\n'.join(definitions).replace('static inline ','')
        source=Path(cls.directory.name)/'helpers.c'
        source.write_text('#include <stdint.h>\n'+wrappers)
        cls.libraries=[]
        for opt in ['-O0','-O2']:
            output=source.with_name('helpers'+opt+'.so')
            subprocess.run([cc,'-std=c11',opt,'-shared','-fPIC','-fsanitize=undefined',
                            '-fno-sanitize-recover=all',str(source),'-o',str(output)],
                           check=True,capture_output=True,timeout=15)
            library=ctypes.CDLL(str(output))
            for name in helpers.NAMES:
                function=getattr(library,name);function.restype=ctypes.c_uint64
                function.argtypes=([ctypes.c_uint64,ctypes.c_int64,ctypes.c_uint]
                                   if name.endswith('_word') else [ctypes.c_uint64]* (2 if 'ashr' in name else 1))
            cls.libraries.append(library)

    def check(self,g,root,words,name,args):
        expected=[getattr(lib,name)(*args) for lib in self.libraries]
        self.assertEqual(expected[0],expected[1],(name,args))
        self.assertEqual(g.evaluate([root],words),expected[:1],(name,args))
        return expected[0]

    def test_signed_word_division_preserves_full_divisor_and_total_edge_cases(self):
        rng=random.Random(301)
        for bits in [8,16,32]:
            divisors=[0,1,-1,3,-7,-31,2**(bits-1),-2**(bits-1),2**bits-1,
                      2**bits, -(2**bits),2**63-1,-2**63]
            values=[0,1,2**bits-1,2**(bits-1),2**(bits-1)-1,2**64-1]+[rng.getrandbits(64) for _ in range(12)]
            if bits==8: values+=list(range(256))
            for divisor in divisors:
                g=Graph();args=[g.inputs[0],g.const(divisor,Type(64,True)),g.const(bits,Type(32))]
                roots=[helpers.lower(g,name,args) for name in ['nirvana_sdiv_word','nirvana_srem_word']]
                for value in values:
                    for name,root in zip(['nirvana_sdiv_word','nirvana_srem_word'],roots):
                        self.check(g,root,[value,0,0,0],name,[value,divisor,bits])

    def test_extensions_and_shift_counts_match_c_including_count_wrapping(self):
        values=[0,1,127,128,255,32768,2**31,2**63,2**64-1,0x8877665544332211]
        for bits in [8,16,32]:
            g=Graph();name=f'nirvana_sext{bits}';root=helpers.lower(g,name,[g.inputs[0]])
            for value in values: self.check(g,root,[value,0,0,0],name,[value])
        g=Graph();root=helpers.lower(g,'nirvana_ashr64',g.inputs[:2])
        for count in [*range(130),2**63,2**64-1]:
            for value in values: self.check(g,root,[value,count,0,0],'nirvana_ashr64',[value,count])

    def test_smt_and_concrete_model_share_actual_native_results(self):
        solver=shutil.which(os.environ.get('NIRVANA_Z3','z3'))
        if not solver: self.skipTest('requires Z3')
        g=Graph();checks=[]
        values=[0,1,128,2**31,2**63,2**64-1]
        for bits in [8,16,32]:
            for value in values:
                for divisor in [0,-1,-31,2**bits,-2**63]:
                    for name in ['nirvana_sdiv_word','nirvana_srem_word']:
                        root=helpers.lower(g,name,[g.const(value),g.const(divisor,Type(64,True)),g.const(bits,Type(32))])
                        expected=self.check(g,root,[0]*4,name,[value,divisor,bits])
                        checks.append(f'(distinct v{root} (_ bv{expected} 64))')
        for value in values:
            for count in [0,1,63,64,65,2**64-1]:
                root=helpers.lower(g,'nirvana_ashr64',[g.const(value),g.const(count)])
                expected=self.check(g,root,[0]*4,'nirvana_ashr64',[value,count])
                checks.append(f'(distinct v{root} (_ bv{expected} 64))')
        result=subprocess.run([solver,'-in'],input=g.smt()+'(assert (or '+' '.join(checks)+'))\n(check-sat)\n',
                              capture_output=True,text=True,timeout=15)
        self.assertEqual((result.returncode,result.stdout.strip()),(0,'unsat'),result.stderr)

    def test_contract_rejects_unmodeled_signatures(self):
        for name,args in [('nirvana_sext8',[]),('nirvana_ashr64',[0]),
                          ('nirvana_sdiv_word',[0,0,64]),('unknown',[])]:
            g=Graph()
            with self.assertRaises(Unsupported): helpers.lower(g,name,[g.const(n) for n in args])
