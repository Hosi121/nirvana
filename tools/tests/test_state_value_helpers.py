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
from evaluation.state_values import helpers,division_abstraction
from evaluation.state_values.terms import Graph,Type,Node,Unsupported


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
            elif 'static inline int' in line and 'nirvana_signed' in line:
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
                function=getattr(library,name)
                function.restype=(getattr(ctypes,'c_int'+name[len('nirvana_signed'):])
                                 if name.startswith('nirvana_signed') else ctypes.c_uint64)
                function.argtypes=([ctypes.c_uint64,ctypes.c_int64,ctypes.c_uint]
                                   if name.endswith('_word') else [ctypes.c_uint64]* (2 if 'ashr' in name else 1))
            cls.libraries.append(library)

    def check(self,g,root,words,name,args):
        expected=[getattr(lib,name)(*args) for lib in self.libraries]
        self.assertEqual(expected[0],expected[1],(name,args))
        bits=g.type(root).bits;expected_bits=expected[0]%2**bits
        self.assertEqual(g.evaluate([root],words),[expected_bits],(name,args))
        return expected_bits

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
            for prefix in ['nirvana_sext','nirvana_signed']:
                g=Graph();name=f'{prefix}{bits}';root=helpers.lower(g,name,[g.inputs[0]])
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

    def test_signed_magnitude_interpretation_contains_every_native_byte_quotient_and_remainder(self):
        library=self.libraries[1]
        for divisor in range(-128,128):
            g=Graph();root=helpers.lower(g,'nirvana_sdiv_word',[g.inputs[0],g.const(divisor,Type(64,True)),g.const(8,Type(32))])
            node=next(n for n in g.nodes if n.op=='total_sdiv')
            _,bits,magnitude,negative=division_abstraction.operation(g,node)
            self.assertEqual((bits,magnitude,negative),(8,abs(divisor),divisor<0))
            for value in range(256):
                signed=value-256 if value>=128 else value
                q=(abs(signed)//magnitude if magnitude else 255)*(-1 if signed<0 else 1)
                quotient=(-q if negative else q)&255
                remainder=(value-q*magnitude)&255
                self.assertEqual(library.nirvana_sdiv_word(value,divisor,8),quotient)
                self.assertEqual(library.nirvana_srem_word(value,divisor,8),remainder)
                self.assertEqual(g.evaluate([root],[value,0,0,0]),[quotient])

    def test_normalization_matches_signed_quadrants_for_any_unsigned_quotient_function(self):
        # SMT-LIB defines signed division/remainder through four sign cases.
        # An arbitrary unsigned quotient is stronger than actual bvudiv; its
        # remainder uses n-q*d. Real division supplies one interpretation.
        solver=shutil.which(os.environ.get('NIRVANA_Z3','z3'))
        if not solver: self.skipTest('requires Z3')
        artifacts=Path(os.environ['NIRVANA_VALUE_PROOFS']) if 'NIRVANA_VALUE_PROOFS' in os.environ else None
        if artifacts: artifacts.mkdir(parents=True,exist_ok=True)
        proved=0
        for bits in [8,16,32,64]:
            g=Graph();unsigned=Type(bits);signed=Type(bits,True)
            u=g.cast(g.inputs[0],unsigned);a=g.intern(Node('bitcast',signed,(u,)))
            roots=[]
            for divisor in [0,1,-1,3,-31,-(1 << (bits-1)),(1 << (bits-1))-1]:
                for op in ['/','%']:
                    roots.extend([g.intern(Node(op,signed,(a,g.const(divisor,signed)))),
                                  g.intern(Node(op,unsigned,(u,g.const(divisor,unsigned))))])
                roots.append(g.intern(Node('total_sdiv',unsigned,(u,g.const(divisor,unsigned)))))
            bv=f'(_ BitVec {bits})';zero=f'(_ bv0 {bits})';q=f'quotient_unsigned_{bits}'
            positive=lambda n:f'(bvsge {n} {zero})'
            call=lambda x,y:f'({q} {x} {y})'
            rem=lambda x,y:f'(bvsub {x} (bvmul {call(x,y)} {y}))'
            def quadrants(operation,division):
                pp=operation('a','b');np=operation('(bvneg a)','b')
                pn=operation('a','(bvneg b)');nn=operation('(bvneg a)','(bvneg b)')
                if division: pn=f'(bvneg {pn})'
                else: nn=f'(bvneg {nn})'
                return f'(ite {positive("a")} (ite {positive("b")} {pp} {pn}) (ite {positive("b")} (bvneg {np}) {nn}))'
            definitions=(f'(declare-fun {q} ({bv} {bv}) {bv})\n'
                f'(define-fun quotient_signed_magnitude_{bits} ((a {bv}) (m {bv})) {bv} '
                f'(ite {positive("a")} ({q} a m) (bvneg ({q} (bvneg a) m))))\n'
                f'(define-fun reference_sdiv ((a {bv}) (b {bv})) {bv} {quadrants(call,True)})\n'
                f'(define-fun reference_srem ((a {bv}) (b {bv})) {bv} {quadrants(rem,False)})\n'
                f'(define-fun reference_udiv ((a {bv}) (b {bv})) {bv} {call("a","b")})\n'
                f'(define-fun reference_urem ((a {bv}) (b {bv})) {bv} {rem("a","b")})\n')
            exact=g.smt().replace('(set-logic QF_BV)','(set-logic QF_UFBV)\n'+definitions)
            for old,new in [('bvsdiv','reference_sdiv'),('bvsrem','reference_srem'),
                            ('bvudiv','reference_udiv'),('bvurem','reference_urem')]:
                exact=exact.replace('('+old+' ','('+new+' ')
            differences=[f'(distinct v{i} {division_abstraction.term(g,g.nodes[i])})' for i in roots]
            checks=[]
            for nonnegative in [False,True]:
                condition=f'(bvsge v{a} {zero})'
                if not nonnegative: condition=f'(not {condition})'
                for difference in differences:
                    checks.append(f'(push)\n(assert {condition})\n(assert {difference})\n(check-sat)\n(pop)\n')
            script='(set-option :timeout 1000)\n'+exact+''.join(checks)
            result=subprocess.run([solver,'-in'],input=script,capture_output=True,text=True,timeout=15)
            if artifacts:
                (artifacts/f'bits-{bits}.smt2').write_text(script)
                (artifacts/f'bits-{bits}.out').write_text(result.stdout)
            self.assertEqual((result.returncode,result.stdout.split()),(0,['unsat']*len(checks)),f'{bits}: {result.stderr}')
            proved+=len(checks)
        if artifacts:
            (artifacts/'result.json').write_text(json.dumps({'model':division_abstraction.MODEL,'unsat':proved,
                'interpretation':'arbitrary unsigned quotient; remainder n-q*d; all four signed quadrants'},indent=2)+'\n')
