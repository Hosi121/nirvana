"""Numeric ranges and C definedness have independent bit-vector checks."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest
from unittest import mock

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from evaluation.state_values.terms import Graph,Type,U64,BYTE,BOOL,Unsupported,number
from evaluation.state_values.ast import Model
from evaluation.state_values.solver import compare
from evaluation.state_values import definedness


class SignedRanges(unittest.TestCase):
    def test_ranges_admit_bounded_math_and_keep_unsafe_conversions_and_operations_out(self):
        g=Graph();signed=Type(32,True);low=g.cast(g.cast(g.inputs[0],BYTE),signed)
        delta=g.binary('-',low,g.const(200,signed),signed)
        self.assertEqual(g.bounds(delta),(-200,55))
        self.assertEqual(g.bounds(g.binary('/',delta,g.const(-3,signed),signed)),(-18,66))
        self.assertEqual(g.bounds(g.unary('-',delta,signed)),(-55,200))
        small=g.binary('&',delta,g.const(127,signed),signed)
        self.assertEqual(g.bounds(g.cast(small,Type(8,True))),(0,127))
        with self.assertRaises(Unsupported): g.cast(low,Type(8,True))
        high=g.cast(g.binary('&',g.inputs[0],g.const((1<<31)-1),U64),signed)
        with self.assertRaises(Unsupported): g.binary('+',high,g.const(1,signed),signed)
        with self.assertRaises(Unsupported): g.binary('<<',high,g.const(1),signed)
        negative=g.unary('~',low,signed)
        with self.assertRaises(Unsupported): g.binary('>>',negative,g.const(1),signed)


class CheckedRanges(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.solver=shutil.which(os.environ.get('NIRVANA_Z3','z3'))
        if not cls.solver: raise unittest.SkipTest('requires Z3')

    def test_informative_ranges_contain_all_smt_values_for_arbitrary_input_words(self):
        g=Graph();signed=Type(32,True)
        low=g.cast(g.cast(g.inputs[0],BYTE),signed)
        other=g.cast(g.cast(g.inputs[1],BYTE),signed)
        for op in ['+','-','*','&','|','^']:
            value=g.binary(op,low,other,signed)
            g.cast(value,U64)
            for divisor in [-7,-1,1,3]:
                for division in ['/','%']: g.binary(division,value,g.const(divisor,signed),signed)
        for bits in [8,16,32,64]:
            typ=Type(bits)
            a=g.cast(g.inputs[0],typ)
            g.binary('&',a,g.const(127,typ),typ)
            g.binary('+',a,g.const(255,typ),typ)
            g.binary('-',a,g.const(255,typ),typ)
            g.binary('>>',a,g.const(3),typ)
        for op in ['<<','>>']: g.binary(op,low,g.const(3),signed)
        g.unary('-',g.binary('-',low,g.const(200,signed),signed),signed)
        g.choose(g.truth(g.inputs[2]),low,g.unary('~',other,signed))
        differences=[];informative=0
        for i,n in enumerate(g.nodes):
            lo,hi=g.bounds(i)
            minimum=-(1 << (n.type.bits-1)) if n.type.signed else 0
            maximum=(1 << (n.type.bits-int(n.type.signed)))-1
            if (lo,hi)==(minimum,maximum): continue
            informative+=1
            literal=lambda v:f'(_ bv{v%2**n.type.bits} {n.type.bits})'
            lt,gt=('bvslt','bvsgt') if n.type.signed else ('bvult','bvugt')
            differences.append(f'(or ({lt} v{i} {literal(lo)}) ({gt} v{i} {literal(hi)}))')
        self.assertGreater(informative,50)
        differences.extend(f'(not {predicate})' for _,predicate in definedness.predicates(g))
        script=g.smt()+'(assert (or '+' '.join(differences)+'))\n(check-sat)\n'
        result=subprocess.run([self.solver,'-in','-smt2'],input=script,capture_output=True,text=True,timeout=20)
        self.assertEqual(result.returncode,0,result.stderr or result.stdout)
        self.assertEqual(result.stdout.strip(),'unsat')

    def test_an_unsound_interval_proposal_cannot_turn_undefined_math_into_equivalence(self):
        for operation in ['cast','+','-','*','neg','/','%','<<','>>']:
            with self.subTest(operation=operation):
                g=Graph();signed=Type(32,True)
                positive=g.cast(g.binary('&',g.inputs[0],g.const((1<<31)-1),U64),signed)
                extreme=g.choose(g.truth(g.inputs[1]),g.const(-(1<<31),signed),g.const(0,signed))
                negative=g.unary('~',g.cast(g.cast(g.inputs[0],BYTE),signed),signed)
                with mock.patch.object(g,'bounds',return_value=(0,0)):
                    if operation=='cast': bad=g.cast(g.inputs[0],signed)
                    elif operation=='neg': bad=g.unary('-',extreme,signed)
                    elif operation in ['/','%']: bad=g.binary(operation,extreme,g.const(-1,signed),signed)
                    elif operation=='>>': bad=g.binary(operation,negative,g.const(1),signed)
                    else: bad=g.binary(operation,positive,g.const(-1 if operation=='-' else 2 if operation=='*' else 1,signed),signed)
                value=g.cast(bad,U64);model=Model([value,*g.inputs],1,0,0,g.const(0,BOOL))
                proof=compare(g,model,model,self.solver)
                self.assertEqual(proof.status,'unknown')
                self.assertEqual(proof.reason,'definedness_not_established')
                self.assertIn(bad,proof.definedness_witness['value_ids'])
                self.assertIsNone(proof.witness)
                self.assertIsNone(proof.bound_witness)
