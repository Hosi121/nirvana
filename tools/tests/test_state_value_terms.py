import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation.state_values.terms import Graph, Node, Type, U64, BYTE, BOOL, Unsupported


class ValueTerms(unittest.TestCase):
    def test_casts_keep_signed_extension_truncation_and_boolean_values(self):
        g = Graph()
        for value in [-128, -1, 0, 1, 127]:
            narrow = g.const(value, Type(8, True))
            wide = g.cast(narrow, U64)
            self.assertEqual(g.evaluate([wide], [0] * 4), [value % 2**64])
        low = g.cast(g.inputs[0], BYTE)
        boolean = g.cast(low, BOOL)
        for value in range(512):
            self.assertEqual(g.evaluate([low, boolean], [value, 0, 0, 0]), [value % 256, int(value % 256 != 0)])

    def test_unknown_c_overflow_conversions_divisors_and_shifts_are_rejected(self):
        g = Graph()
        for op in ['/', '%']:
            with self.assertRaises(Unsupported): g.binary(op, g.inputs[0], g.const(0), U64)
            with self.assertRaises(Unsupported): g.binary(op, g.inputs[0], g.inputs[1], U64)
            with self.assertRaises(Unsupported):
                g.binary(op, g.const(-(1 << 31), Type(32, True)), g.const(-1, Type(32, True)), Type(32, True))
        with self.assertRaises(Unsupported): g.cast(g.inputs[0], Type(64, True))
        signed = g.cast(g.cast(g.inputs[0], BYTE), Type(32, True))
        with self.assertRaises(Unsupported): g.binary('+', signed, g.const(1, Type(32, True)), Type(32, True))
        for count in [64, 65, (1 << 64) - 1]:
            with self.assertRaises(Unsupported): g.binary('<<', g.inputs[0], g.const(count), U64)
        with self.assertRaises(Unsupported): g.binary('>>', g.inputs[0], g.inputs[1], U64)

    def test_partial_load_and_store_bytes_keep_little_endian_aliases(self):
        g = Graph()
        memory = [g.extract(g.inputs[n // 8], n % 8 * 8) for n in range(32)]
        memory[7:11] = [g.const(v, BYTE) for v in [0x11, 0x22, 0x33, 0x44]]
        roots = [g.pack(memory[:8]), g.pack(memory[8:16])]
        values = [0x8877665544332211, 0xffeeddccbbaa9988, 0, 0]
        self.assertEqual(g.evaluate(roots, values), [0x1177665544332211, 0xffeeddccbb443322])
        self.assertEqual(g.cast(g.inputs[0], U64), g.inputs[0])
        self.assertEqual(g.choose(g.const(1, BOOL), *roots), roots[0])

    def test_budgets_reject_whole_graph_growth(self):
        g = Graph()
        with self.assertRaisesRegex(Unsupported, 'budget'):
            for n in range(4097): g.const(n)


class SolverValueTerms(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.solver = shutil.which(os.environ.get('NIRVANA_Z3', 'z3'))
        if not cls.solver: raise unittest.SkipTest('requires Z3; set NIRVANA_Z3')

    def check(self, script):
        result = subprocess.run([self.solver, '-in', '-smt2'], input=script + '(check-sat)\n',
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr or result.stdout)
        self.assertEqual(result.stdout.strip(), 'unsat')

    def test_symbolic_cast_and_u64_wrap_identities(self):
        g = Graph()
        x = g.inputs[0]
        low = g.cast(g.cast(x, BYTE), U64)
        masked = g.binary('&', x, g.const(255), U64)
        plus = g.binary('+', x, g.const(2**64 - 1), U64)
        minus = g.binary('-', x, g.const(1), U64)
        parts = tuple(g.extract(x, n * 8) for n in range(8))
        packed = g.intern(Node('pack', U64, parts))  # Bypass normalization in the oracle.
        self.assertEqual(g.pack(parts), x)
        self.check(g.smt() + f'(assert (or (distinct v{low} v{masked}) (distinct v{plus} v{minus}) (distinct v{packed} v{x})))\n')

    def test_concrete_semantics_and_smt_agree_across_widths_and_signs(self):
        g = Graph(); roots = []
        for bits in [8, 16, 32, 64]:
            typ = Type(bits)
            a, b = [g.cast(x, typ) for x in g.inputs[:2]]
            for op in ['+', '-', '*', '&', '|', '^', '==', '!=', '<', '<=', '>', '>=']:
                roots.append(g.binary(op, a, b, BOOL if op in ['==', '!=', '<', '<=', '>', '>='] else typ))
            roots.extend(g.binary(op, a, g.const(3, typ), typ) for op in ['/', '%', '<<', '>>'])
        signed = g.unary('~', g.cast(g.cast(g.inputs[0], Type(32)), Type(64, True)), Type(64, True))
        roots.extend([signed, g.binary('<', signed, g.const(0, Type(64, True)), BOOL)])
        for inputs in [[0, 1, 2, 3], [2**64 - 1, 0, 0, 0], [1 << 63, 2**32 + 17, 0, 0], [255, 256, 0, 0]]:
            fixed = ''.join(f'(assert (= word{i} (_ bv{v} 64)))\n' for i, v in enumerate(inputs))
            expected = g.evaluate(roots, inputs)
            difference = ' '.join(f'(distinct v{r} (_ bv{value} {g.type(r).bits}))' for r, value in zip(roots, expected))
            self.check(g.smt() + fixed + f'(assert (or {difference}))\n')
