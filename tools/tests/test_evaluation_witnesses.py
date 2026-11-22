"""Optional compiled witness-probe checks; set NIRVANA_WITNESS_PROBE and NIRVANA_Z3."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class PathInputs(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        helper = os.environ.get('NIRVANA_WITNESS_PROBE')
        solver = os.environ.get('NIRVANA_Z3')
        cls.cc = shutil.which('cc')
        if not helper or not solver or not cls.cc:
            raise unittest.SkipTest('requires built path probe, Z3 and C compiler')
        cls.helper, cls.solver = str(Path(helper).resolve()), str(Path(solver).resolve())

    def prepare(self, root, *, debug=False, nonreturning=False):
        source = root / 'rare.c'
        source.write_text('''#include <stdint.h>
uint64_t fixture(uint64_t r[4]) {
    if (r[0] == UINT64_C(0x123456789abcdef0)) {
        r[1] = r[2] + 7;
        r[3] += r[1];
    } else r[1] ^= r[3];
    return r[1] + r[3];
}
''')
        if nonreturning:
            source.write_text('''#include <stdint.h>
uint64_t fixture(uint64_t r[4]) {
    if (r[0] == UINT64_C(0x123456789abcdef0))
        while (1) ++*(volatile uint64_t *)&r[1];
    return r[1];
}
''')
        obj = root / 'rare.o'
        subprocess.run([self.cc, '-std=c11', '-O2', *(['-g'] if debug else []),
                        '-c', str(source), '-o', str(obj)], check=True, capture_output=True)
        inputs = root / 'seeds.txt'
        inputs.write_text('0 1 2 3\n')
        return obj, inputs

    def run_probe(self, root, *, solver=None, steps=4096, debug=False, nonreturning=False):
        obj, inputs = self.prepare(root, debug=debug, nonreturning=nonreturning)
        out = root / 'output'
        result = subprocess.run([self.helper, str(obj), str(inputs), str(out), '64', '2000', str(steps)],
                                env=dict(os.environ, NIRVANA_Z3=solver or self.solver),
                                capture_output=True, text=True, timeout=30)
        return result, out

    def test_rare_branch_adds_a_replayed_input_and_binds_artifacts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            result, out = self.run_probe(root)
            self.assertEqual(result.returncode, 0, result.stderr)
            report = json.loads((out / 'report.json').read_text())
            self.assertGreater(report['observed_after'], report['observed_before'])
            self.assertEqual(report['output_vectors'], 2)
            vectors = [[int(v) for v in line.split()] for line in (out / 'inputs.txt').read_text().splitlines()]
            self.assertEqual(vectors[0], [0, 1, 2, 3])
            self.assertEqual(vectors[1][0], 0x123456789abcdef0)
            self.assertEqual((out / 'input.o').read_bytes(), (root / 'rare.o').read_bytes())
            self.assertEqual((out / 'seed-inputs.txt').read_bytes(), (root / 'seeds.txt').read_bytes())
            self.assertTrue(any(q['status'] == 'replayed_witness' for q in report['queries']))
            self.assertTrue(list(out.glob('query-*.smt2')))

    def test_missing_solver_and_execution_budget_stay_unproved(self):
        for missing_solver in [False, True]:
            with self.subTest(missing_solver=missing_solver), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                result, out = self.run_probe(root, solver=str(root / 'missing-z3') if missing_solver else None,
                                             steps=4096 if missing_solver else 1)
                self.assertEqual(result.returncode, 0, result.stderr)
                report = json.loads((out / 'report.json').read_text())
                self.assertEqual(report['output_vectors'], 1)
                self.assertTrue(report['remaining'])
                self.assertTrue(all(e['status'] == 'not_proved' for e in report['edges']))
                self.assertTrue(all(q['status'] == 'unknown' for q in report['queries']))

    def test_debug_objects_are_rejected_before_producing_output(self):
        with tempfile.TemporaryDirectory() as directory:
            result, out = self.run_probe(Path(directory), debug=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('nondebug', result.stderr)
            self.assertFalse(out.exists())

    def test_prefix_witness_without_a_return_is_excluded_from_native_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            result, out = self.run_probe(Path(directory), steps=200, nonreturning=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            report = json.loads((out / 'report.json').read_text())
            self.assertEqual(report['output_vectors'], 1)
            self.assertEqual((out / 'inputs.txt').read_text(), '0 1 2 3\n')
            self.assertTrue(any(q['status'] == 'prefix_witness_without_return' for q in report['queries']))
            self.assertTrue(list(out.glob('query-*.replay.txt')))
