"""Semantic observations preserve full-word faults/RAM and all profile counts."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import semantics


class SemanticTests(unittest.TestCase):
    def test_full_ram_and_first_fault_differences_replay_their_input(self):
        returned = [0, 0, 0, 0, 17, 0x1122334455667788]
        fault = [1, 8191, 2, 8, 0, 0x1122334455667788]
        text = lambda rows: ''.join(' '.join(map(str, row)) + '\n' for row in rows)
        expected = text([returned, fault])
        self.assertEqual(semantics.compare(expected, expected, 'first\nsecond\n', 6)['status'], 'passed')
        for field in [0, 1, 2, 3, 5]:
            changed = fault.copy()
            changed[field] ^= 1
            result = semantics.compare(expected, text([returned, changed]), 'first\nsecond\n', 6)
            self.assertEqual(result['status'], 'counterexample')
            self.assertEqual(result['input'], 'second')
            self.assertEqual(result['case_index'], 1)
        for actual in [text([returned]), 'bad\n', text([[0, 0, 0, 0, 0, -1]]), expected + expected]:
            with self.assertRaises(semantics.ProtocolError):
                semantics.compare(expected, actual, 'first\nsecond\n', 6)

    def protocol(self, root, *, wrong=False, suspended=0):
        destination = root / 'semantics'
        destination.mkdir()
        count = 8
        profile = dict(schema='nirvana-evaluation-probe-v1', generator='fixture-state4-seeds-v1',
                       vectors=count, seed=17, step_limit=4096, requested_cases=24,
                       checked_cases=24 - suspended, native_cases=count,
                       returned=8, read_faults=8, write_faults=8 - suspended,
                       suspended=suspended, memory_base=4096, memory_size=512,
                       stack_pointer=4600, state_pointer=4224, row_words=69)
        native = ('0 1 2 3 4\n' * count)
        checked = (' '.join(['0'] * 69) + '\n') * profile['checked_cases']
        files = {'native-inputs.txt': '1 2 3 4\n' * count, 'native-expected.txt': native,
                 'generated-inputs.txt': '4224 1 2 3 4\n' * profile['checked_cases'],
                 'generated-expected.txt': checked, 'native-probe.c': 'native harness',
                 'generated-probe.c': 'checked harness'}
        for name, content in files.items():
            (destination / name).write_text(content)
        calls = []
        def invoke(argv, stage, **kwargs):
            calls.append(stage)
            output = json.dumps(profile) if stage == 'semantic_prepare' else ''
            if stage == 'native_run':
                output = native
            elif stage.endswith('_run'):
                output = checked
                if wrong and stage == 'generated_O2_run':
                    # Mutate one RAM word, leaving return/fault fields untouched.
                    lines = output.splitlines()
                    fields = lines[0].split()
                    fields[-1] = '1'
                    lines[0] = ' '.join(fields)
                    output = '\n'.join(lines) + '\n'
            return subprocess.CompletedProcess(argv, 0, output, '')
        args = argparse.Namespace(semantic_probe='probe', emit='readable-c', semantic_seed=17,
                                  semantic_cases=count, semantic_steps=4096, c_compiler='cc')
        row = {'function': 'fixture'}
        semantics.run(args, row, root, invoke, [])
        return row, calls

    def test_all_three_comparisons_have_independent_coverage_and_witnesses(self):
        for wrong in [False, True]:
            with tempfile.TemporaryDirectory() as directory:
                row, calls = self.protocol(Path(directory), wrong=wrong)
                self.assertEqual(row['semantics']['status'], 'counterexample' if wrong else 'passed')
                self.assertEqual(set(row['semantics']['checks']), {'native', 'generated_O0', 'generated_O2'})
                self.assertIn('generated_O2_run', calls)
                if wrong:
                    witness = row['semantics']['checks']['generated_O2']
                    self.assertEqual(witness['case_index'], 0)
                    self.assertEqual(witness['actual'][:5], witness['expected'][:5])

    def test_budget_suspension_remains_in_denominator(self):
        with tempfile.TemporaryDirectory() as directory:
            row, _ = self.protocol(Path(directory), suspended=2)
            observed = row['semantics']
            self.assertEqual(observed['status'], 'inconclusive')
            self.assertEqual(observed['profile']['requested_cases'], 24)
            self.assertEqual(observed['profile']['checked_cases'], 22)
            self.assertEqual(observed['profile']['suspended'], 2)


if __name__ == '__main__':
    unittest.main()
