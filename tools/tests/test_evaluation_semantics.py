"""Semantic observations preserve full-word faults/RAM and all profile counts."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import semantics, stages


def architecture():
    return dict(schema='nirvana-evaluation-stages-v1', contract='nirvana-entry-full-state-v1',
                status='passed', prefix_budgets=[0, 4096],
                execution=[dict(name='low_middle', status='passed', observations=96, witness=None),
                           dict(name='middle_predicates', status='not_applied', observations=0, witness=None)],
                selected_c=dict(predicates=None, input_structure_checked=True, display_structure_checked=True,
                                saved_value_rounds=0, fallback_goto=False),
                low_coverage=dict(steps_started=2, syntactic_steps=3, transfers_observed=1,
                                  syntactic_transfers=2, unobserved_transfers=[[1, 2]]))


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

    def protocol(self, root, *, wrong=False, suspended=0, stage_checks=None, input_file=False):
        destination = root / 'semantics'
        destination.mkdir()
        count = 8
        profile = dict(schema='nirvana-evaluation-probe-v1', generator='fixture-state4-seeds-v1',
                       vectors=count, seed=17, step_limit=4096, requested_cases=24,
                       checked_cases=24 - suspended, native_cases=count,
                       returned=8, read_faults=8, write_faults=8 - suspended,
                       suspended=suspended, memory_base=4096, memory_size=512,
                       stack_pointer=4600, state_pointer=4224, row_words=69)
        if stage_checks is not None:
            profile['stage_checks'] = stage_checks
            if stage_checks['status'] == 'counterexample':
                (destination / 'low_middle.witness.txt').write_text('actual full-state counterexample')
        if input_file: profile['generator'] = 'fixture-state4-input-file-v1'
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
                if wrong == 'native': output = output.replace('0 1 2 3 4', '0 1 2 3 5', 1)
            elif stage.endswith('_run'):
                output = checked
                if wrong is True and stage == 'generated_O2_run':
                    # Mutate one RAM word, leaving return/fault fields untouched.
                    lines = output.splitlines()
                    fields = lines[0].split()
                    fields[-1] = '1'
                    lines[0] = ' '.join(fields)
                    output = '\n'.join(lines) + '\n'
            return subprocess.CompletedProcess(argv, 0, output, '')
        args = argparse.Namespace(semantic_probe='probe', emit='readable-c', semantic_seed=17,
                                  semantic_cases=count, semantic_steps=4096, c_compiler='cc')
        if input_file:
            args.semantic_inputs = root / 'fixed-inputs.txt'
            args.semantic_inputs.write_text('1 2 3 4\n' * count)
        row = {'function': 'fixture'}
        semantics.run(args, row, root, invoke, [])
        self.assertEqual(row['semantics']['prepare_stdout_sha256'],
                         hashlib.sha256(json.dumps(profile).encode()).hexdigest())
        return row, calls

    def test_fixed_input_file_keeps_an_explicit_generator_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            row, _ = self.protocol(Path(directory), input_file=True)
            self.assertEqual(row['semantics']['profile']['generator'], 'fixture-state4-input-file-v1')
            self.assertEqual(row['semantics']['status'], 'passed')

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

    def test_native_ir_counterexample_keeps_both_ir_c_comparisons(self):
        with tempfile.TemporaryDirectory() as directory:
            row, calls = self.protocol(Path(directory), wrong='native')
            checks = row['semantics']['checks']
            self.assertEqual(row['semantics']['status'], 'counterexample')
            self.assertEqual(checks['native']['status'], 'counterexample')
            self.assertEqual(checks['generated_O0']['status'], 'passed')
            self.assertEqual(checks['generated_O2']['status'], 'passed')
            self.assertIn('generated_O2_run', calls)

    def test_architecture_failure_keeps_native_and_generated_comparisons(self):
        for status in ['passed', 'counterexample', 'malformed']:
            with tempfile.TemporaryDirectory() as directory:
                value = architecture()
                if status == 'counterexample':
                    value['status'] = status
                    value['execution'][0].update(status=status, observations=1, witness='low_middle.witness.txt')
                elif status == 'malformed': value['low_coverage']['syntactic_transfers'] = 99
                row, calls = self.protocol(Path(directory), stage_checks=value)
                self.assertEqual(row['semantics']['status'], 'passed')
                self.assertNotIn('stage_checks', row['semantics']['profile'])
                self.assertIn('generated_O2_run', calls)
                self.assertEqual(row['stage_checks']['status'], 'evaluator_error' if status == 'malformed' else status)
                self.assertEqual(bool(row.get('failures')), status != 'passed')

    def test_stage_prefix_coverage_and_counterexample_protocol(self):
        for variant in ['coverage', 'budget', 'count', 'witness', 'status']:
            with tempfile.TemporaryDirectory() as directory:
                value = architecture()
                if variant == 'coverage': value['low_coverage']['unobserved_transfers'] = []
                elif variant == 'budget': value['prefix_budgets'] = [4096, 0]
                elif variant == 'count': value['execution'][0]['observations'] = 1
                elif variant == 'witness': value['execution'][0]['witness'] = '../outside'
                else: value['status'] = 'counterexample'
                with self.subTest(variant=variant), self.assertRaises(semantics.ProtocolError):
                    stages.validate(value, 4096, Path(directory), 24)

    def test_c_continuation_model_is_distinct_from_full_state_checks(self):
        evidence = dict(model='c-fragment-continuation-v1', removed_conditions=3,
                        compared_graph_nodes=10)
        with tempfile.TemporaryDirectory() as directory:
            for change in [None, {}, {'model': 'machine-full-state'}, {'removed_conditions': True},
                           {'removed_conditions': 0}, {'compared_graph_nodes': 16385}]:
                value = architecture()
                value['selected_c']['continuations'] = None if change is None else {**evidence, **change}
                if change in [None, {}]:
                    stages.validate(value, 4096, Path(directory), 24)
                else:
                    with self.subTest(change=change), self.assertRaises(semantics.ProtocolError):
                        stages.validate(value, 4096, Path(directory), 24)
            value = architecture()
            value['selected_c'].update(continuations=evidence, fallback_goto=True)
            with self.assertRaises(semantics.ProtocolError):
                stages.validate(value, 4096, Path(directory), 24)

    def test_c_continuation_v2_can_share_effects_while_retaining_the_condition(self):
        evidence = dict(model='c-fragment-continuation-v2', removed_conditions=0,
                        shared_fragments=3, compared_graph_nodes=10)
        with tempfile.TemporaryDirectory() as directory:
            for change in [{}, {'shared_fragments': 0}, {'shared_fragments': True},
                           {'shared_fragments': 4097}, {'removed_conditions': -1}]:
                value = architecture()
                value['selected_c']['continuations'] = {**evidence, **change}
                if change:
                    with self.subTest(change=change), self.assertRaises(semantics.ProtocolError):
                        stages.validate(value, 4096, Path(directory), 24)
                else:
                    stages.validate(value, 4096, Path(directory), 24)

    def test_argument_registers_preserve_order_and_reject_ambiguous_descriptors(self):
        with tempfile.TemporaryDirectory() as directory:
            for parameters in [[7], [1, 7], [], [7, 7], [True], [-1], [2**32], '7']:
                value = architecture()
                value['selected_c']['parameter_registers'] = parameters
                if parameters in [[7], [1, 7], []]:
                    self.assertEqual(stages.validate(value, 4096, Path(directory), 24)['selected_c']['parameter_registers'], parameters)
                else:
                    with self.subTest(parameters=parameters), self.assertRaises(semantics.ProtocolError):
                        stages.validate(value, 4096, Path(directory), 24)


if __name__ == '__main__':
    unittest.main()
