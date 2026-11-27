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


from report_fixture import architecture, semantic_architecture, retain_semantic_ir


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

    def protocol(self, root, *, wrong=False, suspended=0, stage_checks=None, input_file=False,
                 loop_enabled=False, loop_record=None):
        destination = root / 'semantics'
        destination.mkdir()
        count = 8
        profile = dict(schema='nirvana-evaluation-probe-v1', generator='fixture-state4-seeds-v1',
                       vectors=count, seed=17, step_limit=4096, requested_cases=24,
                       checked_cases=24 - suspended, native_cases=count,
                       returned=8, read_faults=8, write_faults=8 - suspended,
                       suspended=suspended, memory_base=4096, memory_size=512,
                       stack_pointer=4600, state_pointer=4224, row_words=69, register_count=32)
        if stage_checks is not None:
            profile['stage_checks'] = stage_checks
            retain_semantic_ir(destination, stage_checks)
            if stage_checks['status'] == 'counterexample':
                for entry in stage_checks['execution']:
                    if entry['status'] == 'counterexample':
                        (destination / entry['witness']).write_text('actual original-state counterexample')
        if input_file: profile['generator'] = 'fixture-state4-input-file-v1'
        if loop_record is not None: profile['loop_recovery'] = loop_record
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
        if loop_enabled: args.loop_solver = 'z3'
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

    def test_loop_evidence_requires_its_explicit_profile_and_keeps_c_checks_on_failure(self):
        for enabled, record in [(True, None), (False, {'status': 'passed'})]:
            with tempfile.TemporaryDirectory() as directory:
                row, calls = self.protocol(Path(directory), loop_enabled=enabled, loop_record=record)
                self.assertEqual(row['loop_recovery']['status'], 'evaluator_error')
                self.assertEqual(row['semantics']['status'], 'passed')
                self.assertEqual(row['failures'][0]['stage'], 'loop_recovery')
                self.assertIn('generated_O2_run', calls)
                self.assertNotIn('loop_recovery', row['semantics']['profile'])

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

    def test_semantic_projection_binds_registers_capture_counts_and_two_private_patterns(self):
        for variant in ['valid', 'display-input', 'source', 'lowered', 'count', 'boolean', 'model', 'private',
                        'original', 'unbound', 'absent', 'missing-stage', 'observations', 'ir-hash', 'ir-name']:
            with tempfile.TemporaryDirectory() as directory:
                value = semantic_architecture()
                entry = value['execution'][-1]
                evidence = entry['semantic']
                retain_semantic_ir(Path(directory), value)
                registers = 32
                if variant == 'display-input': evidence.update(source_registers=96, lowered_registers=99)
                elif variant == 'source': evidence['source_registers'] = 31
                elif variant == 'lowered': evidence['lowered_registers'] = 36
                elif variant == 'count': evidence['inputs'] = 0
                elif variant == 'boolean': evidence['divisions'] = True
                elif variant == 'model': evidence['model'] = 'all-registers-v1'
                elif variant == 'private': evidence['fresh_initializers'] = [0, 0]
                elif variant == 'original': value['original_registers'] = 31
                elif variant == 'unbound': registers = None
                elif variant == 'absent': entry['semantic'] = None
                elif variant == 'missing-stage': value['execution'].pop()
                elif variant == 'observations': entry['observations'] = 48
                elif variant == 'ir-hash': evidence['input_ir_sha256'] = '0' * 64
                elif variant == 'ir-name': evidence['input_ir'] = '../outside'
                with self.subTest(variant=variant):
                    if variant in ['valid', 'display-input']:
                        stages.validate(value, 4096, Path(directory), 24, registers)
                    else:
                        with self.assertRaises(semantics.ProtocolError):
                            stages.validate(value, 4096, Path(directory), 24, registers)

    def test_semantic_counterexamples_keep_native_c_observations_and_not_applied_is_explicit(self):
        for status in ['passed', 'counterexample', 'not_applied']:
            with tempfile.TemporaryDirectory() as directory:
                value = semantic_architecture()
                entry = value['execution'][-1]
                if status == 'counterexample':
                    value['status'] = status
                    entry.update(status=status, observations=2, witness='selected_semantic.witness.txt')
                elif status == 'not_applied':
                    entry.update(status=status, observations=0, semantic=None)
                row, calls = self.protocol(Path(directory), stage_checks=value)
                self.assertEqual(row['semantics']['status'], 'passed')
                self.assertIn('generated_O2_run', calls)
                self.assertEqual(row['stage_checks']['status'], 'counterexample' if status == 'counterexample' else 'passed')
                self.assertEqual(row['stage_checks']['execution'][-1]['status'], status)

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

    def test_store_order_evidence_has_explicit_prefix_range_and_progress_counts(self):
        with tempfile.TemporaryDirectory() as directory:
            evidence = dict(model='c-fragment-continuation-v3', removed_conditions=0, shared_fragments=1,
                            compared_graph_nodes=20, store_order=dict(prefix_nodes=3,range_witnesses=2,swapped_pairs=1))
            for change in [{}, {'prefix_nodes': 0}, {'range_witnesses': True}, {'swapped_pairs': 0}, {'extra': 1}]:
                value = architecture()
                value['selected_c']['continuations'] = {**evidence, 'store_order': {**evidence['store_order'], **change}}
                if change:
                    with self.subTest(change=change), self.assertRaises(semantics.ProtocolError):
                        stages.validate(value, 4096, Path(directory), 24)
                else: stages.validate(value, 4096, Path(directory), 24)

    def test_effect_order_evidence_counts_scalar_and_memory_moves_separately(self):
        with tempfile.TemporaryDirectory() as directory:
            evidence = dict(model='c-fragment-continuation-v4', removed_conditions=0, shared_fragments=1,
                            compared_graph_nodes=20, effect_order=dict(prefix_nodes=3,range_witnesses=2,store_pairs=0,local_pairs=1))
            for change in [{}, {'prefix_nodes': 0}, {'range_witnesses': True}, {'local_pairs': 0},
                           {'store_pairs': -1}, {'store_pairs': 4096}, {'extra': 1}]:
                value = architecture()
                value['selected_c']['continuations'] = {**evidence, 'effect_order': {**evidence['effect_order'], **change}}
                if change:
                    with self.subTest(change=change), self.assertRaises(semantics.ProtocolError):
                        stages.validate(value, 4096, Path(directory), 24)
                else: stages.validate(value, 4096, Path(directory), 24)


if __name__ == '__main__':
    unittest.main()
