"""MIR memory/saved-value stage contracts and retained full-state controls."""
import copy
import itertools
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import middle_pairs, semantic_pairs, stages, reports
from evaluation.semantics import ProtocolError
from report_fixture import architecture, fixture, save


class MiddlePairTests(unittest.TestCase):
    def fixture(self, root, saved=False):
        value = architecture(3, [0, 1, 4])
        value.update(schema='nirvana-evaluation-stages-v3', contract='nirvana-stage-input-state-v3',
                     original_registers=32)
        value['execution'].extend([
            dict(name=name, status='not_applied', observations=0, witness=None, transition=None)
            for name in ['middle_memory', 'middle_saved']])
        value['execution'].append(dict(name='selected_semantic', status='not_applied', observations=0,
                                       witness=None, semantic=None))
        for entry in value['execution']:
            entry['comparisons'] = stages.COMPARISONS[entry['name']].copy()
        entry = value['execution'][3 if saved else 2]
        name = entry['name']
        facts = (dict(annotated_reads=2, phi_values=0, merged_snapshots=0, proved_loads=1,
                      snapshot_values=1, replaced_reads=2) if saved else
                 dict(loads=2, proved_loads=1, refined_loads=1, analysis_complete=True))
        evidence = dict(model='middle-memory-transition-v1', source_registers=32,
                        lowered_registers=33 if saved else 32, input_ir=name + '.input.ir.txt',
                        lowered_ir=name + '.lowered.ir.txt', middle_ir=name + '.mir.txt', facts=facts,
                        state_pairs=dict(model=middle_pairs.MODEL, file=name + '.states.jsonl'))
        entry.update(status='passed', transition=evidence)
        for field in ['input_ir', 'lowered_ir', 'middle_ir']:
            count = evidence['lowered_registers'] if field == 'lowered_ir' else 32
            save(root, evidence[field], f'entry=16 registers={count}\n')
        save(root, 'native-inputs.txt', '1 2 3 4\n')
        rows = []
        for case, budget, variant in itertools.product(range(3), value['prefix_budgets'], entry['comparisons']):
            initial = [0] * 32
            pointer = [4224, 4592, 2**64 - 1][case]
            initial[4], initial[7] = 4600, pointer
            state = dict(status=[2, 0, 0, 0] if budget == 0 else [1, pointer, 1, 8],
                         registers=initial.copy(), memory_base=4096,
                         memory=semantic_pairs.memory([1, 2, 3, 4], pointer),
                         instruction=16, trace=[] if budget == 0 else [16])
            rows.append(dict(case=case, budget=budget, variant=variant, input=initial,
                             expected=state, actual=copy.deepcopy(state)))
        entry['observations'] = len(rows)
        return value, entry, rows

    def validate(self, root, value, entry, rows):
        save(root, entry['transition']['state_pairs']['file'], ''.join(json.dumps(r) + '\n' for r in rows))
        return stages.validate(value, 4, root, 3, 32)

    def test_both_transitions_replay_complete_states_and_bind_artifacts(self):
        for saved in [False, True]:
            with tempfile.TemporaryDirectory() as directory, self.subTest(saved=saved):
                root = Path(directory)
                value, entry, rows = self.fixture(root, saved)
                self.validate(root, value, entry, rows)
                evidence = entry['transition']
                self.assertEqual(evidence['state_pairs']['rows'], 27 if saved else 18)
                self.assertEqual(evidence['state_pairs']['input_binding'], 'native-vectors')
                self.validate(root, value, entry, rows)
                (root / evidence['middle_ir']).write_text('changed MIR\n')
                with self.assertRaisesRegex(ProtocolError, 'artifact hash'):
                    self.validate(root, value, entry, rows)

    def test_projection_inputs_faults_and_comparison_denominators_are_checked(self):
        for change in ['register', 'ram', 'fault', 'pc', 'trace', 'projection', 'input', 'initial',
                       'order', 'missing', 'patterns', 'facts', 'source-count', 'observations', 'native']:
            with tempfile.TemporaryDirectory() as directory, self.subTest(change=change):
                root = Path(directory)
                value, entry, rows = self.fixture(root, True)
                if change == 'register': rows[-1]['actual']['registers'][0] ^= 1
                elif change == 'ram': rows[-1]['actual']['memory'][0] ^= 1
                elif change == 'fault': rows[-1]['actual']['status'][1] ^= 1
                elif change == 'pc': rows[-1]['actual']['instruction'] = 99
                elif change == 'trace': rows[-1]['actual']['trace'] = [17]
                elif change == 'projection': rows[-1]['actual']['registers'].pop()
                elif change == 'input': rows[-1]['input'][7] = 0
                elif change == 'initial':
                    for side in ['expected', 'actual']: rows[0][side]['registers'][0] = 1
                elif change == 'order': rows[0], rows[1] = rows[1], rows[0]
                elif change == 'missing': rows.pop(); entry['observations'] -= 1
                elif change == 'patterns': entry['comparisons'].pop()
                elif change == 'facts': entry['transition']['facts']['replaced_reads'] = True
                elif change == 'source-count': entry['transition']['source_registers'] = 31
                elif change == 'observations': entry['observations'] -= 1
                elif change == 'native': save(root, 'native-inputs.txt', '5 2 3 4\n')
                with self.assertRaises(ProtocolError):
                    self.validate(root, value, entry, rows)

    def test_partial_observations_and_counterexamples_have_distinct_statuses(self):
        for status in ['counterexample', 'budget_exhausted']:
            with tempfile.TemporaryDirectory() as directory, self.subTest(status=status):
                root = Path(directory)
                value, entry, rows = self.fixture(root)
                value['status'] = 'counterexample' if status == 'counterexample' else 'inconclusive'
                entry['status'] = status
                if status == 'counterexample':
                    rows[-1]['actual']['registers'][0] ^= 1
                    entry['witness'] = entry['name'] + '.witness.txt'
                    save(root, entry['witness'], 'register differs\n')
                else:
                    rows.pop(); entry['observations'] -= 1
                self.validate(root, value, entry, rows)
                self.assertEqual(entry['transition']['state_pairs']['mismatches'], int(status == 'counterexample'))

    def test_new_stages_cannot_disappear_from_report_summary(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            report = fixture(root)
            value, _, _ = self.fixture(root / 'states')
            report['rows'][0]['stage_checks'] = value
            report['summary']['architecture_execution'] = stages.execution_summary(report['rows'])
            reports.index(report)
            report['summary']['architecture_execution'].pop('middle_saved')
            with self.assertRaisesRegex(ValueError, 'architecture execution denominator'):
                reports.index(report)
            report['summary'].pop('architecture_execution')
            with self.assertRaisesRegex(ValueError, 'missing architecture execution denominator'):
                reports.index(report)


if __name__ == '__main__':
    unittest.main()
