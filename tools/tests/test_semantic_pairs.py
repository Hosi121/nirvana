"""Concrete Semantic IR replay controls, independent of Rust's equality test."""
import copy
import itertools
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import semantic_pairs as pairs
from evaluation.semantics import ProtocolError
from evaluation import stages, reports
from report_fixture import fixture, save, semantic_architecture


class StatePairTests(unittest.TestCase):
    def test_complete_state_pairs_cannot_be_silently_replaced_with_metadata_only(self):
        with tempfile.TemporaryDirectory() as directory:
            roots = [Path(directory) / 'before', Path(directory) / 'after']
            for index, root in enumerate(roots):
                report = fixture(root)
                row = report['rows'][0]
                destination = root / row['artifacts'] / 'semantics'
                evidence, budgets, data = self.fixture(destination)
                (destination / 'input.ir').rename(destination / 'selected-semantic-input.ir.txt')
                (destination / 'selected-semantic-lowered.ir.txt').write_text('lowered IR\n')
                self.replay(destination, {**evidence, 'input_ir': 'selected-semantic-input.ir.txt'}, budgets, data)
                row['semantics']['profile'].update(register_count=32, step_limit=4, requested_cases=3)
                row['stage_checks'] = semantic_architecture(3, budgets)
                semantic = row['stage_checks']['execution'][-1]['semantic']
                semantic.update(source_registers=34, lowered_registers=37)
                if index == 0:
                    semantic['state_pairs'] = dict(model=pairs.MODEL, file=pairs.FILENAME)
                row['semantics']['prepare_stdout_sha256'] = save(root / row['artifacts'],
                    'semantic_prepare.stdout.txt', json.dumps({**row['semantics']['profile'], 'stage_checks': row['stage_checks']}))
                report['summary']['architecture_execution'] = stages.execution_summary(report['rows'])
                (root / 'report.json').write_text(json.dumps(report))
            result = reports.compare(*(root / 'report.json' for root in roots))
            self.assertEqual(result['architecture_regressions'], 1)
            self.assertEqual(result['rows'][0]['architecture_checks_lost'], ['selected_semantic.state_pairs'])

    def fixture(self, root):
        (root / 'native-inputs.txt').write_text('1 2 3 4\n')
        (root / 'input.ir').write_text('entry=16 registers=34\n')
        evidence = dict(source_registers=34, input_ir='input.ir')
        budgets = [0, 1, 4]
        rows = []
        for case, budget, fresh in itertools.product(range(3), budgets, [0, pairs.MAX_U64]):
            pointer = [4224, 4592, pairs.MAX_U64][case]
            initial = [0] * 32
            initial[4], initial[7] = 4600, pointer
            state = dict(status=[2, 0, 0, 0] if budget == 0 else [0, 7, 0, 0],
                         registers=initial + ([fresh] * 2 if budget == 0 else [9, 10]),
                         memory_base=4096, memory=pairs.memory([1, 2, 3, 4], pointer),
                         instruction=16 if budget == 0 else None, trace=[] if budget == 0 else [16])
            rows.append(dict(case=case, budget=budget, fresh=fresh, input=initial,
                             expected=state, actual=copy.deepcopy(state)))
        return evidence, budgets, rows

    def replay(self, root, evidence, budgets, rows, status='passed', metadata=None):
        (root / pairs.FILENAME).write_text(''.join(json.dumps(row) + '\n' for row in rows))
        return pairs.validate(metadata or dict(model=pairs.MODEL, file=pairs.FILENAME),
                              dict(status=status, observations=len(rows)), evidence, budgets, 3, root, 32)

    def test_full_words_ram_status_pc_and_trace_are_replayed_and_summaries_are_bound(self):
        for change in ['intact', 'register', 'ram', 'status', 'pc', 'trace', 'projection', 'input',
                       'initial-ram', 'initial-private', 'coverage', 'truncated', 'native']:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                evidence, budgets, rows = self.fixture(root)
                if change == 'register': rows[-1]['actual']['registers'][0] ^= 1
                elif change == 'ram': rows[-1]['actual']['memory'][0] ^= 1
                elif change == 'status': rows[-1]['actual']['status'] = [1, 8192, 2, 8]
                elif change == 'pc': rows[-1]['actual']['instruction'] = 99
                elif change == 'trace': rows[-1]['actual']['trace'] = [17]
                elif change == 'projection': rows[-1]['actual']['registers'].append(0)
                elif change == 'input': rows[-1]['input'][7] = 99
                elif change == 'initial-ram':
                    for side in ['expected', 'actual']: rows[0][side]['memory'][0] ^= 1
                elif change == 'initial-private':
                    for side in ['expected', 'actual']: rows[0][side]['registers'][-1] = 1
                elif change == 'coverage': rows[0], rows[1] = rows[1], rows[0]
                elif change == 'truncated': rows.pop()
                elif change == 'native': (root / 'native-inputs.txt').write_text('5 2 3 4\n')
                with self.subTest(change=change):
                    if change == 'intact':
                        result = self.replay(root, evidence, budgets, rows)
                        self.assertEqual((result['rows'], result['mismatches'], result['input_binding']),
                                         (18, 0, 'native-vectors'))
                        self.assertEqual(self.replay(root, evidence, budgets, rows, metadata=result), result)
                        for key, value in [('sha256', '0' * 64), ('rows', 17), ('mismatches', False)]:
                            with self.assertRaises(ProtocolError):
                                self.replay(root, evidence, budgets, rows, metadata={**result, key: value})
                    else:
                        with self.assertRaises(ProtocolError):
                            self.replay(root, evidence, budgets, rows)

    def test_counterexamples_and_incomplete_observations_keep_their_distinct_statuses(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            evidence, budgets, rows = self.fixture(root)
            rows[-1]['actual']['memory'][-1] ^= 1
            result = self.replay(root, evidence, budgets, rows, 'counterexample')
            self.assertEqual(result['mismatches'], 1)
            rows.pop()
            result = self.replay(root, evidence, budgets, rows, 'budget_exhausted')
            self.assertEqual((result['rows'], result['mismatches']), (17, 0))
            (root / 'native-inputs.txt').write_text('')
            result = self.replay(root, evidence, budgets, rows, 'budget_exhausted')
            self.assertEqual(result['input_binding'], 'stage-profile')

    def test_records_are_bounded_and_ambiguous_json_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            evidence, budgets, rows = self.fixture(root)
            metadata = dict(model=pairs.MODEL, file=pairs.FILENAME)
            entry = dict(status='passed', observations=18)
            self.replay(root, evidence, budgets, rows)
            path = root / pairs.FILENAME
            for text in ['{"case":0,"case":0}\n', '[]\n', '{bad}\n', ' ' * (pairs.MAX_LINE_BYTES + 1)]:
                path.write_text(text)
                with self.assertRaises(ProtocolError):
                    pairs.validate(metadata, entry, evidence, budgets, 3, root, 32)
            with path.open('wb') as stream: stream.truncate(pairs.MAX_BYTES + 1)
            with self.assertRaises(ProtocolError):
                pairs.validate(metadata, entry, evidence, budgets, 3, root, 32)


if __name__ == '__main__':
    unittest.main()
