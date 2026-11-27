"""Saved entry facts, completion and every cut are independent acceptance gates."""
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import replay_loop_checkpoint as replay


class LoopCheckpointTests(unittest.TestCase):
    def fixture(self, inductive):
        texts = {'automatic-complete.smt2': 'complete', 'automatic-compare.smt2': 'compare',
                 'cut0': 'cut0', 'cut1': 'cut1', 'base': 'base', 'feedback': 'feedback'}
        value = dict(schema='nirvana-contextual-loop-m2-v1', cut_obligations=[
            dict(artifact=f'cut{n}', cut=n, kind='correspondence') for n in range(2)],
            comparison_partitions=dict(property_sha256=replay.digest(b'compare')))
        if inductive:
            value.update(schema='nirvana-inductive-loop-m2-v1', proof_artifacts=dict(
                completion='automatic-complete.smt2', comparison='automatic-compare.smt2',
                entry_invariants=dict(base='base', feedback='feedback')))
        return value, texts

    def test_legacy_and_inductive_results_require_every_relevant_obligation(self):
        for inductive in [False, True]:
            value, texts = self.fixture(inductive)
            expected = ['base', 'feedback', 'complete', 'cut0', 'cut1'] if inductive else ['complete', 'cut0', 'cut1']
            with self.subTest(inductive=inductive), patch.object(replay, 'solve', return_value='unsat') as solve:
                record = replay.replay_obligations(value, texts, Path('/unused/solver'))
                self.assertTrue(record['all_checkpoint_obligations_unsat'])
                self.assertEqual([call.args[1] for call in solve.call_args_list], expected)

    def test_failed_entry_completion_or_cut_stops_without_claiming_acceptance(self):
        for stage in range(5):
            for status in ['sat', 'unknown', 'unknown-budget', 'solver-failure']:
                value, texts = self.fixture(True)
                with self.subTest(stage=stage, status=status), patch.object(
                        replay, 'solve', side_effect=['unsat'] * stage + [status]) as solve:
                    record = replay.replay_obligations(value, texts, Path('/unused/solver'))
                    self.assertFalse(record['all_checkpoint_obligations_unsat'])
                    self.assertEqual(solve.call_count, stage + 1)
                    if stage < 2:
                        self.assertEqual(record['completion'], 'not-run')
                        self.assertEqual(record['obligations'], [])

    def test_missing_aliased_or_unbound_queries_are_rejected_before_the_solver(self):
        for mutation in ['missing', 'alias', 'property', 'empty', 'layout']:
            value, texts = self.fixture(True)
            if mutation == 'missing': del value['proof_artifacts']['entry_invariants']['feedback']
            elif mutation == 'alias': value['proof_artifacts']['entry_invariants']['feedback'] = 'base'
            elif mutation == 'property': texts['automatic-compare.smt2'] += ' changed'
            elif mutation == 'empty': value['cut_obligations'] = []
            else: del value['proof_artifacts']
            with self.subTest(mutation=mutation), patch.object(replay, 'solve') as solve:
                with self.assertRaises(ValueError):
                    replay.replay_obligations(value, texts, Path('/unused/solver'))
                solve.assert_not_called()


if __name__ == '__main__':
    unittest.main()
