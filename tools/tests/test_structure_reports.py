"""M0 comparison controls: fixed denominators, drift, replay and bounded search."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import control_graph as cg, reports, semantics, c_footprint as cf
import evaluate_structure


from report_fixture import DUMP, save, fixture


class ReportTests(unittest.TestCase):
    def test_probe_profile_and_stage_summaries_replay_the_retained_json(self):
        for variant in ['intact', 'profile', 'continuation', 'coverage', 'raw_hash', 'legacy', 'missing_binding']:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                report = fixture(root)
                report['evaluation']['probe_metadata'] = 'hashed-probe-json-v1'
                row = report['rows'][0]
                row['semantics']['profile'].update(step_limit=4096, requested_cases=3, seed=17)
                row['stage_checks'] = dict(
                    schema='nirvana-evaluation-stages-v1', contract='nirvana-entry-full-state-v1',
                    status='passed', prefix_budgets=[0, 4096],
                    execution=[dict(name='low_middle', status='passed', observations=12, witness=None),
                               dict(name='middle_predicates', status='not_applied', observations=0, witness=None)],
                    selected_c=dict(predicates=None, continuations=dict(model='c-fragment-continuation-v1',
                                    removed_conditions=1, compared_graph_nodes=3),
                                    input_structure_checked=True, display_structure_checked=True,
                                    saved_value_rounds=0, fallback_goto=False),
                    low_coverage=dict(steps_started=2, syntactic_steps=3, transfers_observed=1,
                                      syntactic_transfers=2, unobserved_transfers=[[1, 2]]))
                raw = {**row['semantics']['profile'], 'stage_checks': copy.deepcopy(row['stage_checks'])}
                target = root / row['artifacts']
                row['semantics']['prepare_stdout_sha256'] = save(target, 'semantic_prepare.stdout.txt', json.dumps(raw))
                if variant == 'profile': row['semantics']['profile']['seed'] = 18
                elif variant == 'continuation': row['stage_checks']['selected_c']['continuations']['removed_conditions'] = 2
                elif variant == 'coverage': row['stage_checks']['low_coverage']['steps_started'] = 1
                elif variant == 'raw_hash': (target / 'semantic_prepare.stdout.txt').write_text(json.dumps(raw) + ' ')
                elif variant in ['legacy', 'missing_binding']: row['semantics'].pop('prepare_stdout_sha256')
                if variant == 'missing_binding':
                    with self.assertRaisesRegex(ValueError, 'missing declared probe metadata'):
                        reports.index(report)
                    continue
                if variant == 'legacy': report['evaluation'].pop('probe_metadata')
                reports.index(report)
                if variant in ['intact', 'legacy']:
                    result = reports.replay(root, row)
                    self.assertEqual(result['probe_metadata'], 'replayed' if variant == 'intact' else 'legacy_unbound')
                else:
                    with self.subTest(variant=variant), self.assertRaises(ValueError):
                        reports.replay(root, row)

    def test_retained_content_is_recomputed_from_hashed_ast(self):
        with tempfile.TemporaryDirectory() as directory:
            a, b = Path(directory) / 'a', Path(directory) / 'b'
            before, after = fixture(a), fixture(b)
            for root, report in [(a, before), (b, after)]:
                row = report['rows'][0]; sides = {}
                for side, name in [('source', 'fixture'), ('generated', 'nirvana_readable')]:
                    raw = json.dumps({'kind': 'FunctionDecl', 'name': name, 'inner': [
                        {'kind': 'CompoundStmt', 'inner': [{'kind': 'ReturnStmt', 'inner': [
                            {'kind': 'IntegerLiteral', 'type': {'qualType': 'int'}, 'value': '7'}]}]}]})
                    sides[side] = {**cf.measure(raw, name), 'raw_ast_sha256': save(root / row['artifacts'], side + '_ast.stdout.txt', raw)}
                row['c_footprint'] = dict(metric=cf.METRIC, status='measured', **sides,
                                         source_generated_delta=cf.delta(sides['source'], sides['generated']))
            result = self.compare(a, b, before, after)
            self.assertEqual(result['rows'][0]['c_syntax_delta']['literals'], {})
            row = after['rows'][0]
            path = b / row['artifacts'] / 'generated_ast.stdout.txt'
            changed = path.read_text().replace('"value": "7"', '"value": "8"')
            row['c_footprint']['generated']['raw_ast_sha256'] = save(path.parent, path.name, changed)
            with self.assertRaisesRegex(ValueError, 'footprint differs'):
                self.compare(a, b, before, after)

    def test_reanalysis_retains_original_runs_and_failure_denominators(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = fixture(root)
            path = root / 'report.json'
            path.write_text(json.dumps(original))
            before = path.read_bytes()
            refined = reports.reanalyze(path)
            self.assertEqual(refined['rows'][0]['distance']['upper_bound'], 0)
            self.assertEqual(refined['reanalysis']['source_report_sha256'], semantics.sha(path))
            self.assertEqual(refined['reanalysis']['original_evaluation'], original['evaluation'])
            self.assertEqual(refined['rows'][0]['commands'], original['rows'][0]['commands'])
            self.assertEqual(refined['requested_profiles'], 1)
            self.assertEqual(path.read_bytes(), before)
            for states, seconds in [(0, 1), (100, float('inf')), (100, 0)]:
                with self.assertRaises(ValueError):
                    reports.reanalyze(path, max_states=states, seconds=seconds)
            failed = copy.deepcopy(original)
            failed['rows'][0].pop('distance')
            failed['rows'][0].update(structure_status='timeout', semantics={'status': 'not_run'})
            path.write_text(json.dumps(failed))
            preserved = reports.reanalyze(path)
            self.assertEqual(preserved['requested_profiles'], 1)
            self.assertEqual(preserved['rows'][0]['structure_status'], 'timeout')
            self.assertNotIn('distance', preserved['rows'][0])

    def compare(self, a, b, before, after):
        (a / 'report.json').write_text(json.dumps(before))
        (b / 'report.json').write_text(json.dumps(after))
        return reports.compare(a / 'report.json', b / 'report.json')

    def test_replays_graphs_mappings_all_ram_and_fault_rows(self):
        with tempfile.TemporaryDirectory() as directory:
            a, b = Path(directory) / 'a', Path(directory) / 'b'
            before, after = fixture(a), fixture(b)
            result = self.compare(a, b, before, after)
            self.assertEqual(result['requested'], 1)
            self.assertEqual(result['structure'], {'equal': 1})
            self.assertEqual(result['rows'][0]['distance_basis'], 'identical_graphs')
            self.assertEqual(result['semantic_regressions'], 0)
            # Last word includes a fault component, not just the returned value.
            path = b / after['rows'][0]['artifacts'] / 'generated_O2_run.stdout.txt'
            path.write_text(' '.join(['0'] * 68 + ['7']) + '\n')
            with self.assertRaisesRegex(reports.Incompatible, 'observer replay'):
                self.compare(a, b, before, after)

    def test_coverage_and_profile_drift_are_rejected(self):
        for variant in ['missing', 'duplicate', 'cohort', 'binary', 'seed', 'compiler', 'flags', 'metric']:
            with tempfile.TemporaryDirectory() as directory:
                a, b = Path(directory) / 'a', Path(directory) / 'b'
                before, after = fixture(a), fixture(b)
                row = after['rows'][0]
                if variant == 'missing': after['rows'] = []
                elif variant == 'duplicate': after['rows'].append(copy.deepcopy(row))
                elif variant == 'cohort': row['cohort'] = 'holdout'
                elif variant == 'binary': row['object_sha256'] = save(b / row['artifacts'], 'input.o', 'different')
                elif variant == 'seed': after['budgets']['seed'] = 3
                elif variant == 'compiler': after['compilers'] = {'gcc': {'sha256': 'f' * 64}}
                elif variant == 'flags': row['commands'][0]['argv'][1] = '-O3'
                else: after['metric'] = 'other-metric'
                with self.subTest(variant=variant), self.assertRaises(ValueError):
                    self.compare(a, b, before, after)

    def test_mappings_hashes_and_raw_dump_correspondence_are_replayed(self):
        for variant in ['mapping', 'hash', 'dump', 'escape']:
            with tempfile.TemporaryDirectory() as directory:
                a, b = Path(directory) / 'a', Path(directory) / 'b'
                before, after = fixture(a), fixture(b)
                row = after['rows'][0]
                if variant == 'mapping': row['distance']['mapping'][0] = (row['distance']['mapping'][0][0], 999)
                elif variant == 'hash': (b / row['artifacts'] / 'readable.c').write_text('changed')
                elif variant == 'dump':
                    row['generated_cfg']['dump_sha256'] = save(b / row['artifacts'], 'generated_cfg.stderr.txt',
                                                               DUMP.replace('fixture', 'nirvana_readable').replace('return 7;', 'x = 7;'))
                else: row['artifacts'] = '../a'
                with self.subTest(variant=variant), self.assertRaises(ValueError):
                    self.compare(a, b, before, after)

    def test_failures_keep_denominator_and_passed_to_unavailable_is_regression(self):
        with tempfile.TemporaryDirectory() as directory:
            a, b = Path(directory) / 'a', Path(directory) / 'b'
            before, after = fixture(a), fixture(b)
            row = after['rows'][0]
            for field in ['distance', 'source_cfg', 'generated_cfg', 'preprocessed_sha256',
                          'object_sha256', 'readable_sha256']:
                del row[field]
            row.update(structure_status='unavailable', semantics=dict(status='not_run'), commands=[])
            result = self.compare(a, b, before, after)
            self.assertEqual(result['requested'], 1)
            self.assertEqual(result['structure'], {'unmeasured': 1})
            self.assertEqual(result['semantic_regressions'], 1)
            self.assertEqual(result['structure_regressions'], 1)

    def test_overlapping_search_bounds_are_inconclusive(self):
        interval = lambda lo, hi: dict(status='exact' if lo == hi else 'upper_bound', lower_bound=lo, upper_bound=hi)
        for a, b, wanted in [(interval(0, 10), interval(0, 8), 'overlapping_bounds'),
                              (interval(10, 10), interval(0, 8), 'improved'),
                              (interval(0, 8), interval(10, 10), 'regressed'),
                              (interval(4, 4), interval(4, 4), 'equal')]:
            self.assertEqual(reports.interval_change(a, b), wanted)

    def test_initial_corpus_locks_four_development_and_two_holdout_families(self):
        path = evaluate_structure.ROOT / 'tools/corpora/structure-initial-v1.json'
        cases = evaluate_structure.load_cases(path)
        self.assertEqual(len(cases), 6)
        self.assertEqual(sum(c['cohort'] == 'development' for c in cases), 4)
        self.assertEqual(sum(c['cohort'] == 'holdout' for c in cases), 2)
        self.assertEqual(len({c['family'] for c in cases}), 6)
        for case in cases:
            self.assertEqual(case['source_sha256'], semantics.sha(evaluate_structure.ROOT / case['source']))


if __name__ == '__main__':
    unittest.main()
