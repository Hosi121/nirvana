"""M0 comparison controls: fixed denominators, drift, replay and bounded search."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import control_graph as cg, reports, semantics
import evaluate_structure


DUMP = '''uint64_t fixture(void)
 [B2 (ENTRY)]
   Succs (1): B1
 [B1]
   1: return 7;
   Succs (1): B0
 [B0 (EXIT)]
'''


def save(root, name, text):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    return semantics.sha(path)


def fixture(root):
    row = dict(id='sample-gcc-O2', family='sample', cohort='development', source_sha256='a' * 64,
               function='fixture', compiler='gcc', optimization='O2', artifacts='sample-gcc-O2',
               structure_status='measured', commands=[])
    directory = root / row['artifacts']
    for field, name, text in [('preprocessed_sha256', 'source.i', 'source'),
                              ('object_sha256', 'input.o', 'object'),
                              ('readable_sha256', 'readable.c', 'generated')]:
        row[field] = save(directory, name, text)
    for stage in ['source_cfg', 'generated_cfg']:
        dump = DUMP if stage == 'source_cfg' else DUMP.replace('fixture', 'nirvana_readable')
        raw, stats = cg.parse_dump(dump, 'fixture' if stage == 'source_cfg' else 'nirvana_readable')
        graph, removed = cg.normalize(raw)
        row[stage] = {**stats, **removed, 'nodes': len(graph['nodes']), 'edges': len(graph['edges']),
                      'graph_sha256': save(directory, stage + '.json', json.dumps({'graph': graph})),
                      'dump_sha256': save(directory, stage + '.stderr.txt', dump)}
    row['distance'] = cg.distance(graph, graph)
    profile = dict(vectors=1, native_cases=1, checked_cases=1, suspended=0)
    inputs = {}
    for name in semantics.FILES:
        text = (' '.join(['0'] * (5 if name.startswith('native') else 69)) + '\n'
                if name.endswith('expected.txt') else '1 2 3 4\n' if name.endswith('inputs.txt') else 'harness')
        inputs[name] = save(directory / 'semantics', name, text)
    checks = {}
    for label, prefix, width in [('native', 'native', 5), ('generated_O0', 'generated', 69),
                                 ('generated_O2', 'generated', 69)]:
        save(directory, label + '_run.stdout.txt', ' '.join(['0'] * width) + '\n')
        checks[label] = dict(status='passed', cases=1)
    row['semantics'] = dict(status='passed', contract=semantics.CONTRACT, profile=profile,
                             inputs=inputs, checks=checks)
    row['commands'] = [dict(stage='input_compile', argv=['cc', '-O2', str(directory / 'source.i'),
                                                       '-o', str(directory / 'input.o')])]
    tool = dict(sha256='b' * 64, version='compiler-v1', returncode=0)
    report = dict(schema='nirvana-structure-report-v1', metric=cg.METRIC,
                  requested_profiles=1, summary=dict(requested=1, cohorts=dict(development=1)),
                  evaluation=dict(metric_sha256='c' * 64), budgets=dict(states=100), emission='readable-c',
                  corpus=dict(sha256='d' * 64), clang=tool, c_compiler=tool, compilers=dict(gcc=tool),
                  semantics=dict(contract=semantics.CONTRACT), workspace_revision='revision',
                  workspace_dirty=False, decompiler=dict(sha256='e' * 64), rows=[row])
    return report


class ReportTests(unittest.TestCase):
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
