"""Independent small-graph oracle, malformed dumps, and real Clang controls."""
from collections import Counter
import itertools
import os
from pathlib import Path
import random
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import control_graph as cg


def graph(nodes, edges):
    return {'nodes': dict(enumerate(nodes)), 'edges': edges}


def oracle(left, right, fixed=None):
    """Enumerate every partial matching, including simultaneous deletions/insertions."""
    fixed = {0: 0, 1: 1} if fixed is None else fixed
    a = sorted(set(left['nodes']) - set(fixed))
    b = sorted(set(right['nodes']) - set(fixed.values()))
    best = float('inf')
    for size in range(min(len(a), len(b)) + 1):
        for subset in itertools.combinations(a, size):
            for targets in itertools.permutations(b, size):
                mapping = {**fixed, **dict(zip(subset, targets))}
                score = len(left['nodes']) + len(right['nodes']) - 2 * len(mapping)
                score += sum(left['nodes'][x] != right['nodes'][y] for x, y in mapping.items())
                pending = Counter(right['edges'])
                for x, y in left['edges']:
                    edge = (mapping.get(x), mapping.get(y))
                    if None not in edge and pending[edge]:
                        pending[edge] -= 1
                    else:
                        score += 1
                score += sum(pending.values())
                best = min(best, score)
    return best


class EditDistance(unittest.TestCase):
    def test_partition_bound_never_exceeds_independent_partial_mapping_oracle(self):
        # Exercise all edges of the smallest nontrivial rooted graph. Loops and
        # disconnected nodes deliberately remain in this metric-level test.
        graphs = []
        possibilities = [(0, 1), (0, 2), (2, 1), (2, 2)]
        for mask in range(16):
            for label in ['branch', 'return']:
                graphs.append(graph(['entry', 'exit', label],
                                    [edge for n, edge in enumerate(possibilities) if mask >> n & 1]))
        for left in graphs:
            for right in graphs:
                for fixed in [{0: 0, 1: 1}, {0: 0, 1: 1, 2: 2}]:
                    self.assertLessEqual(cg.completion_bound(left, right, fixed), oracle(left, right, fixed))
        rng = random.Random(314159)
        for _ in range(120):
            size_a = rng.randrange(2, 6)
            size_b = rng.randrange(size_a, 7)
            def make(size):
                return graph(['entry', 'exit'] + [rng.choice(['return', 'branch', 'flow']) for _ in range(size - 2)],
                             [(a, b) for a in range(size) for b in range(size)
                              for _ in range(rng.randrange(3)) if rng.randrange(3) == 0])
            left, right = make(size_a), make(size_b)
            fixed = {0: 0, 1: 1}
            if size_a > 2 and rng.randrange(2):
                fixed[2] = rng.randrange(2, size_b)
            self.assertLessEqual(cg.completion_bound(left, right, fixed), oracle(left, right, fixed))

    def test_search_matches_all_partial_matchings_on_small_graphs(self):
        rng = random.Random(271828)
        graphs = []
        for size in range(2, 6):
            for _ in range(5):
                edges = [(a, b) for a in [0, *range(2, size)] for b in [1, *range(2, size)]
                         if rng.randrange(3) == 0]
                kinds = ['entry', 'exit', *[rng.choice(['branch', 'flow', 'return']) for _ in range(size - 2)]]
                graphs.append(graph(kinds, edges))
        for left, right in zip(graphs, reversed(graphs)):
            result = cg.distance(left, right)
            self.assertEqual(result['status'], 'exact')
            self.assertEqual(result['upper_bound'], oracle(left, right))
            self.assertEqual(result['upper_bound'], cg.mapping_cost(left, right, dict(result['mapping'])))
            self.assertEqual(result['upper_bound'], cg.distance(right, left)['upper_bound'])

    def test_ids_order_and_branch_polarity_are_not_structure(self):
        left = graph(['entry', 'exit', 'branch', 'return', 'return'], [(0, 2), (2, 3), (2, 4), (3, 1), (4, 1)])
        names = {0: 99, 1: 5, 2: 34, 3: 12, 4: 70}
        right = {'nodes': {names[n]: k for n, k in reversed(list(left['nodes'].items()))},
                 'edges': [(names[a], names[b]) for a, b in reversed(left['edges'])]}
        self.assertEqual(cg.distance(left, right)['upper_bound'], 0)

    def test_state_and_time_limits_keep_replayable_upper_bounds(self):
        rng = random.Random(1729)
        left = graph(['entry', 'exit'] + ['branch'] * 6,
                     [(a, b) for a in range(8) for b in range(8) if rng.randrange(4) == 0])
        right = graph(['entry', 'exit'] + ['branch'] * 6,
                      [(a, b) for a in range(8) for b in range(8) if rng.randrange(4) == 0])
        exact = oracle(left, right)
        for settings in [dict(max_states=1), dict(seconds=1e-12)]:
            result = cg.distance(left, right, **settings)
            self.assertEqual(result['status'], 'upper_bound')
            self.assertLessEqual(result['lower_bound'], exact)
            self.assertGreaterEqual(result['upper_bound'], exact)
            self.assertEqual(cg.mapping_cost(left, right, dict(result['mapping'])), result['upper_bound'])

    def test_parallel_edges_are_counted_and_bad_witnesses_rejected(self):
        left = graph(['entry', 'exit'], [(0, 1), (0, 1)])
        right = graph(['entry', 'exit'], [(0, 1)])
        self.assertEqual(cg.distance(left, right)['upper_bound'], 1)
        for mapping in [{0: 1, 1: 0}, {0: 0, 1: 0}, {0: 0}]:
            with self.assertRaises(ValueError):
                cg.mapping_cost(left, right, mapping)
        for settings in [dict(max_states=0), dict(seconds=float('inf')), dict(seconds=0)]:
            with self.assertRaises(ValueError):
                cg.distance(left, right, **settings)


DUMP = '''int fixture(int x)
 [B4 (ENTRY)]
   Succs (1): B3
 [B3]
   T: while 1
   Succs (2): B2 NULL
 [B2]
   1: return 4;
   Preds (1): B3
   Succs (1): B0
 [B1]
   1: return 5;
   Succs (1): B0
 [B0 (EXIT)]
   Preds (2): B1 B2

int helper(void)
 [B1 (ENTRY)]
   Succs (1): B0
 [B0 (EXIT)]
'''


class DumpReader(unittest.TestCase):
    def test_pruning_unreachable_and_transparent_flow_are_explicit(self):
        raw, stats = cg.parse_dump(DUMP, 'fixture')
        result, removed = cg.normalize(raw)
        self.assertEqual(stats['pruned_successor_slots'], 1)
        self.assertEqual(removed, {'unreachable_blocks': 1, 'contracted_flow_blocks': 1})
        self.assertEqual(result['nodes'], {4: 'entry', 2: 'return', 0: 'exit'})
        self.assertEqual(result['edges'], [(2, 0), (4, 2)])
        marked = DUMP.replace('B2 NULL', 'B2 B1(Unreachable)')
        self.assertEqual(cg.normalize(cg.parse_dump(marked, 'fixture')[0])[0], result)

    def test_unknown_and_incomplete_formats_are_rejected(self):
        for text in [DUMP.replace('B2 NULL', 'B999 NULL'),
                     DUMP.replace('Succs (2)', 'Succs (3)'),
                     DUMP.replace('B2 NULL', 'B2 UNKNOWN'),
                     DUMP.replace(' (ENTRY)', ' (NEW)'),
                     DUMP.replace('   Succs (1): B3\n', ''),
                     DUMP.replace(' [B3]', ' [B4]'),
                     DUMP + DUMP]:
            with self.subTest(text=text), self.assertRaises(cg.Unsupported):
                cg.parse_dump(text, 'fixture')
        with self.assertRaises(cg.Unsupported):
            cg.parse_dump(DUMP, 'missing')

    def test_an_infinite_cycle_does_not_disappear(self):
        raw = graph(['entry', 'exit', 'flow', 'flow'], [(0, 2), (2, 3), (3, 2)])
        normalized, _ = cg.normalize(raw)
        self.assertEqual(len(normalized['nodes']), 3)
        self.assertTrue(any(a == b for a, b in normalized['edges']))
        returning = graph(['entry', 'exit', 'return'], [(0, 2), (2, 1)])
        self.assertGreater(cg.distance(normalized, returning)['upper_bound'], 0)


class ClangControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.clang = os.environ.get('NIRVANA_CLANG') or shutil.which('clang')
        if not cls.clang:
            raise unittest.SkipTest('real CFG controls require Clang; set NIRVANA_CLANG')

    def test_renaming_and_goto_removal_with_duplicated_conditions(self):
        source = '''int original(int a, int b) {
 int x;
 if (a) { x = 1; goto done; }
 x = 2;
 done: if (b) x++;
 return x;
}
int renamed(int p, int q) {
 int result;
 if (p) { result = 1; goto bb_999; }
 result = 2;
 bb_999: if (q) result++;
 return result;
}
int duplicated(int a, int b) {
 int x = 0;
 if (a) x = 1;
 if (!a) x = 2;
 if (a && b) x++;
 if (!a && b) x++;
 return x;
}
int main(void) {
 for (int a=-1; a<=1; ++a) for (int b=-1; b<=1; ++b)
  if (original(a,b) != duplicated(a,b)) return 1;
 return 0;
}
'''
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'controls.c'
            path.write_text(source)
            result = subprocess.run([self.clang, '--analyze', '-std=c11', '-Xclang',
                                     '-analyzer-checker=debug.DumpCFG', str(path), '-o', os.devnull],
                                    capture_output=True, text=True, timeout=15)
            self.assertEqual(result.returncode, 0, result.stderr)
            original, stats = cg.parse_dump(result.stderr, 'original')
            renamed, _ = cg.parse_dump(result.stderr, 'renamed')
            duplicated, bad_stats = cg.parse_dump(result.stderr, 'duplicated')
            original, _ = cg.normalize(original)
            renamed, _ = cg.normalize(renamed)
            duplicated, _ = cg.normalize(duplicated)
            self.assertEqual(cg.distance(original, renamed)['upper_bound'], 0)
            result = cg.distance(original, duplicated)
            self.assertEqual(result['status'], 'exact')
            self.assertGreater(result['upper_bound'], 0)
            self.assertEqual((stats['gotos'], bad_stats['gotos']), (1, 0))
            binary = Path(directory) / 'control'
            subprocess.run([self.clang, '-std=c11', '-O2', str(path), '-o', str(binary)], check=True, timeout=15)
            subprocess.run([str(binary)], check=True, timeout=5)


if __name__ == '__main__':
    unittest.main()
