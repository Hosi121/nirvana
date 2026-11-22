"""M0 runner protocol: denominator, artifact replay and tool failures."""
import argparse
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import evaluate_structure as tool
from evaluation import control_graph as cg


class RunnerTests(unittest.TestCase):
    def args(self, root, **settings):
        defaults = dict(cases=tool.ROOT / 'tools/corpora/structure-smoke.json',
                        compiler=['missing=/nonexistent/nirvana-evaluation-compiler'],
                        optimization=['O2', 'O3'], out=root / 'out',
                        decompiler=Path(sys.executable), clang='/nonexistent/clang',
                        c_compiler='cc', timeout=10, search_seconds=1, max_states=10000)
        defaults.update(settings)
        return argparse.Namespace(**defaults)

    def test_unavailable_tools_preserve_every_requested_profile(self):
        with tempfile.TemporaryDirectory() as directory:
            args = self.args(Path(directory))
            result = tool.run(args)
            self.assertEqual(result['summary']['requested'], 8)
            self.assertEqual(result['summary']['status'], {'unavailable': 8})
            self.assertEqual(result['summary']['failures_by_stage'], {'preprocess': 8})
            self.assertEqual(result['semantics']['status'], 'not_run')
            for row in result['rows']:
                self.assertNotIn('distance', row)
                self.assertEqual(row['commands'][0]['status'], 'unavailable')
            saved = json.loads((args.out / 'report.json').read_text())
            self.assertEqual(saved, result)
            with self.assertRaisesRegex(ValueError, 'must be empty'):
                tool.run(args)
            self.assertEqual(json.loads((args.out / 'report.json').read_text()), result)

    def test_manifest_prevents_family_leakage_and_path_ambiguity(self):
        manifest = json.loads((tool.ROOT / 'tools/corpora/structure-smoke.json').read_text())
        for variant in ['cohort', 'path', 'id', 'symbol']:
            changed = copy.deepcopy(manifest)
            if variant == 'cohort':
                changed['cases'][1]['family'] = changed['cases'][0]['family']
                changed['cases'][1]['cohort'] = 'holdout'
            elif variant == 'path':
                changed['cases'][0]['source'] = '/etc/passwd'
            elif variant == 'id':
                changed['cases'][0]['id'] = '../outside'
            else:
                changed['cases'][0]['function'] = 'fixture.*'
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / 'cases.json'
                path.write_text(json.dumps(changed))
                with self.subTest(variant=variant), self.assertRaises(ValueError):
                    tool.load_cases(path)

    def test_timeout_keeps_partial_output_and_budget_classification(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            row = {'stages': {}, 'commands': []}
            with self.assertRaises(tool.CommandError) as caught:
                tool.invoke([sys.executable, '-c', 'import time; print("started", flush=True); time.sleep(2)'],
                            'probe', path, row, .5)
            self.assertEqual(caught.exception.kind, 'timeout')
            self.assertEqual(row['commands'][0]['status'], 'timeout')
            self.assertEqual((path / 'probe.stdout.txt').read_text(), 'started\n')
            self.assertNotIn('probe', row['stages'])

    def test_real_compiler_protocol_and_saved_witness(self):
        clang = os.environ.get('NIRVANA_CLANG') or shutil.which('clang')
        if not clang or not shutil.which('cc'):
            self.skipTest('requires cc and Clang; set NIRVANA_CLANG')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = json.loads((tool.ROOT / 'tools/corpora/structure-smoke.json').read_text())
            manifest['cases'] = manifest['cases'][:1]
            cases = root / 'cases.json'
            cases.write_text(json.dumps(manifest))
            # This is a protocol stub, not a decompiler oracle. It ensures the
            # evaluator gives its decompiler only an ELF object and mode flags.
            binary = root / 'decompiler'
            binary.write_text('#!' + sys.executable + '\n' + '''import sys
from pathlib import Path
assert len(sys.argv)==6 and sys.argv[2:]==['--symbol','fixture','--emit','readable-c']
assert Path(sys.argv[1]).suffix=='.o' and Path(sys.argv[1]).read_bytes()[:4]==b'\\x7fELF'
print('#include <stdint.h>\\nuint64_t nirvana_readable(uint64_t a) { if(a) return 1; return 2; }')
''')
            binary.chmod(0o755)
            args = self.args(root, cases=cases, compiler=['gcc=cc'], optimization=['O2'],
                             decompiler=binary, clang=clang)
            result = tool.run(args)
            self.assertEqual(result['summary']['status'], {'measured': 1})
            row = result['rows'][0]
            artifacts = args.out / row['artifacts']
            self.assertEqual(row['object_sha256'], tool.digest(artifacts / 'input.o'))
            graphs = [cg.graph_from_json(json.loads((artifacts / f'{name}.json').read_text())['graph'])
                      for name in ['source_cfg', 'generated_cfg']]
            self.assertEqual(cg.mapping_cost(*graphs, dict(row['distance']['mapping'])),
                             row['distance']['upper_bound'])
            # An invalid generated translation unit fails at recompile, not lift
            # or metric evaluation, and stays in the same one-profile cohort.
            binary.write_text('#!' + sys.executable + '\nprint("invalid C !!!")\n')
            args.out = root / 'bad-c'
            bad = tool.run(args)
            self.assertEqual(bad['summary']['requested'], 1)
            self.assertEqual(bad['summary']['failures_by_stage'], {'recompile': 1})
            self.assertEqual(bad['rows'][0]['stages']['decompile'], 'passed')
            self.assertNotIn('distance', bad['rows'][0])


if __name__ == '__main__':
    unittest.main()
