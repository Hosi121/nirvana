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
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import evaluate_structure as tool
from evaluation import control_graph as cg


class RunnerTests(unittest.TestCase):
    def test_missing_ast_tools_keep_semantic_axis_and_content_denominator(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = json.loads((tool.ROOT / 'tools/corpora/structure-smoke.json').read_text())
            manifest['cases'] = manifest['cases'][:1]
            cases = root / 'cases.json'; cases.write_text(json.dumps(manifest))
            binary = root / 'decompiler'
            binary.write_text('#!' + sys.executable + '\nprint("#include <stdint.h>\\nuint64_t nirvana_readable(uint64_t a) { return a; }")\n')
            binary.chmod(0o755)
            args = self.args(root, cases=cases, compiler=['gcc=cc'], optimization=['O2'],
                             decompiler=binary, semantic_probe=Path(sys.executable), c_footprint=True,
                             state_memory_sites=True, state_values=True)
            def semantic(*args): args[1]['semantics'] = {'status': 'passed'}
            with mock.patch.object(tool.semantics, 'run', side_effect=semantic) as probe:
                report = tool.run(args)
            probe.assert_called_once()
            row = report['rows'][0]
            self.assertEqual(row['semantics']['status'], 'passed')
            self.assertEqual(report['summary']['requested'], 1)
            self.assertEqual(report['summary']['c_footprint'], {'incomplete': 1})
            self.assertEqual(row['c_footprint']['source']['status'], 'unavailable')
            self.assertEqual(row['c_footprint']['generated']['status'], 'unavailable')
            self.assertEqual(report['summary']['state_memory_sites'], {'unavailable': 1})
            self.assertEqual(report['summary']['state_values'], {'unavailable': 1})

    def test_state_values_require_sites_and_a_finite_solver_budget(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with self.assertRaisesRegex(ValueError, 'require --state-memory-sites'):
                tool.run(self.args(root, state_values=True))
            for seconds in [0, -1, float('nan'), float('inf'), 31, True]:
                with self.subTest(seconds=seconds), self.assertRaisesRegex(ValueError, 'solver budget'):
                    tool.run(self.args(root, value_seconds=seconds))

    def test_state_memory_requires_both_ast_and_abi_evidence(self):
        for settings in [dict(c_footprint=True), dict(semantic_probe=Path(sys.executable))]:
            with tempfile.TemporaryDirectory() as directory:
                args = self.args(Path(directory), state_memory_sites=True, **settings)
                with self.assertRaisesRegex(ValueError, 'require --c-footprint and --semantic-probe'):
                    tool.run(args)

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
        for variant in ['cohort', 'path', 'id', 'symbol', 'hash']:
            changed = copy.deepcopy(manifest)
            if variant == 'cohort':
                changed['cases'][1]['family'] = changed['cases'][0]['family']
                changed['cases'][1]['cohort'] = 'holdout'
            elif variant == 'path':
                changed['cases'][0]['source'] = '/etc/passwd'
            elif variant == 'id':
                changed['cases'][0]['id'] = '../outside'
            elif variant == 'symbol':
                changed['cases'][0]['function'] = 'fixture.*'
            else:
                changed['cases'][0]['source_sha256'] = '0' * 64
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

    def test_command_transport_delivers_semantic_case_inputs(self):
        inputs = '1 2 3 4\n' * 4096
        result = tool.capture([sys.executable, '-c', 'import sys; print(sys.stdin.read(), end="")'],
                              5, input=inputs)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, inputs)

    def test_graph_tool_failure_keeps_semantic_axis_and_each_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = json.loads((tool.ROOT / 'tools/corpora/structure-smoke.json').read_text())
            manifest['cases'] = manifest['cases'][:1]
            cases = root / 'cases.json'
            cases.write_text(json.dumps(manifest))
            binary = root / 'decompiler'
            binary.write_text('#!' + sys.executable + '\nprint("#include <stdint.h>\\nuint64_t nirvana_readable(uint64_t a) { return a; }")\n')
            binary.chmod(0o755)
            for fail in [False, True, 'internal']:
                args = self.args(root, cases=cases, compiler=['gcc=cc'], optimization=['O2'],
                                 decompiler=binary, semantic_probe=Path(sys.executable),
                                 out=root / str(fail))
                def probe(args, row, *rest):
                    if fail == 'internal':
                        raise TypeError('observer bug')
                    if fail:
                        raise tool.semantics.ProtocolError('bad observer')
                    row['semantics'] = {'status': 'passed'}
                # A protocol stub isolates axis orchestration from equivalence.
                with mock.patch.object(tool.semantics, 'run', side_effect=probe) as called:
                    report = tool.run(args)
                called.assert_called_once()
                row = report['rows'][0]
                self.assertEqual(row['structure_status'], 'unavailable')
                expected = 'evaluator_error' if fail == 'internal' else 'tool_error' if fail else 'passed'
                self.assertEqual(row['semantics']['status'], expected)
                self.assertEqual(report['summary']['requested'], 1)
                failures = report['summary']['failures_by_stage']
                self.assertEqual(failures['source_cfg'], 1)
                self.assertEqual(failures.get('semantic_prepare', 0), int(bool(fail)))
                if fail == 'internal':
                    self.assertTrue((args.out / row['artifacts'] / 'evaluator.traceback.txt').is_file())

    def test_rss_measurement_is_per_command_and_keeps_missing_tools_unavailable(self):
        if not Path('/usr/bin/time').is_file():
            self.skipTest('requires GNU time')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            row = {'stages': {}, 'commands': [], 'measure_rss': True}
            tool.invoke([sys.executable, '-c', 'x=bytearray(8*1024*1024); print(len(x))'],
                        'memory', root, row, 5)
            sample = row['commands'][0]['resources']
            self.assertGreater(sample['max_rss_kib'], 0)
            self.assertGreaterEqual(sample['user_seconds'], 0)
            with self.assertRaises(tool.CommandError) as error:
                tool.invoke(['/nonexistent/nirvana-eval-tool'], 'missing', root, row, 5)
            self.assertEqual(error.exception.kind, 'unavailable')
            self.assertNotIn('resources', row['commands'][1])

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
