"""Loop endpoint replay preserves faults, RAM, coverage and artifact binding."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import loop_recovery as lr
from evaluation.semantics import ProtocolError


class LoopRecoveryTests(unittest.TestCase):
    def fixture(self, root):
        directory = root / 'semantics'
        directory.mkdir()
        memory = bytes((n * 29 + 7) & 255 for n in range(512))
        regs = [0] * 32
        regs[4], regs[7] = 4600, lr.U64
        endpoints = [
            {'status': {'kind': 'returned', 'value': 17}, 'memory': memory.hex()},
            {'status': {'kind': 'fault', 'address': lr.U64, 'access': 'read', 'width': 8}, 'memory': memory.hex()},
        ]
        rows = [{'case': case, 'initial': initial, 'input': regs, 'ram': memory.hex(),
                 **{name: copy.deepcopy(endpoint) for name in ['machine', 'display', 'recovered']}}
                for case, endpoint in enumerate(endpoints) for initial in [0, lr.U64]]
        (directory / 'loop-endpoints.jsonl').write_text(''.join(json.dumps(row) + '\n' for row in rows))
        (directory / 'generated-inputs.txt').write_text((f'{lr.U64} 0 0 0 0\n') * 2)
        (directory / 'generated-expected.txt').write_text(''.join(
            ' '.join(map(str, lr.observer_words(value))) + '\n' for value in endpoints))
        for name in ['loop-source.ir.txt', 'loop-recovered.ir.txt', 'loop-baseline.c', 'loop-candidate.c',
                     'loop-completion.smt2', 'loop-comparison.smt2', 'loop-cut-0.smt2']:
            (directory / name).write_text('metadata fixture: ' + name)
        (root / 'readable.c').write_bytes((directory / 'loop-candidate.c').read_bytes())
        candidate = dict(source_registers=40, program_registers=44, parameters=[4, 7], group=0,
                         structured=True, locals=9, completion='unsat', proof_method='cut_composition',
                         checked=1, context_model='checked-rolled-function-context-v1', outside_instructions=25,
                         original_region_instructions=90, candidate_region_instructions=32, future_reads_checked=19,
                         source_ir='loop-source.ir.txt', program_ir='loop-recovered.ir.txt', baseline_c='loop-baseline.c',
                         candidate_c='loop-candidate.c', states='loop-endpoints.jsonl')
        value = dict(schema='nirvana-loop-recovery-evaluation-v1', model=lr.MODEL, contract=lr.CONTRACT,
                     selected=True, retention=None, attempt_seconds=0.5, baseline=dict(structured=False, locals=8),
                     candidate=candidate, endpoint=dict(status='passed', cases=2, observations=8, step_limit=4096,
                     private_initializers=[0, lr.U64], comparisons=['display_zero', 'recovered_zero', 'display_ones', 'recovered_ones'],
                     witness=None))
        return directory, value, rows

    def validate(self, value, directory, **kwargs):
        return lr.validate(value, directory, 2, 4096, [4, 7], 32, **kwargs)

    def write_rows(self, directory, rows):
        (directory / 'loop-endpoints.jsonl').write_text(''.join(json.dumps(row) + '\n' for row in rows))

    def test_replays_full_endpoint_records_and_every_retained_artifact(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory, value, _ = self.fixture(Path(temporary))
            result = self.validate(value, directory)
            self.assertEqual(result['status'], 'passed')
            self.assertEqual(self.validate(result, directory, retained=True), result)
            for name in result['candidate']['artifact_sha256']:
                path = directory / name
                original = path.read_bytes()
                path.write_bytes(original + b' altered')
                with self.subTest(name=name), self.assertRaises(ProtocolError):
                    self.validate(result, directory, retained=True)
                path.write_bytes(original)

    def test_fault_ram_return_input_and_private_state_mutations_cannot_claim_success(self):
        for field in ['return', 'address', 'access', 'width', 'memory', 'input', 'ram', 'case', 'initial']:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as temporary:
                directory, value, rows = self.fixture(Path(temporary))
                row = rows[2]
                if field == 'return': rows[0]['recovered']['status']['value'] ^= 1
                elif field == 'address': row['recovered']['status']['address'] ^= 1
                elif field == 'access': row['recovered']['status']['access'] = 'write'
                elif field == 'width': row['recovered']['status']['width'] = 4
                elif field == 'memory': row['recovered']['memory'] = '00' + row['recovered']['memory'][2:]
                elif field == 'input': row['input'] = [1] + row['input'][1:]
                elif field == 'ram': row['ram'] = '00' + row['ram'][2:]
                elif field == 'case': row['case'] = 0
                else: row['initial'] = 1
                self.write_rows(directory, rows)
                with self.assertRaises(ProtocolError): self.validate(value, directory)

    def test_coverage_proof_counts_and_selected_c_are_bound(self):
        for field in ['count', 'cases', 'parameters', 'method', 'completion', 'selection', 'source', 'time', 'selected-c']:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                directory, value, _ = self.fixture(root)
                if field == 'count': value['endpoint']['observations'] -= 2
                elif field == 'cases': value['endpoint']['cases'] -= 1
                elif field == 'parameters': value['candidate']['parameters'] = [0, 1]
                elif field == 'method': value['candidate']['proof_method'] = 'assumed'
                elif field == 'completion': value['candidate']['completion'] = 'unknown'
                elif field == 'selection': value['retention'] = 'unknown'
                elif field == 'source': value['candidate']['source_ir'] = '../outside'
                elif field == 'time': value['attempt_seconds'] = float('nan')
                else: (root / 'readable.c').write_text('unrelated C')
                with self.assertRaises(ProtocolError): self.validate(value, directory)

    def test_counterexample_and_budget_limit_remain_distinct_from_success(self):
        for status in ['counterexample', 'budget_exhausted']:
            with self.subTest(status=status), tempfile.TemporaryDirectory() as temporary:
                directory, value, rows = self.fixture(Path(temporary))
                if status == 'counterexample': rows[0]['recovered']['status']['value'] ^= 1
                else: rows[0]['recovered']['status'] = {'kind': 'suspended'}
                self.write_rows(directory, rows)
                value['endpoint'].update(status=status, witness='loop-recovery.witness.txt')
                (directory / 'loop-recovery.witness.txt').write_text('replayed mismatch or bounded execution')
                self.assertEqual(self.validate(value, directory)['status'], status)

    def test_unaccepted_proof_keeps_the_original_and_has_no_candidate_observations(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory, value, _ = self.fixture(Path(temporary))
            value.update(selected=False, retention='unknown', candidate=None)
            value['endpoint'].update(status='not_applied', observations=0)
            self.assertEqual(self.validate(value, directory)['status'], 'not_applied')
            value['selected'] = True
            with self.assertRaises(ProtocolError): self.validate(value, directory)


if __name__ == '__main__':
    unittest.main()
