"""Register compression preserves complete logical observations and byte hashes."""
import copy
import hashlib
import itertools
import json
from pathlib import Path
import random
import shutil
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import state_record_codec as codec, semantic_pairs, middle_pairs, stages, reports
from evaluation.semantics import ProtocolError
from report_fixture import fixture, save, semantic_architecture
import test_semantic_pairs as semantic_fixture
import test_middle_pairs as middle_fixture


def digest(data):
    return hashlib.sha256(data).hexdigest()


def runs(values):
    return {'rle': [[sum(1 for _ in group), value] for value, group in itertools.groupby(values)]}


def record(row, *, encoded=False, overrides=None):
    """Independent producer-like serializer; no decoder token/span helpers."""
    overrides = overrides or {}
    def render(value, path=()):
        if path in overrides:
            return overrides[path]
        if len(path) == 2 and path[0] in ['expected', 'actual'] and path[1] == 'registers':
            dense = json.dumps(value)
            packed = json.dumps(runs(value), separators=(',', ':'))
            return packed if encoded and len(packed) < len(dense) else dense
        if isinstance(value, dict):
            return '{' + ', '.join(json.dumps(k) + ': ' + render(v, path + (k,)) for k, v in value.items()) + '}'
        if isinstance(value, list):
            return '[' + ', '.join(render(v, path + (i,)) for i, v in enumerate(value)) + ']'
        return json.dumps(value, ensure_ascii=False)
    return (render(row) + '\n').encode('utf-8')


def metadata(legacy):
    return {'encoding': codec.ENCODING, 'decoded_bytes': len(legacy)}


class RecordCodecTests(unittest.TestCase):
    def row(self, values):
        return {'note': 'α "expected": {"registers":{"rle":[[99999,1]]}}',
                'expected': {'registers': values, 'trace': [1, 2]},
                'actual': {'registers': values.copy(), 'trace': [1, 2]}}

    def test_dense_and_rle_roundtrips_preserve_every_other_byte_and_source_dimension(self):
        rng = random.Random(11)
        for count in [0, 1, 2, 32, 34, 238, 307, 4096, 5000]:
            for repeated in [False, True]:
                values = ([rng.randrange(2**64)] * count if repeated else
                          [rng.randrange(2**64) for _ in range(count)])
                row = self.row(values)
                legacy, encoded = record(row), record(row, encoded=True)
                decoder = codec.Decoder(metadata(legacy), count)
                self.assertEqual(decoder.decode(encoded), row)
                self.assertEqual(decoder.summary(), {'sha256': digest(encoded), 'encoding': codec.ENCODING,
                    'decoded_bytes': len(legacy), 'decoded_sha256': digest(legacy)})
                dense = codec.Decoder({}, count)
                self.assertEqual(dense.decode(legacy), row)
                self.assertEqual(dense.summary(), {'sha256': digest(legacy)})
        row = self.row([0] * 238)
        legacy = b' \t' + record(row).rstrip(b'\n') + b' \r\n'
        encoded = b' \t' + record(row, encoded=True).rstrip(b'\n') + b' \r\n'
        decoder = codec.Decoder(metadata(legacy), 238)
        decoder.decode(encoded)
        self.assertEqual(decoder.summary()['decoded_sha256'], digest(legacy))

    def test_invalid_counts_values_keys_canonical_spelling_and_source_quotas_are_rejected(self):
        row = self.row([0] * 238)
        legacy = record(row)
        invalid = [
            '{"rle":[[0,0]]}', '{"rle":[[-1,0]]}', '{"rle":[[true,0]]}',
            '{"rle":[[238,true]]}', '{"rle":[[238,-1]]}', '{"rle":[[238,18446744073709551616]]}',
            '{"rle":[[32,0]]}', '{"rle":[[244,0]]}', '{"rle":[[239,0]]}',
            '{"rle":[[119,0],[119,0]]}', '{"rle":[[238,0]],"extra":0}',
            '{"rle":[[238,0]],"rle":[[238,0]]}', '{"rle": [[238, 0]]}',
            '{"rle":[[238,0,1]]}', '{"rle":[238,0]}', '{"rle":null}',
            '{"rle":[[100000000000000000000000000000000,0]]}',
            '[0,0]', '[true]', '{"rle":[[238,0.0]]}',
        ]
        for token in invalid:
            raw = record(row, encoded=True, overrides={('expected', 'registers'): token})
            with self.subTest(token=token), self.assertRaises(ProtocolError):
                codec.Decoder(metadata(legacy), 238).decode(raw)
        for encoding in [None, '', 'rle', False]:
            with self.subTest(encoding=encoding), self.assertRaises(ProtocolError):
                codec.Decoder({**metadata(legacy), 'encoding': encoding}, 238)
        for extra in [{'decoded_bytes': 0}, {'decoded_sha256': '0' * 64}]:
            with self.assertRaises(ProtocolError):
                codec.Decoder(extra, 238)

    def test_total_logical_limits_are_checked_before_either_run_is_expanded(self):
        row = self.row([codec.MAX_U64] * 238)
        legacy, encoded = record(row), record(row, encoded=True)
        decoder = codec.Decoder(metadata(legacy), 238, max_line_bytes=len(legacy) - 1)
        self.assertLess(len(encoded), len(legacy) - 1)
        with mock.patch.object(codec, 'range', side_effect=AssertionError('expanded before quota'), create=True):
            with self.assertRaisesRegex(ProtocolError, 'decoded row budget'):
                decoder.decode(encoded)
        decoder = codec.Decoder({'encoding': codec.ENCODING, 'decoded_bytes': 2 * len(legacy) - 1}, 238,
                                max_bytes=2 * len(legacy) - 1)
        decoder.decode(encoded)
        with mock.patch.object(codec, 'range', side_effect=AssertionError('expanded before quota'), create=True):
            with self.assertRaisesRegex(ProtocolError, 'decoded file budget'):
                decoder.decode(encoded)
        for source in [32, 244, 307]:
            with mock.patch.object(codec, 'range', side_effect=AssertionError('expanded before quota'), create=True):
                with self.assertRaises(ProtocolError):
                    codec.Decoder(metadata(legacy), source).decode(encoded)
        # This is the semantic snapshot domain, not the narrower signed-SSA
        # inference domain. Its two legal register quotas still exceed the
        # unchanged logical row budget and must never allocate dense arrays.
        token = b'{"rle":[[1000000,0]]}'
        raw = b'{"expected":{"registers":' + token + b'},"actual":{"registers":' + token + b'}}\n'
        size = len(raw) + 2 * (3_000_000 - len(token))
        decoder = codec.Decoder({'encoding': codec.ENCODING, 'decoded_bytes': size}, 1_000_000)
        with mock.patch.object(codec, 'range', side_effect=AssertionError('expanded before quota'), create=True):
            with self.assertRaisesRegex(ProtocolError, 'decoded row budget'):
                decoder.decode(raw)

    def test_duplicate_snapshot_keys_partial_records_and_dense_fallback_canonicality_are_checked(self):
        row = self.row([0] * 34)
        legacy, encoded = record(row), record(row, encoded=True)
        mutants = [encoded[:-1], encoded.replace(b'"expected":', b'"expected": {}, "expected":', 1),
                   encoded.replace(b'"registers":', b'"registers": [], "registers":', 1),
                   b'{"expected":{},"actual":{}}\n']
        for raw in mutants:
            with self.assertRaises(ProtocolError):
                codec.Decoder(metadata(legacy), 34).decode(raw)
        # A short dense token is retained by the writer, with exact Debug spacing.
        row = self.row([0, 1])
        compact = record(row, overrides={('expected', 'registers'): '[0,1]'})
        with self.assertRaisesRegex(ProtocolError, 'canonical dense'):
            codec.Decoder(metadata(record(row)), 2).decode(compact)


class RecordProtocolTests(unittest.TestCase):
    def semantic(self, root, *, mismatch=False):
        evidence, budgets, rows = semantic_fixture.StatePairTests().fixture(root)
        if mismatch:
            rows[-1]['actual']['registers'][0] ^= 1
        legacy = b''.join(record(row) for row in rows)
        encoded = b''.join(record(row, encoded=True) for row in rows)
        (root / semantic_pairs.FILENAME).write_bytes(encoded)
        meta = {'model': semantic_pairs.MODEL, 'file': semantic_pairs.FILENAME, **metadata(legacy)}
        entry = {'status': 'counterexample' if mismatch else 'passed', 'observations': len(rows)}
        return evidence, budgets, rows, legacy, encoded, meta, entry

    def test_semantic_complete_snapshots_and_both_retained_hashes_are_required(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            evidence, budgets, _, legacy, encoded, meta, entry = self.semantic(root)
            result = semantic_pairs.validate(meta, entry, evidence, budgets, 3, root, 32)
            self.assertEqual((result['rows'], result['mismatches']), (18, 0))
            self.assertEqual((result['sha256'], result['decoded_sha256'], result['decoded_bytes']),
                             (digest(encoded), digest(legacy), len(legacy)))
            self.assertEqual(semantic_pairs.validate(result, entry, evidence, budgets, 3, root, 32, retained=True), result)
            for key in ['sha256', 'decoded_sha256', 'decoded_bytes']:
                broken = {k: v for k, v in result.items() if k != key}
                with self.subTest(missing=key), self.assertRaises(ProtocolError):
                    semantic_pairs.validate(broken, entry, evidence, budgets, 3, root, 32, retained=True)
                with self.subTest(changed=key), self.assertRaises(ProtocolError):
                    semantic_pairs.validate({**result, key: 1 if key == 'decoded_bytes' else '0' * 64},
                        entry, evidence, budgets, 3, root, 32, retained=True)
            with self.assertRaises(ProtocolError):
                semantic_pairs.validate({'model': semantic_pairs.MODEL, 'file': semantic_pairs.FILENAME},
                                        entry, evidence, budgets, 3, root, 32)

    def test_encoded_counterexamples_faults_coverage_and_initial_binding_keep_their_meaning(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            evidence, budgets, rows, legacy, _, meta, entry = self.semantic(root, mismatch=True)
            result = semantic_pairs.validate(meta, entry, evidence, budgets, 3, root, 32)
            self.assertEqual(result['mismatches'], 1)
            self.assertEqual(result['decoded_sha256'], digest(legacy))
            with self.assertRaises(ProtocolError):
                semantic_pairs.validate(meta, {**entry, 'status': 'passed'}, evidence, budgets, 3, root, 32)
            for change in ['ram', 'fault', 'pc', 'trace', 'input', 'order', 'initial']:
                _, _, data, _, _, _, _ = self.semantic(root)
                if change == 'ram': data[-1]['actual']['memory'][0] ^= 1
                elif change == 'fault': data[-1]['actual']['status'] = [1, 99, 2, 8]
                elif change == 'pc': data[-1]['actual']['instruction'] = 99
                elif change == 'trace': data[-1]['actual']['trace'] = [17]
                elif change == 'input': data[0]['input'][7] ^= 1
                elif change == 'order': data[0], data[1] = data[1], data[0]
                else:
                    for side in ['expected', 'actual']: data[0][side]['registers'][-1] = 9
                dense = b''.join(record(row) for row in data)
                (root / semantic_pairs.FILENAME).write_bytes(b''.join(record(row, encoded=True) for row in data))
                with self.subTest(change=change), self.assertRaises(ProtocolError):
                    semantic_pairs.validate({**meta, **metadata(dense)}, {'status': 'passed', 'observations': len(data)},
                                            evidence, budgets, 3, root, 32)

    def test_both_middle_transitions_pass_retained_through_stages_and_relocate(self):
        for saved in [False, True]:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory) / 'original'; root.mkdir()
                value, entry, rows = middle_fixture.MiddlePairTests().fixture(root, saved)
                legacy = b''.join(record(row) for row in rows)
                name = entry['transition']['state_pairs']['file']
                (root / name).write_bytes(b''.join(record(row, encoded=True) for row in rows))
                entry['transition']['state_pairs'].update(metadata(legacy))
                with self.assertRaises(ProtocolError):
                    stages.validate(copy.deepcopy(value), 4, root, 3, 32, retained=True)
                result = stages.validate(value, 4, root, 3, 32)
                observed = entry['transition']['state_pairs']
                self.assertEqual(observed['decoded_sha256'], digest(legacy))
                self.assertEqual(stages.validate(copy.deepcopy(result), 4, root, 3, 32, retained=True), result)
                relocated = Path(directory) / 'relocated'; shutil.copytree(root, relocated)
                self.assertEqual(stages.validate(copy.deepcopy(result), 4, relocated, 3, 32, retained=True), result)

    def test_raw_probe_replay_still_binds_hashes_and_reattached_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            report = fixture(root)
            row = report['rows'][0]
            destination = root / row['artifacts'] / 'semantics'
            evidence, budgets, _, _, _, meta, _ = self.semantic(destination)
            (destination / 'input.ir').rename(destination / 'selected-semantic-input.ir.txt')
            (destination / 'selected-semantic-lowered.ir.txt').write_text('lowered IR\n')
            row['semantics']['profile'].update(register_count=32, step_limit=4, requested_cases=3)
            raw_stages = semantic_architecture(3, budgets)
            semantic = raw_stages['execution'][-1]['semantic']
            semantic.update(source_registers=34, lowered_registers=37, state_pairs=meta)
            raw_probe = {**row['semantics']['profile'], 'stage_checks': copy.deepcopy(raw_stages)}
            row['semantics']['prepare_stdout_sha256'] = save(root / row['artifacts'],
                'semantic_prepare.stdout.txt', json.dumps(raw_probe))
            row['stage_checks'] = stages.validate(raw_stages, 4, destination, 3, 32)
            report['summary']['architecture_execution'] = stages.execution_summary(report['rows'])
            self.assertEqual(reports.replay(root, row)['semantic_state_pairs'], 'replayed')
            row['stage_checks']['execution'][-1]['semantic']['state_pairs'].pop('decoded_sha256')
            with self.assertRaises(ValueError):
                reports.replay(root, row)


if __name__ == '__main__':
    unittest.main()
