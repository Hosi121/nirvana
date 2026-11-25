"""The v7 proof binds actual selected storage and C without changing raw facts."""
import copy
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import analysis_checks as checks, reports, selected_storage as selected, stages
from evaluation.semantics import ProtocolError
from report_fixture import save
from test_analysis_checks import analysis_fixture, bound_report


def add_selected(root, value, *, registers=35, phase='display-after-dce', status='checked'):
    evidence = dict(registers=registers, narrow_registers=1, blocks=2, edges=1,
                    assignments=1, reads=1, expressions=3)
    widths = [64] * registers
    widths[1] = 8
    certificate = dict(schema=checks.MODELS[4], scope='source-entry-storage-observations',
                       status='checked', evidence=evidence, widths=widths,
                       incoming=[None, [64] * registers, widths.copy()], entry_block=1,
                       block_starts=[8, 48, 64], reason=None)
    manifest = dict(schema=selected.MODEL, scope='selected-c-unsigned-width-observations',
                    status=status, source_phase=phase, registers=registers, entry=48,
                    certificate=certificate, parameters=[0, registers - 1],
                    locals=[dict(name='byte_value', registers=[1], unsigned_bits=8,
                                 signed_bits=8, address_bits=None),
                            dict(name='wide_value', registers=[0, registers - 1], unsigned_bits=64,
                                 signed_bits=8, address_bits=16),
                            dict(name='byte_alias', registers=[1], unsigned_bits=16,
                                 signed_bits=None, address_bits=None)], reason=None)
    outcome, reason = 'passed', None
    if status != 'checked':
        outcome = status
        reason = 'selected storage budget' if status == 'unavailable' else 'invalid selected local width'
        for field in ['source_phase', 'registers', 'entry', 'certificate', 'parameters', 'locals']:
            manifest[field] = None
        manifest['reason'] = reason
        value['status'] = 'inconclusive' if status == 'unavailable' else 'rejected'
    else:
        save(root, 'selected-storage-input.ir.txt', f'entry=48 registers={registers}\nselected Low IR\n')
        readable = root.parent / 'readable.c'
        if not readable.exists():
            save(root.parent, 'readable.c', 'int nirvana_readable(void) { return 0; }\n')
        save(root, 'selected-readable.c', readable.read_text())
    save(root, 'selected-storage.json', json.dumps(manifest))
    value.update(schema='nirvana-evaluation-stages-v7', contract='nirvana-stage-input-state-v7')
    value['analysis_checks'].append(dict(name='selected_storage', model=selected.MODEL,
        checker=selected.CHECKER, status=outcome,
        input_ir='selected-storage-input.ir.txt' if outcome == 'passed' else None,
        selected_storage='selected-storage.json',
        emitted_c='selected-readable.c' if outcome == 'passed' else None,
        evidence={**evidence, 'local_variables': 3, 'local_members': 4, 'parameters': 2}
                 if outcome == 'passed' else None, reason=reason))
    return manifest


def selected_fixture(root, **options):
    value, _ = analysis_fixture(root, version=6)
    return value, add_selected(root, value, **options)


def selected_report(root, **options):
    report = bound_report(root, version=6)
    row = report['rows'][0]
    directory = root / row['artifacts'] / 'semantics'
    value = row['stage_checks']
    add_selected(directory, value, **options)
    raw = {**row['semantics']['profile'], 'stage_checks': copy.deepcopy(value)}
    row['semantics']['prepare_stdout_sha256'] = save(directory.parent,
        'semantic_prepare.stdout.txt', json.dumps(raw))
    stages.validate(value, 4, directory, 3, 32)
    report['summary']['architecture_analysis'] = checks.summary(report['rows'])
    return report


class SelectedStorage(unittest.TestCase):
    def test_actual_source_can_use_same_or_different_register_space_and_both_phases(self):
        for registers in [32, 35]:
            for phase in ['before-presentation', 'display-after-dce']:
                with tempfile.TemporaryDirectory() as temporary, self.subTest(registers=registers, phase=phase):
                    root = Path(temporary) / 'semantics'
                    value, manifest = selected_fixture(root, registers=registers, phase=phase)
                    stages.validate(value, 4, root, 3, 32)
                    entries = value['analysis_checks']
                    self.assertEqual([entry['name'] for entry in entries], list(checks.V7_NAMES))
                    self.assertEqual([entry['status'] for entry in entries], ['passed'] * 6)
                    self.assertEqual(len({entry['input_ir_sha256'] for entry in entries[:5]}), 1)
                    self.assertNotEqual(entries[0]['input_ir_sha256'], entries[5]['input_ir_sha256'])
                    self.assertEqual(entries[5]['evidence']['registers'], registers)
                    self.assertEqual(entries[5]['evidence']['local_members'], 4)
                    self.assertEqual(manifest['locals'][1]['signed_bits'], 8)
                    self.assertEqual(manifest['locals'][1]['address_bits'], 16)
                    stages.validate(value, 4, root, 3, 32, retained=True)
                    rows = [dict(stage_checks=value), dict(status='tool_error')]
                    self.assertEqual(checks.summary(rows),
                                     {name: dict(passed=1, not_run=1) for name in checks.V7_NAMES})

    def test_strict_manifest_local_members_and_certificate_reject_mutants(self):
        changes = ['missing-status', 'schema', 'scope', 'extra', 'checked-reason', 'phase', 'phase-null',
                   'register-bool', 'register-count', 'entry-bool', 'entry-range', 'certificate-status',
                   'certificate-rejected', 'certificate-null',
                   'certificate-width-bool', 'certificate-row-bool', 'certificate-cell-budget',
                   'locals-null', 'local-extra', 'local-missing', 'name-empty', 'name-invalid',
                   'name-long', 'name-duplicate', 'members-empty', 'member-duplicate', 'member-bool',
                   'member-negative', 'member-range', 'unsigned-narrow', 'unsigned-invalid',
                   'unsigned-bool', 'unsigned-null', 'signed-bool', 'address-invalid',
                   'parameter-null', 'parameter-duplicate', 'parameter-bool', 'parameter-range',
                   'evidence-count', 'evidence-bool', 'evidence-extra', 'duplicate-key', 'nested-duplicate']
        for change in changes:
            with tempfile.TemporaryDirectory() as temporary, self.subTest(change=change):
                root = Path(temporary) / 'semantics'
                value, manifest = selected_fixture(root)
                entry = value['analysis_checks'][5]
                local = manifest['locals'][0]
                cert = manifest['certificate']
                if change == 'missing-status': manifest.pop('status')
                elif change == 'schema': manifest['schema'] = 'nirvana-selected-storage-v0'
                elif change == 'scope': manifest['scope'] = 'source-language-types'
                elif change == 'extra': manifest['extra'] = None
                elif change == 'checked-reason': manifest['reason'] = 'budget'
                elif change == 'phase': manifest['source_phase'] = 'raw-original'
                elif change == 'phase-null': manifest['source_phase'] = None
                elif change == 'register-bool': manifest['registers'] = True
                elif change == 'register-count': manifest['registers'] = 32
                elif change == 'entry-bool': manifest['entry'] = True
                elif change == 'entry-range': manifest['entry'] = 2**64
                elif change in ['certificate-status', 'certificate-rejected']:
                    cert.update(status='unavailable' if change == 'certificate-status' else 'rejected',
                                reason='unsigned certificate unavailable or invalid')
                    for field in ['evidence', 'widths', 'incoming', 'entry_block', 'block_starts']:
                        cert[field] = None
                elif change == 'certificate-null': manifest['certificate'] = None
                elif change == 'certificate-width-bool': cert['widths'][1] = True
                elif change == 'certificate-row-bool': cert['incoming'][1][0] = True
                elif change == 'certificate-cell-budget':
                    cert['incoming'] = [None] * 28568
                    cert['incoming'][1] = [64] * 35
                    cert['block_starts'] = [8, 48] + list(range(64, 64 + 28566))
                elif change == 'locals-null': manifest['locals'] = None
                elif change == 'local-extra': local['extra'] = None
                elif change == 'local-missing': local.pop('address_bits')
                elif change == 'name-empty': local['name'] = ''
                elif change == 'name-invalid': local['name'] = 'x; return 0'
                elif change == 'name-long': local['name'] = 'x' * 257
                elif change == 'name-duplicate': local['name'] = manifest['locals'][1]['name']
                elif change == 'members-empty': local['registers'] = []
                elif change == 'member-duplicate': local['registers'] = [1, 1]
                elif change == 'member-bool': local['registers'] = [True]
                elif change == 'member-negative': local['registers'] = [-1]
                elif change == 'member-range': local['registers'] = [35]
                elif change == 'unsigned-narrow': manifest['locals'][1]['unsigned_bits'] = 32
                elif change == 'unsigned-invalid': local['unsigned_bits'] = 7
                elif change == 'unsigned-bool': local['unsigned_bits'] = True
                elif change == 'unsigned-null': local['unsigned_bits'] = None
                elif change == 'signed-bool': local['signed_bits'] = True
                elif change == 'address-invalid': local['address_bits'] = 0
                elif change == 'parameter-null': manifest['parameters'] = None
                elif change == 'parameter-duplicate': manifest['parameters'] = [0, 0]
                elif change == 'parameter-bool': manifest['parameters'] = [False]
                elif change == 'parameter-range': manifest['parameters'] = [35]
                elif change == 'evidence-count': entry['evidence']['local_members'] += 1
                elif change == 'evidence-bool': entry['evidence']['assignments'] = True
                elif change == 'evidence-extra': entry['evidence']['signed_checked'] = True
                raw = json.dumps(manifest)
                if change == 'duplicate-key':
                    raw = raw.replace('"status": "checked"', '"status": "checked", "status": "checked"', 1)
                elif change == 'nested-duplicate':
                    raw = raw.replace('"unsigned_bits": 8', '"unsigned_bits": 8, "unsigned_bits": 8', 1)
                save(root, 'selected-storage.json', raw)
                with self.assertRaises((ProtocolError, KeyError)):
                    stages.validate(value, 4, root, 3, 32)

    def test_local_and_member_totals_have_independent_bounds(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'semantics'
            _, manifest = selected_fixture(root)
            too_many_locals = copy.deepcopy(manifest)
            too_many_locals['locals'] = [manifest['locals'][0]] * 100_001
            with self.assertRaisesRegex(ProtocolError, 'local bound'):
                selected.manifest_counts(too_many_locals)
            manifest['locals'] = [dict(name=f'v{index}', registers=list(range(35)), unsigned_bits=64,
                                      signed_bits=None, address_bits=None) for index in range(28_572)]
            with self.assertRaisesRegex(ProtocolError, 'total member bound'):
                selected.manifest_counts(manifest)

    def test_check_artifacts_and_both_source_bindings_are_mandatory(self):
        for change in ['missing-check', 'missing-status', 'checker', 'model', 'input-name', 'manifest-name',
                       'c-name', 'null-c', 'extra-field', 'source-registers', 'source-entry', 'source-empty',
                       'original-registers', 'c-binding', 'missing-input', 'missing-manifest', 'missing-c',
                       'input-size', 'manifest-size', 'c-size']:
            with tempfile.TemporaryDirectory() as temporary, self.subTest(change=change):
                root = Path(temporary) / 'semantics'
                value, _ = selected_fixture(root)
                entry = value['analysis_checks'][5]
                if change == 'missing-check': value['analysis_checks'].pop()
                elif change == 'missing-status': entry.pop('status')
                elif change == 'checker': entry['checker'] = 'value_width::analyze'
                elif change == 'model': entry['model'] = checks.MODELS[4]
                elif change == 'input-name': entry['input_ir'] = 'analysis-input.ir.txt'
                elif change == 'manifest-name': entry['selected_storage'] = '../selected-storage.json'
                elif change == 'c-name': entry['emitted_c'] = '../readable.c'
                elif change == 'null-c': entry['emitted_c'] = None
                elif change == 'extra-field': entry['unsigned_checked'] = True
                elif change == 'source-registers': save(root, 'selected-storage-input.ir.txt', 'entry=48 registers=32\n')
                elif change == 'source-entry': save(root, 'selected-storage-input.ir.txt', 'entry=16 registers=35\n')
                elif change == 'source-empty': save(root, 'selected-storage-input.ir.txt', '')
                elif change == 'original-registers': save(root, 'analysis-input.ir.txt', 'entry=16 registers=35\n')
                elif change == 'c-binding': save(root.parent, 'readable.c', 'changed C\n')
                elif change.startswith('missing-'):
                    field = {'missing-input': 'input_ir', 'missing-manifest': 'selected_storage', 'missing-c': 'emitted_c'}[change]
                    (root / entry[field]).unlink()
                elif change.endswith('-size'):
                    field = {'input-size': 'input_ir', 'manifest-size': 'selected_storage', 'c-size': 'emitted_c'}[change]
                    with (root / entry[field]).open('r+b') as stream:
                        stream.truncate(checks.MAX_BYTES + 1)
                with self.assertRaises((ProtocolError, KeyError, OSError)):
                    stages.validate(value, 4, root, 3, 32)

    def test_both_fallbacks_retain_manifest_without_partial_facts(self):
        for status in ['unavailable', 'rejected']:
            with tempfile.TemporaryDirectory() as temporary, self.subTest(status=status):
                root = Path(temporary) / 'semantics'
                value, manifest = selected_fixture(root, status=status)
                stages.validate(value, 4, root, 3, 32)
                entry = value['analysis_checks'][5]
                self.assertEqual([e['status'] for e in value['analysis_checks']], ['passed'] * 5 + [status])
                self.assertEqual(value['status'], 'inconclusive' if status == 'unavailable' else 'rejected')
                self.assertEqual(set(entry) & {'input_ir_sha256', 'emitted_c_sha256'}, set())
                self.assertEqual(len(entry['selected_storage_sha256']), 64)
                stages.validate(value, 4, root, 3, 32, retained=True)
                for field in ['source_phase', 'registers', 'entry', 'certificate', 'parameters', 'locals', 'reason']:
                    bad = copy.deepcopy(manifest)
                    bad[field] = None if field == 'reason' else []
                    save(root, 'selected-storage.json', json.dumps(bad))
                    entry.pop('selected_storage_sha256', None)
                    with self.subTest(field=field), self.assertRaises(ProtocolError):
                        stages.validate(value, 4, root, 3, 32)
                save(root, 'selected-storage.json', json.dumps(manifest))
                for field in ['evidence', 'reason', 'status', 'input_ir', 'emitted_c']:
                    bad = copy.deepcopy(value)
                    bad['analysis_checks'][5].pop('selected_storage_sha256', None)
                    replacement = dict(evidence={}, reason=None, status='passed', **selected.ARTIFACTS)
                    bad['analysis_checks'][5][field] = replacement[field]
                    with self.subTest(field=field), self.assertRaises(ProtocolError):
                        stages.validate(bad, 4, root, 3, 32)

    def test_replay_hashes_raw_record_denominators_and_relocation(self):
        for change in ['intact', 'input-hash', 'manifest-hash', 'c-hash', 'input-tamper', 'manifest-tamper',
                       'c-tamper', 'c-binding', 'missing-metadata', 'v6-downgrade', 'missing-denominator',
                       'partial-denominator', 'bool-denominator']:
            with tempfile.TemporaryDirectory() as temporary, self.subTest(change=change):
                root = Path(temporary) / 'original'
                report = selected_report(root)
                row = report['rows'][0]
                entry = row['stage_checks']['analysis_checks'][5]
                directory = root / row['artifacts'] / 'semantics'
                if change.endswith('-hash'):
                    field = {'input-hash': 'input_ir', 'manifest-hash': 'selected_storage', 'c-hash': 'emitted_c'}[change]
                    entry.pop(field + '_sha256')
                elif change.endswith('-tamper'):
                    field = {'input-tamper': 'input_ir', 'manifest-tamper': 'selected_storage', 'c-tamper': 'emitted_c'}[change]
                    path = directory / entry[field]
                    path.write_text(path.read_text() + '\n')
                elif change == 'c-binding': row['readable_sha256'] = save(directory.parent, 'readable.c', 'changed C')
                elif change == 'missing-metadata': row['semantics'].pop('prepare_stdout_sha256')
                elif change == 'v6-downgrade':
                    row['stage_checks'].update(schema='nirvana-evaluation-stages-v6', contract='nirvana-stage-input-state-v6')
                    row['stage_checks']['analysis_checks'].pop()
                    report['summary']['architecture_analysis'] = checks.summary(report['rows'])
                elif change == 'missing-denominator': report['summary'].pop('architecture_analysis')
                elif change == 'partial-denominator': report['summary']['architecture_analysis'].pop('selected_storage')
                elif change == 'bool-denominator': report['summary']['architecture_analysis']['selected_storage']['passed'] = True
                if change == 'intact':
                    reports.index(report)
                    relocated = Path(temporary) / 'relocated'
                    shutil.copytree(root, relocated)
                    replayed = reports.replay(relocated, row)
                    self.assertEqual(replayed['architecture_analysis'], dict.fromkeys(checks.V7_NAMES, 'passed'))
                    self.assertEqual(replayed['probe_metadata'], 'replayed')
                else:
                    with self.assertRaises((ValueError, KeyError, OSError)):
                        reports.index(report)
                        reports.replay(root, row)

    def test_legacy_replay_and_comparison_retain_selected_proof_addition_and_loss(self):
        with tempfile.TemporaryDirectory() as temporary:
            a, b = Path(temporary) / 'a', Path(temporary) / 'b'
            def compare(left, right):
                save(a, 'report.json', json.dumps(left))
                save(b, 'report.json', json.dumps(right))
                return reports.compare(a / 'report.json', b / 'report.json')
            for version in [4, 5, 6]:
                legacy, current = bound_report(a, version=version), selected_report(b)
                reports.index(legacy)
                replayed = reports.replay(a, legacy['rows'][0])
                self.assertEqual(set(replayed['architecture_analysis']), set(checks.VERSION_NAMES[version]))
                result = compare(legacy, current)
                self.assertIn('selected_storage', result['rows'][0]['analysis_checks_added'])
                self.assertEqual(result['analysis_regressions'], 0)
            current, legacy = selected_report(a), bound_report(b, version=6)
            result = compare(current, legacy)
            self.assertEqual(result['rows'][0]['analysis_checks_lost'], ['selected_storage'])
            self.assertEqual(result['analysis_regressions'], 1)
            self.assertEqual(result['candidate_analysis']['selected_storage'], {'not_run': 1})
            for status in ['unavailable', 'rejected']:
                fallback = selected_report(b, status=status)
                result = compare(current, fallback)
                self.assertEqual(result['rows'][0]['analysis_checks_lost'], ['selected_storage'])
                self.assertEqual(result['candidate_analysis']['selected_storage'], {status: 1})


if __name__ == '__main__':
    unittest.main()
