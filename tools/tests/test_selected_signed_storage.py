"""Selected signed facts bind the final display source, SSA and C independently."""
import copy
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import analysis_checks as checks, reports, stages, selected_signed_storage as signed
from evaluation.semantics import ProtocolError
from report_fixture import save
from test_selected_storage import selected_fixture, selected_report


def add_signed(root, value, status='checked'):
    registers = 36
    widths = [64] * registers
    widths[1:3] = [16, 8]
    evidence = dict(registers=registers, narrow_registers=2, values=registers + 2,
                    constants=1, blocks=2, phi_inputs=0, assignments=2, reads=3, expressions=5)
    certificate = dict(schema='nirvana-signed-storage-v1',
                       scope='source-entry-sign-extension-observations', status='checked',
                       evidence=evidence, widths=widths,
                       values=[{'signed_bits': 64}] * registers + [{'signed_bits': 16}, {'constant': 7}],
                       entry=64, registers=registers, reason=None)
    manifest = dict(schema=signed.MODEL, scope='selected-c-sign-extension-observations',
                    status=status, source_phase='prepared-display', registers=registers, entry=64,
                    certificate=certificate, parameters=[0, 34],
                    locals=[dict(name='signed_value', registers=[1], unsigned_bits=64,
                                 signed_bits=16, address_bits=None),
                            dict(name='byte_value', registers=[2], unsigned_bits=8,
                                 signed_bits=None, address_bits=None)], reason=None)
    passed = status == 'checked'
    if passed:
        save(root, signed.ARTIFACTS['input_ir'], 'entry=64 registers=36\nfinal display IR\n')
        save(root, signed.ARTIFACTS['input_ssa'], 'entry=64 registers=36 values=38\nchecked SSA\n')
        save(root, signed.ARTIFACTS['emitted_c'], (root.parent / 'readable.c').read_text())
    else:
        for field in ['source_phase', 'registers', 'entry', 'certificate', 'parameters', 'locals']:
            manifest[field] = None
        manifest['reason'] = 'signed inference resource limit' if status == 'unavailable' else 'invalid signed fact'
        value['status'] = 'inconclusive' if status == 'unavailable' else 'rejected'
    save(root, signed.ARTIFACTS['selected_signed_storage'], json.dumps(manifest))
    value.update(schema='nirvana-evaluation-stages-v8', contract='nirvana-stage-input-state-v8')
    value['analysis_checks'].append(dict(name='selected_signed_storage', model=signed.MODEL,
        checker=signed.CHECKER, status='passed' if passed else status,
        **{key: filename if passed or key == 'selected_signed_storage' else None
           for key, filename in signed.ARTIFACTS.items()},
        evidence={**evidence, 'local_variables': 2, 'local_members': 2,
                  'signed_locals': 1, 'signed_members': 1, 'parameters': 2} if passed else None,
        reason=manifest['reason']))
    return manifest


def fixture(root, status='checked'):
    value, _ = selected_fixture(root)
    return value, add_signed(root, value, status)


def bound_report(root, status='checked'):
    report = selected_report(root)
    row = report['rows'][0]
    directory = root / row['artifacts'] / 'semantics'
    add_signed(directory, row['stage_checks'], status)
    raw = {**row['semantics']['profile'], 'stage_checks': copy.deepcopy(row['stage_checks'])}
    row['semantics']['prepare_stdout_sha256'] = save(directory.parent,
        'semantic_prepare.stdout.txt', json.dumps(raw))
    stages.validate(row['stage_checks'], 4, directory, 3, 32)
    report['summary']['architecture_analysis'] = checks.summary(report['rows'])
    return report


class SelectedSignedStorage(unittest.TestCase):
    def test_replay_identity_pins_both_selected_fact_helpers(self):
        identity = checks.implementation()
        self.assertEqual(set(identity), {'analysis_checks.py', 'selected_storage.py',
                                        'selected_signed_storage.py'})
        self.assertTrue(all(len(value) == 64 for value in identity.values()))

    def test_final_display_source_ssa_and_c_have_separate_bindings(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'semantics'
            value, _ = fixture(root)
            stages.validate(value, 4, root, 3, 32)
            stages.validate(value, 4, root, 3, 32, retained=True)
            self.assertEqual([e['name'] for e in value['analysis_checks']], list(checks.V8_NAMES))
            self.assertEqual([e['status'] for e in value['analysis_checks']], ['passed'] * 7)
            self.assertEqual(len({value['analysis_checks'][i]['input_ir_sha256'] for i in [0, 5, 6]}), 3)
            self.assertEqual(value['analysis_checks'][6]['evidence']['signed_locals'], 1)
            self.assertEqual(checks.summary([dict(stage_checks=value), dict(status='tool_error')]),
                             {name: dict(passed=1, not_run=1) for name in checks.V8_NAMES})

    def test_certificate_and_local_mutations_are_rejected(self):
        changes = [
            lambda m: m.update(source_phase='before-presentation'),
            lambda m: m.update(registers=True),
            lambda m: m.update(entry=48),
            lambda m: m['certificate'].update(status='rejected'),
            lambda m: m['certificate']['widths'].__setitem__(1, True),
            lambda m: m['certificate']['values'].__setitem__(0, {'constant': True}),
            lambda m: m['certificate']['values'].__setitem__(0, {'constant': -1}),
            lambda m: m['certificate']['values'].__setitem__(0, {'constant': 2**64}),
            lambda m: m['certificate']['values'].__setitem__(0, {'signed_bits': 7}),
            lambda m: m['certificate']['values'].__setitem__(0, {'signed_bits': 8, 'constant': 1}),
            lambda m: m['certificate']['values'].pop(),
            lambda m: m['certificate']['evidence'].update(constants=2),
            lambda m: m['certificate']['evidence'].update(narrow_registers=1),
            lambda m: m['locals'][0].update(signed_bits=8),
            lambda m: m['locals'][0].update(signed_bits=64),
            lambda m: m['locals'][0].update(address_bits=16),
            lambda m: m['locals'][0].update(unsigned_bits=16),
            lambda m: m['locals'][0].update(registers=[1, 1]),
            lambda m: m['locals'][1].update(registers=[1]),
            lambda m: m['parameters'].append(1),
            lambda m: m['locals'][0].update(name='bad-name'),
            lambda m: m['locals'][1].update(name='signed_value'),
        ]
        for index, change in enumerate(changes):
            with tempfile.TemporaryDirectory() as temporary, self.subTest(index=index):
                root = Path(temporary) / 'semantics'
                value, manifest = fixture(root)
                change(manifest)
                save(root, signed.ARTIFACTS['selected_signed_storage'], json.dumps(manifest))
                with self.assertRaises(ProtocolError):
                    stages.validate(value, 4, root, 3, 32)

    def test_all_four_artifacts_and_raw_source_dimensions_are_load_bearing(self):
        for change in ['ir-boundary', 'ssa-boundary', 'ssa-values', 'c-binding',
                       *['missing-' + k for k in signed.ARTIFACTS],
                       *['size-' + k for k in signed.ARTIFACTS]]:
            with tempfile.TemporaryDirectory() as temporary, self.subTest(change=change):
                root = Path(temporary) / 'semantics'
                value, _ = fixture(root)
                if change == 'ir-boundary': save(root, signed.ARTIFACTS['input_ir'], 'entry=64 registers=35\nunsigned input\n')
                elif change == 'ssa-boundary': save(root, signed.ARTIFACTS['input_ssa'], 'entry=48 registers=36 values=38\nSSA\n')
                elif change == 'ssa-values': save(root, signed.ARTIFACTS['input_ssa'], 'entry=64 registers=36 values=37\nSSA\n')
                elif change == 'c-binding': save(root.parent, 'readable.c', 'changed C')
                else:
                    kind, key = change.split('-', 1)
                    path = root / signed.ARTIFACTS[key]
                    if kind == 'missing': path.unlink()
                    else:
                        with path.open('r+b') as stream: stream.truncate(checks.MAX_BYTES + 1)
                with self.assertRaises((ProtocolError, OSError)):
                    stages.validate(value, 4, root, 3, 32)

    def test_fallback_has_reason_and_no_partial_facts(self):
        for status in ['unavailable', 'rejected']:
            with tempfile.TemporaryDirectory() as temporary, self.subTest(status=status):
                root = Path(temporary) / 'semantics'
                value, manifest = fixture(root, status)
                stages.validate(value, 4, root, 3, 32, retained=False)
                stages.validate(value, 4, root, 3, 32, retained=True)
                self.assertEqual(value['analysis_checks'][6]['status'], status)
                for key in ['certificate', 'locals', 'source_phase', 'registers', 'reason']:
                    bad = copy.deepcopy(manifest)
                    bad[key] = None if key == 'reason' else []
                    with self.subTest(key=key), self.assertRaises(ProtocolError):
                        signed.manifest_counts(bad)

    def test_reports_replay_relocation_and_proof_addition_loss(self):
        with tempfile.TemporaryDirectory() as temporary:
            a, b = Path(temporary) / 'a', Path(temporary) / 'b'
            old, new = selected_report(a), bound_report(b)
            reports.index(new)
            moved = Path(temporary) / 'moved'
            shutil.copytree(b, moved)
            self.assertEqual(reports.replay(moved, new['rows'][0])['architecture_analysis'],
                             dict.fromkeys(checks.V8_NAMES, 'passed'))
            save(a, 'report.json', json.dumps(old)); save(b, 'report.json', json.dumps(new))
            result = reports.compare(a / 'report.json', b / 'report.json')
            self.assertEqual(result['analysis_regressions'], 0)
            self.assertEqual(result['rows'][0]['analysis_checks_added'], ['selected_signed_storage'])
            reverse = reports.compare(b / 'report.json', a / 'report.json')
            self.assertEqual(reverse['analysis_regressions'], 1)
            self.assertEqual(reverse['rows'][0]['analysis_checks_lost'], ['selected_signed_storage'])
            entry = new['rows'][0]['stage_checks']['analysis_checks'][6]
            entry.pop('input_ssa_sha256')
            with self.assertRaises((ProtocolError, ValueError)):
                reports.replay(b, new['rows'][0])


if __name__ == '__main__':
    unittest.main()
