"""Static checker claims remain separate, hashed and in every denominator."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import analysis_checks as checks, stages, reports
from evaluation.semantics import ProtocolError
from report_fixture import architecture, fixture, save


def analysis_fixture(root, *, unavailable=False, version=4, phi_checked=True):
    value = architecture(3, [0, 1, 4])
    value.update(schema='nirvana-evaluation-stages-v4', contract='nirvana-stage-input-state-v4',
                 original_registers=32)
    value['execution'].extend(dict(name=name, status='not_applied', observations=0, witness=None,
        **({'semantic': None} if name == 'selected_semantic' else {'transition': None}))
        for name in ['middle_memory', 'middle_saved', 'selected_semantic'])
    for entry in value['execution']:
        entry['comparisons'] = stages.COMPARISONS[entry['name']].copy()
    graph = dict(blocks=1, definitions=2, accesses=1, phi_inputs=1, opaque_effects=0)
    coverage = dict(queries=1, states=2, links=2, candidate_bytes=1)
    report = dict(schema='nirvana-memory-ssa-v1', status='analyzed',
        scope='function-entry-normal-continuations', reads='syntactic-possible',
        verification=dict(model=checks.MODELS[0], scope='source-bound-generations', **graph,
            query_coverage=dict(model=checks.MODELS[1], **coverage)),
        definitions=[dict(id=0, kind='initial'),
                     dict(id=1, kind='phi', block=16, inputs=[dict(predecessor=None, memory=0)])],
        blocks=[dict(start=16, entry=1, exit=1, events=[dict(access=0)])],
        accesses=[dict(id=0, kind='read', width=8)],
        queries=dict(status='analyzed', reads=[dict(access=0, translated_edges=1, address_widened=False,
            candidates=[dict(definition=0, alias='may', byte_mask=1, unknown_bytes=1, byte_sources=[0]*8)])],
            certificates=[dict(access=0, states=[dict(memory=n, byte_mask=1, address=None) for n in [0, 1]])]))
    value['analysis_checks'] = [dict(name=name, model=checks.MODELS[i], checker=checks.CHECKERS[i],
        status='passed', input_ir='analysis-input.ir.txt', memory_ssa='memory-ssa.json',
        evidence=graph.copy() if i == 0 else coverage.copy(), reason=None) for i, name in enumerate(checks.NAMES)]
    if unavailable:
        value['status'] = 'inconclusive'
        value['analysis_checks'][1].update(status='unavailable', evidence=None, reason='query work budget')
        report['verification']['query_coverage'] = None
        report['queries'] = dict(status='unavailable', reason='query work budget')
    if version == 5:
        value.update(schema='nirvana-evaluation-stages-v5', contract='nirvana-stage-input-state-v5')
        address = dict(accesses=1, modular_forms=2 if phi_checked else 1,
                       phi_inputs=1 if phi_checked else 0, phi_checked=phi_checked,
                       source_atoms=1, basis_evaluations=4)
        report['address_verification'] = dict(model=checks.MODELS[2], status='checked',
            scope='u64-affine-equalities', **address)
        report['accesses'][0]['identity'] = dict(offset=0, terms=[dict(value=0, coefficient=1)])
        bounds = dict(values=3, assignments=1, phi_inputs=1, expressions=4)
        types = dict(schema='nirvana-type-constraints-v1', identity='ssa',
            access_model='syntactic-possible', interpretations='tentative',
            bounds_verification=dict(model=checks.MODELS[3], status='checked',
                scope='u64-integer-upper-bounds', **bounds),
            values=[dict(id=0, maximum_bits=64, origin=dict(kind='initial', register=0)),
                    dict(id=1, maximum_bits=64, origin=dict(kind='phi', register=0,
                        block=16, inputs=[dict(predecessor=None, value=0)])),
                    dict(id=2, maximum_bits=8, origin=dict(kind='assignment', register=1,
                        site=dict(instruction=16, assignment=0)))])
        value['analysis_checks'].extend([
            dict(name=checks.V5_NAMES[2], model=checks.MODELS[2], checker=checks.CHECKERS[2],
                 status='passed', input_ir='analysis-input.ir.txt', memory_ssa='memory-ssa.json',
                 evidence=address.copy(), reason=None),
            dict(name=checks.V5_NAMES[3], model=checks.MODELS[3], checker=checks.CHECKERS[3],
                 status='passed', input_ir='analysis-input.ir.txt', type_constraints='type-constraints.json',
                 evidence=bounds.copy(), reason=None)])
        if not phi_checked:
            value['status'] = 'inconclusive'
            value['analysis_checks'][1].update(status='unavailable', evidence=None, reason='phi identities unavailable')
            report['verification']['query_coverage'] = None
            report['queries'] = dict(status='unavailable', reason='phi identities unavailable')
        save(root, 'type-constraints.json', json.dumps(types))
    save(root, 'analysis-input.ir.txt', 'entry=16 registers=32\noriginal Low IR\n')
    save(root, 'memory-ssa.json', json.dumps(report))
    return value, report


def bound_report(root, *, version=4, unavailable=False, phi_checked=True):
    report = fixture(root)
    row = report['rows'][0]
    destination = root / row['artifacts'] / 'semantics'
    value, _ = analysis_fixture(destination, version=version, unavailable=unavailable, phi_checked=phi_checked)
    if version == 3:
        value.update(schema='nirvana-evaluation-stages-v3', contract='nirvana-stage-input-state-v3')
        value.pop('analysis_checks')
    row['semantics']['profile'].update(step_limit=4, requested_cases=3, register_count=32)
    raw = {**row['semantics']['profile'], 'stage_checks': copy.deepcopy(value)}
    row['semantics']['prepare_stdout_sha256'] = save(destination.parent,
        'semantic_prepare.stdout.txt', json.dumps(raw))
    row['stage_checks'] = stages.validate(value, 4, destination, 3, 32)
    report['evaluation']['probe_metadata'] = 'hashed-probe-json-v1'
    report['summary']['architecture_execution'] = stages.execution_summary(report['rows'])
    report['summary']['architecture_analysis'] = checks.summary(report['rows'])
    return report


class AnalysisChecks(unittest.TestCase):
    def test_v4_retains_independent_static_checks_and_hashes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            value, _ = analysis_fixture(root)
            stages.validate(value, 4, root, 3, 32)
            self.assertEqual([e['status'] for e in value['analysis_checks']], ['passed', 'passed'])
            self.assertEqual(value['execution'][0]['observations'], 18)
            self.assertEqual(len(value['analysis_checks'][0]['input_ir_sha256']), 64)
            self.assertEqual(value['analysis_checks'][0]['memory_ssa_sha256'],
                             value['analysis_checks'][1]['memory_ssa_sha256'])
            stages.validate(value, 4, root, 3, 32, retained=True)
            value.update(schema='nirvana-evaluation-stages-v3', contract='nirvana-stage-input-state-v3')
            with self.assertRaisesRegex(ProtocolError, 'require stage v4'):
                stages.validate(value, 4, root, 3, 32)

    def test_proof_fields_counts_references_and_artifacts_cannot_disappear(self):
        for change in ['checks', 'one-check', 'name', 'checker', 'evidence', 'extra-evidence', 'graph-proof',
                       'certificates', 'state', 'candidate-reference', 'count', 'query-proof', 'header', 'hash',
                       'query-bool', 'certificate-bool', 'duplicate-key']:
            with tempfile.TemporaryDirectory() as directory, self.subTest(change=change):
                root = Path(directory)
                value, report = analysis_fixture(root)
                entries = value['analysis_checks']
                if change == 'checks': value.pop('analysis_checks')
                elif change == 'one-check': entries.pop()
                elif change == 'name': entries[1]['name'] = 'different'
                elif change == 'checker': entries[1]['checker'] = 'producer'
                elif change == 'evidence': entries[1]['evidence'] = None
                elif change == 'extra-evidence': entries[1]['evidence']['proof'] = True
                elif change == 'graph-proof': report.pop('verification')
                elif change == 'certificates': report['queries'].pop('certificates')
                elif change == 'state': report['queries']['certificates'][0]['states'].pop()
                elif change == 'candidate-reference': report['queries']['reads'][0]['candidates'][0]['definition'] = 9
                elif change == 'query-bool': report['queries']['reads'][0]['access'] = False
                elif change == 'certificate-bool': report['queries']['certificates'][0]['access'] = False
                elif change == 'count': entries[0]['evidence']['blocks'] = True
                elif change == 'query-proof': report['verification']['query_coverage'] = None
                elif change == 'header': save(root, 'analysis-input.ir.txt', 'entry=16 registers=31\n')
                elif change == 'hash':
                    stages.validate(value, 4, root, 3, 32)
                    report['queries']['reads'][0]['translated_edges'] += 1
                save(root, 'memory-ssa.json', json.dumps(report))
                if change == 'duplicate-key':
                    save(root, 'memory-ssa.json', json.dumps(report).replace('"status": "analyzed"',
                        '"status": "analyzed", "status": "analyzed"', 1))
                with self.assertRaises((ProtocolError, KeyError)):
                    stages.validate(value, 4, root, 3, 32)

    def test_query_unavailability_preserves_checked_graph_and_denominator(self):
        with tempfile.TemporaryDirectory() as directory:
            value, _ = analysis_fixture(Path(directory), unavailable=True)
            stages.validate(value, 4, Path(directory), 3, 32)
            rows = [dict(stage_checks=value), dict(status='tool_error'), dict(stage_checks={'status': 'not_run'})]
            self.assertEqual(checks.summary(rows), dict(memory_ssa_graph=dict(passed=1, not_run=2),
                memory_ssa_queries=dict(unavailable=1, not_run=2)))
            entries = value['analysis_checks']
            for entry in entries:
                entry.update(status='unavailable', evidence=None, reason='SSA unavailable', memory_ssa=None)
                entry.pop('memory_ssa_sha256')
            stages.validate(value, 4, Path(directory), 3, 32)
            entries[0]['status'] = 'rejected'
            value['status'] = 'rejected'
            stages.validate(value, 4, Path(directory), 3, 32)

    def test_replay_binds_raw_prepare_hash_and_required_retained_digests(self):
        for change in ['intact', 'input-hash', 'report-hash', 'prepare-hash', 'profile-deletion', 'raw-hash', 'raw-downgrade',
                       'stage-deletion', 'metadata-downgrade', 'duplicate-raw-key']:
            with tempfile.TemporaryDirectory() as directory, self.subTest(change=change):
                root = Path(directory)
                report = bound_report(root)
                row = report['rows'][0]
                if change in ['input-hash', 'report-hash']:
                    row['stage_checks']['analysis_checks'][0].pop(
                        'input_ir_sha256' if change == 'input-hash' else 'memory_ssa_sha256')
                elif change == 'prepare-hash': row['semantics'].pop('prepare_stdout_sha256')
                elif change == 'profile-deletion':
                    row['semantics'].pop('profile')
                    row['semantics']['status'] = 'unavailable'
                    row['stage_checks'] = {'status': 'not_run'}
                    report['summary']['architecture_execution'] = stages.execution_summary(report['rows'])
                    report['summary']['architecture_analysis'] = checks.summary(report['rows'])
                elif change == 'raw-hash':
                    path = root / row['artifacts'] / 'semantic_prepare.stdout.txt'
                    path.write_text(path.read_text() + ' ')
                elif change == 'raw-downgrade':
                    row['stage_checks'].update(schema='nirvana-evaluation-stages-v3', contract='nirvana-stage-input-state-v3')
                    row['stage_checks'].pop('analysis_checks')
                elif change == 'stage-deletion': row['stage_checks'] = {'status': 'not_run'}
                elif change == 'metadata-downgrade':
                    row['semantics'].pop('prepare_stdout_sha256')
                    report['evaluation'].pop('probe_metadata')
                elif change == 'duplicate-raw-key':
                    path = root / row['artifacts'] / 'semantic_prepare.stdout.txt'
                    raw = path.read_text().replace('"vectors": 1', '"vectors": 1, "vectors": 1', 1)
                    row['semantics']['prepare_stdout_sha256'] = save(path.parent, path.name, raw)
                if change == 'intact':
                    reports.index(report)
                    self.assertEqual(reports.replay(root, row)['architecture_analysis'],
                                     dict(memory_ssa_graph='passed', memory_ssa_queries='passed'))
                else:
                    with self.assertRaises((ValueError, KeyError)):
                        reports.index(report)
                        reports.replay(root, row)

    def test_all_row_summaries_and_comparisons_report_analysis_loss(self):
        with tempfile.TemporaryDirectory() as directory:
            a, b = Path(directory) / 'a', Path(directory) / 'b'
            before, after = bound_report(a), bound_report(b, version=3)
            def compare(left, right):
                (a / 'report.json').write_text(json.dumps(left))
                (b / 'report.json').write_text(json.dumps(right))
                return reports.compare(a / 'report.json', b / 'report.json')
            result = compare(before, after)
            self.assertEqual(result['rows'][0]['analysis_checks_lost'], list(checks.NAMES))
            self.assertEqual(result['analysis_regressions'], 1)
            self.assertEqual(result['candidate_analysis']['memory_ssa_graph'], {'not_run': 1})
            # A frozen v3 probe and v4 probe use exactly the same evaluator metadata.
            self.assertEqual(before['evaluation'], after['evaluation'])
            old, new = bound_report(a, version=3), bound_report(b)
            self.assertEqual(compare(old, new)['analysis_regressions'], 0)
            for change in ['missing', 'partial', 'count']:
                report = copy.deepcopy(before)
                if change == 'missing': report['summary'].pop('architecture_analysis')
                elif change == 'partial': report['summary']['architecture_analysis'].pop('memory_ssa_queries')
                else: report['summary']['architecture_analysis']['memory_ssa_graph']['passed'] = True
                with self.subTest(change=change), self.assertRaises(ValueError):
                    reports.index(report)

    def test_schema_deletion_cannot_preserve_passed_checks_without_artifacts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            report = bound_report(root)
            row = report['rows'][0]
            row['semantics'].pop('profile')
            row['semantics'].pop('prepare_stdout_sha256')
            row['semantics']['status'] = 'unavailable'
            row['stage_checks'].pop('schema')
            for entry in row['stage_checks']['analysis_checks']:
                entry['evidence'] = None
                entry.pop('input_ir_sha256')
                entry.pop('memory_ssa_sha256')
            for name in ['analysis-input.ir.txt', 'memory-ssa.json']:
                (root / row['artifacts'] / 'semantics' / name).unlink()
            for check in [lambda: reports.index(report), lambda: reports.replay(root, row)]:
                with self.assertRaisesRegex(ValueError, 'unversioned architecture'):
                    check()


class AnalysisChecksV5(unittest.TestCase):
    def test_v5_binds_four_checks_original_input_and_both_reports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            value, _ = analysis_fixture(root, version=5)
            stages.validate(value, 4, root, 3, 32)
            entries = value['analysis_checks']
            self.assertEqual([e['name'] for e in entries], list(checks.V5_NAMES))
            self.assertEqual([e['status'] for e in entries], ['passed'] * 4)
            self.assertEqual(len({e['input_ir_sha256'] for e in entries}), 1)
            self.assertEqual(len({e['memory_ssa_sha256'] for e in entries[:3]}), 1)
            self.assertEqual(len(entries[3]['type_constraints_sha256']), 64)
            stages.validate(value, 4, root, 3, 32, retained=True)
            rows = [dict(stage_checks=value), dict(status='tool_error'), dict(stage_checks={'status': 'not_run'})]
            self.assertEqual(checks.summary(rows), {name: dict(passed=1, not_run=2) for name in checks.V5_NAMES})

    def test_v5_proofs_typed_counts_booleans_and_hashes_cannot_be_dropped(self):
        for change in ['missing-address', 'missing-bounds', 'address-count', 'bounds-count', 'count-bool',
                       'phi-bool', 'false-phi', 'phi-incomplete', 'modular-total', 'basis-count',
                       'initial-bound', 'maximum-bool', 'value-id-bool', 'phi-value-bool',
                       'missing-site', 'site-bool', 'missing-phi-block',
                       'source-type-scope', 'input-hash', 'type-hash', 'memory-hash', 'missing-check']:
            with tempfile.TemporaryDirectory() as directory, self.subTest(change=change):
                root = Path(directory)
                value, memory = analysis_fixture(root, version=5)
                entries = value['analysis_checks']
                types = json.loads((root / 'type-constraints.json').read_text())
                if change == 'missing-address': memory.pop('address_verification')
                elif change == 'missing-bounds': types.pop('bounds_verification')
                elif change == 'address-count': entries[2]['evidence']['source_atoms'] += 1
                elif change == 'bounds-count': types['bounds_verification']['assignments'] += 1
                elif change == 'count-bool': entries[3]['evidence']['values'] = True
                elif change == 'phi-bool': memory['address_verification']['phi_checked'] = 1
                elif change == 'false-phi': entries[2]['evidence']['phi_checked'] = False
                elif change == 'phi-incomplete':
                    for evidence in [memory['address_verification'], entries[2]['evidence']]:
                        evidence.update(phi_checked=False, phi_inputs=0, modular_forms=1)
                elif change == 'modular-total':
                    memory['address_verification']['modular_forms'] = 1
                    entries[2]['evidence']['modular_forms'] = 1
                elif change == 'basis-count':
                    memory['address_verification']['basis_evaluations'] = 0
                    entries[2]['evidence']['basis_evaluations'] = 0
                elif change == 'initial-bound': types['values'][0]['maximum_bits'] = 32
                elif change == 'maximum-bool': types['values'][2]['maximum_bits'] = True
                elif change == 'value-id-bool': types['values'][0]['id'] = False
                elif change == 'phi-value-bool': types['values'][1]['origin']['inputs'][0]['value'] = False
                elif change == 'missing-site': types['values'][2]['origin'].pop('site')
                elif change == 'site-bool': types['values'][2]['origin']['site']['assignment'] = False
                elif change == 'missing-phi-block': types['values'][1]['origin'].pop('block')
                elif change == 'source-type-scope': types['bounds_verification']['scope'] = 'source-language-types'
                elif change in ['input-hash', 'type-hash', 'memory-hash']:
                    stages.validate(value, 4, root, 3, 32)
                    if change == 'input-hash': save(root, 'analysis-input.ir.txt', 'entry=16 registers=32\nchanged source\n')
                    elif change == 'type-hash': types['values'][2]['maximum_bits'] = 16
                    else: memory['accesses'][0]['identity']['offset'] = 1
                elif change == 'missing-check': entries.pop()
                save(root, 'memory-ssa.json', json.dumps(memory))
                save(root, 'type-constraints.json', json.dumps(types))
                with self.assertRaises((ProtocolError, KeyError)):
                    stages.validate(value, 4, root, 3, 32)

    def test_access_only_modular_checks_and_unavailable_paths_keep_all_names(self):
        for phi_checked in [False, True]:
            with tempfile.TemporaryDirectory() as directory, self.subTest(phi_checked=phi_checked):
                root = Path(directory)
                value, _ = analysis_fixture(root, version=5, unavailable=True, phi_checked=phi_checked)
                stages.validate(value, 4, root, 3, 32)
                self.assertEqual([e['status'] for e in value['analysis_checks']],
                                 ['passed', 'unavailable', 'passed', 'passed'])
                self.assertEqual(value['analysis_checks'][2]['evidence']['phi_checked'], phi_checked)
                for entry in value['analysis_checks'][:3]:
                    entry.update(status='unavailable', memory_ssa=None, evidence=None, reason='memory graph unavailable')
                    entry.pop('memory_ssa_sha256')
                (root / 'memory-ssa.json').unlink()
                stages.validate(value, 4, root, 3, 32, retained=True)
                self.assertEqual(checks.summary([dict(stage_checks=value)])['unsigned_bounds'], {'passed': 1})
                value['analysis_checks'][0].update(status='rejected', reason='memory SSA check mismatch: test control')
                value['status'] = 'rejected'
                stages.validate(value, 4, root, 3, 32, retained=True)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            value, _ = analysis_fixture(root, version=5)
            value['analysis_checks'][3].update(status='unavailable', type_constraints=None,
                evidence=None, reason='unsigned bounds unavailable')
            value['status'] = 'inconclusive'
            (root / 'type-constraints.json').unlink()
            stages.validate(value, 4, root, 3, 32)

    def test_v5_retained_hashes_and_raw_schema_downgrades_are_rejected(self):
        for change in ['intact', 'bounds-hash', 'address-hash', 'v4-downgrade', 'v3-downgrade']:
            with tempfile.TemporaryDirectory() as directory, self.subTest(change=change):
                root = Path(directory)
                report = bound_report(root, version=5)
                row = report['rows'][0]
                value = row['stage_checks']
                if change == 'bounds-hash': value['analysis_checks'][3].pop('type_constraints_sha256')
                elif change == 'address-hash': value['analysis_checks'][2].pop('memory_ssa_sha256')
                elif change in ['v4-downgrade', 'v3-downgrade']:
                    version = 4 if change == 'v4-downgrade' else 3
                    value.update(schema=f'nirvana-evaluation-stages-v{version}',
                                 contract=f'nirvana-stage-input-state-v{version}')
                    if version == 4: value['analysis_checks'] = value['analysis_checks'][:2]
                    else: value.pop('analysis_checks')
                    report['summary']['architecture_analysis'] = checks.summary(report['rows'])
                if change == 'intact':
                    reports.index(report)
                    self.assertEqual(reports.replay(root, row)['architecture_analysis'],
                                     dict.fromkeys(checks.V5_NAMES, 'passed'))
                else:
                    with self.assertRaises((ValueError, KeyError)):
                        reports.index(report)
                        reports.replay(root, row)

    def test_v4_v5_comparison_reports_added_and_lost_checks_with_full_denominators(self):
        with tempfile.TemporaryDirectory() as directory:
            a, b = Path(directory) / 'a', Path(directory) / 'b'
            old, new = bound_report(a, version=4), bound_report(b, version=5)
            def compare(left, right):
                save(a, 'report.json', json.dumps(left))
                save(b, 'report.json', json.dumps(right))
                return reports.compare(a / 'report.json', b / 'report.json')
            self.assertEqual(set(old['summary']['architecture_analysis']), set(checks.NAMES))
            self.assertEqual(set(new['summary']['architecture_analysis']), set(checks.V5_NAMES))
            result = compare(old, new)
            self.assertEqual(result['analysis_regressions'], 0)
            self.assertEqual(result['rows'][0]['analysis_checks_added'], ['memory_addresses', 'unsigned_bounds'])
            old, new = bound_report(a, version=5), bound_report(b, version=4)
            result = compare(old, new)
            self.assertEqual(result['rows'][0]['analysis_checks_lost'], ['memory_addresses', 'unsigned_bounds'])
            self.assertEqual(result['analysis_regressions'], 1)
            self.assertEqual(result['candidate_analysis']['unsigned_bounds'], {'not_run': 1})
            for change in ['missing', 'partial', 'bool']:
                broken = copy.deepcopy(old)
                if change == 'missing': broken['summary'].pop('architecture_analysis')
                elif change == 'partial': broken['summary']['architecture_analysis'].pop('unsigned_bounds')
                else: broken['summary']['architecture_analysis']['unsigned_bounds']['passed'] = True
                with self.subTest(change=change), self.assertRaises(ValueError):
                    reports.index(broken)

    def test_comparison_detects_phi_scope_loss_even_when_access_checks_still_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            a, b = Path(directory) / 'a', Path(directory) / 'b'
            before = bound_report(a, version=5, unavailable=True)
            after = bound_report(b, version=5, unavailable=True, phi_checked=False)
            save(a, 'report.json', json.dumps(before))
            save(b, 'report.json', json.dumps(after))
            result = reports.compare(a / 'report.json', b / 'report.json')
            self.assertEqual(result['rows'][0]['analysis_checks_lost'], ['memory_addresses.phi_inputs'])
            self.assertEqual(result['analysis_regressions'], 1)
            result = reports.compare(b / 'report.json', a / 'report.json')
            self.assertEqual(result['rows'][0]['analysis_checks_added'], ['memory_addresses.phi_inputs'])
            self.assertEqual(result['analysis_regressions'], 0)


if __name__ == '__main__':
    unittest.main()
