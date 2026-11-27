"""Replay loop endpoint observations and artifact identity, separately from SMT.

The retained Rust certificate reports model acceptance. This module independently
checks concrete return/RAM/first-fault records; it does not reconstruct that proof.
"""
import copy
import json
import math
import re
from collections import Counter

from .semantics import ProtocolError, sha
from .semantic_pairs import unique_object

MODEL = 'checked-readable-loop-selection-v1'
CONTRACT = 'return-all-ram-first-fault-v1'
MAX_BYTES = 16 * 1024 * 1024
U64 = 2**64 - 1
HEX = re.compile('[0-9a-f]{1024}\\Z')


def require(condition, message):
    if not condition:
        raise ProtocolError('loop recovery ' + message)


def unsigned(value):
    return type(value) is int and 0 <= value <= U64


def endpoint(value):
    require(isinstance(value, dict) and set(value) == {'status', 'memory'}
            and isinstance(value['memory'], str) and HEX.fullmatch(value['memory']), 'RAM record')
    status = value['status']
    require(isinstance(status, dict), 'endpoint status')
    if status.get('kind') == 'returned':
        require(set(status) == {'kind', 'value'} and unsigned(status['value']), 'return record')
    elif status.get('kind') == 'fault':
        require(set(status) == {'kind', 'address', 'access', 'width'}
                and unsigned(status['address']) and status['access'] in ['read', 'write']
                and type(status['width']) is int and status['width'] in [1, 2, 4, 8], 'first fault record')
    else:
        require(status == {'kind': 'suspended'}, 'suspension record')
    return status['kind']


def observer_words(value):
    status = value['status']
    if status['kind'] == 'returned':
        words = [0, 0, 0, 0, status['value']]
    elif status['kind'] == 'fault':
        words = [1, status['address'], 1 if status['access'] == 'read' else 2, status['width'], 0]
    else:
        return None
    memory = bytes.fromhex(value['memory'])
    return words + [int.from_bytes(memory[n:n+8], 'little') for n in range(0, 512, 8)]


def entry_attempt(value, attempt_seconds):
    if value is None:
        return
    require(isinstance(value, dict) and set(value) == {
        'status', 'phase', 'header', 'normalizers', 'before_lanes', 'after_lanes', 'seconds'
    }, 'entry attempt fields')
    status = value['status']
    require(status in ['not_applicable', 'skipped_budget', 'build_unavailable', 'fact_unknown',
            'fact_counterexample', 'proved_unused', 'proposal_unavailable', 'candidate_unproved',
            'context_unavailable', 'used_in_ir'], 'entry attempt status')
    require(type(value['seconds']) in [int, float] and math.isfinite(value['seconds'])
            and 0 <= value['seconds'] <= attempt_seconds, 'entry attempt time')
    require(all(type(value[k]) is int for k in ['normalizers', 'before_lanes', 'after_lanes'])
            and 3 <= value['before_lanes'] <= value['after_lanes'] <= 8
            and (value['after_lanes'] > value['before_lanes']) == (status == 'used_in_ir'),
            'entry lane coverage')
    has_predicate = status not in ['not_applicable', 'skipped_budget', 'build_unavailable']
    require((unsigned(value['header']) if has_predicate else value['header'] is None)
            and (1 <= value['normalizers'] <= 16 if has_predicate else value['normalizers'] == 0),
            'entry predicate boundary')
    require((value['phase'] in ['base', 'feedback'] if status in ['fact_unknown', 'fact_counterexample']
             else value['phase'] is None), 'entry failure phase')


def entry_artifacts(value, attempt):
    if attempt['status'] != 'used_in_ir':
        require(value is None, 'unused entry certificate')
        return []
    require(isinstance(value, dict) and set(value) == {
        'model', 'header', 'source_registers', 'normalizers', 'base', 'feedback',
        'source_ir', 'normalizers_ir', 'base_smt', 'feedback_smt'
    }, 'entry certificate fields')
    require(value['model'] == 'checked-loop-entry-induction-v1'
            and unsigned(value['header']) and value['header'] == attempt['header']
            and type(value['source_registers']) is int and 0 < value['source_registers'] <= 126
            and type(value['normalizers']) is int and value['normalizers'] == attempt['normalizers']
            and value['base'] == value['feedback'] == 'unsat', 'entry certificate boundary')
    files = {'source_ir': 'loop-entry-source.ir.txt', 'normalizers_ir': 'loop-entry-normalizers.ir.txt',
             'base_smt': 'loop-entry-base.smt2', 'feedback_smt': 'loop-entry-feedback.smt2'}
    require(all(value[k] == name for k, name in files.items()), 'entry artifact names')
    return list(files.values())


def validate(value, directory, requested, step_limit, parameters, original_registers, *, retained=False):
    v2 = isinstance(value, dict) and value.get('schema') == 'nirvana-loop-recovery-evaluation-v2'
    require(isinstance(value, dict) and set(value) == {
        'schema', 'model', 'contract', 'selected', 'retention', 'attempt_seconds', 'baseline', 'candidate', 'endpoint'
    } | ({'entry_attempt'} if v2 else set()) | ({'status'} if retained else set()), 'record fields')
    result = copy.deepcopy(value)
    require(value['schema'] in ['nirvana-loop-recovery-evaluation-v1', 'nirvana-loop-recovery-evaluation-v2'] and value['model'] == MODEL
            and value['contract'] == CONTRACT and type(value['selected']) is bool, 'model or selection')
    require(type(value['attempt_seconds']) in [int, float] and math.isfinite(value['attempt_seconds'])
            and value['attempt_seconds'] >= 0, 'attempt time')
    if v2:
        entry_attempt(value['entry_attempt'], value['attempt_seconds'])
    require(value['retention'] in [None, 'provenance_unavailable', 'unknown', 'counterexample', 'incomplete',
            'no_groups', 'recovery_unavailable', 'rendering_unavailable', 'parameters', 'quality']
            and (value['retention'] is None) == value['selected'], 'retention status')
    baseline = value['baseline']
    require(isinstance(baseline, dict) and set(baseline) == {'structured', 'locals'}
            and type(baseline['structured']) is bool and type(baseline['locals']) is int
            and 0 <= baseline['locals'] <= 100_000, 'baseline shape')
    check = value['endpoint']
    require(isinstance(check, dict) and set(check) == {'status', 'cases', 'observations', 'step_limit',
            'private_initializers', 'comparisons', 'witness'} | ({'witness_sha256'} if 'witness_sha256' in check else set()),
            'endpoint fields')
    require(type(check['cases']) is int and check['cases'] == requested
            and type(check['step_limit']) is int and check['step_limit'] == step_limit
            and check['private_initializers'] == [0, U64]
            and all(type(n) is int for n in check['private_initializers'])
            and check['comparisons'] == ['display_zero', 'recovered_zero', 'display_ones', 'recovered_ones'],
            'endpoint contract or coverage')
    status = check['status']
    require(status in ['passed', 'not_applied', 'counterexample', 'rejected', 'budget_exhausted']
            and type(check['observations']) is int and 0 <= check['observations'] <= requested * 4,
            'endpoint status or count')
    if value['candidate'] is None:
        require(not value['selected'] and status == 'not_applied' and check['observations'] == 0
                and check['witness'] is None, 'missing candidate')
        if v2 and value['entry_attempt'] is not None:
            require(value['retention'] in ['rendering_unavailable', 'parameters'],
                    'entry attempt requires a recovered IR')
    else:
        candidate = value['candidate']
        require(status != 'not_applied', 'candidate requires endpoint observations')
        fields = {'source_registers', 'program_registers', 'parameters', 'group', 'structured', 'locals',
                  'completion', 'proof_method', 'checked', 'context_model', 'outside_instructions',
                  'original_region_instructions', 'candidate_region_instructions', 'future_reads_checked',
                  'source_ir', 'program_ir', 'baseline_c', 'candidate_c', 'states'}
        require(isinstance(candidate, dict) and set(candidate) == fields
                | ({'entry_invariants'} if v2 else set()) | ({'artifact_sha256'} if retained else set()),
                'candidate fields')
        counts = fields - {'parameters', 'structured', 'completion', 'proof_method', 'context_model',
                          'source_ir', 'program_ir', 'baseline_c', 'candidate_c', 'states'}
        require(all(type(candidate[k]) is int and 0 <= candidate[k] <= 1_000_000 for k in counts)
                and 0 < candidate['source_registers'] <= candidate['program_registers']
                and type(candidate['structured']) is bool
                and candidate['completion'] == 'unsat' and candidate['checked'] > 0
                and candidate['proof_method'] in ['cut_composition', 'exhaustive_partitions']
                and candidate['context_model'] == 'checked-rolled-function-context-v1', 'candidate proof boundary')
        require(candidate['parameters'] == parameters and all(type(n) is int for n in parameters)
                and len(parameters) == len(set(parameters)), 'original parameter binding')
        files = {'source_ir': 'loop-source.ir.txt', 'program_ir': 'loop-recovered.ir.txt',
                 'baseline_c': 'loop-baseline.c', 'candidate_c': 'loop-candidate.c', 'states': 'loop-endpoints.jsonl'}
        require(all(candidate[k] == name for k, name in files.items()), 'artifact names')
        names = list(files.values()) + ['loop-completion.smt2', 'loop-comparison.smt2']
        if v2:
            require(value['entry_attempt'] is not None, 'missing entry attempt')
            names += entry_artifacts(candidate['entry_invariants'], value['entry_attempt'])
        if candidate['proof_method'] == 'cut_composition':
            require(candidate['checked'] <= 48, 'cut obligation count')
            names += [f'loop-cut-{n}.smt2' for n in range(candidate['checked'])]
        else:
            require(candidate['checked'] <= 4096, 'partition count')
            names += [f'loop-part-{n}.smt2' for n in range(candidate['checked'])]
        hashes = {}
        for name in names:
            path = directory / name
            require(path.stat().st_size <= MAX_BYTES, 'artifact budget')
            hashes[name] = sha(path)
        if retained:
            require(candidate['artifact_sha256'] == hashes, 'artifact identity')
        result['candidate']['artifact_sha256'] = hashes
        selected = directory.parent / 'readable.c'
        require(sha(selected) == hashes['loop-candidate.c' if value['selected'] else 'loop-baseline.c'],
                'selected C differs from candidate/baseline')
        rows = (directory / files['states']).read_text().splitlines()
        require(len(rows) <= requested * 2 and check['observations'] == len(rows) * 2
                and (status != 'passed' or len(rows) == requested * 2), 'state coverage denominator')
        expected = [[int(word) for word in line.split()] for line in
                    (directory / 'generated-expected.txt').read_text().splitlines()]
        inputs = [[int(word) for word in line.split()] for line in
                  (directory / 'generated-inputs.txt').read_text().splitlines()]
        mismatch = False
        suspended = False
        for n, line in enumerate(rows):
            row = json.loads(line, object_pairs_hook=unique_object)
            require(isinstance(row, dict) and set(row) == {'case', 'initial', 'input', 'ram', 'machine', 'display', 'recovered'}
                    and type(row['case']) is int and row['case'] == n // 2
                    and type(row['initial']) is int and row['initial'] == [0, U64][n % 2]
                    and isinstance(row['input'], list) and len(row['input']) == original_registers
                    and all(unsigned(word) for word in row['input'])
                    and isinstance(row['ram'], str) and HEX.fullmatch(row['ram']), 'state pair identity')
            kinds = [endpoint(row[key]) for key in ['machine', 'display', 'recovered']]
            suspended |= 'suspended' in kinds
            mismatch |= ('suspended' not in kinds and any(row[key] != row['machine'] for key in ['display', 'recovered']))
            if status == 'passed':
                require(len(expected) == requested and observer_words(row['machine']) == expected[row['case']],
                        'machine endpoint differs from the checked-C reference')
                require(len(inputs) == requested and len(inputs[row['case']]) == 5
                        and original_registers >= 8, 'input ABI profile')
                address, *words = inputs[row['case']]
                registers = [0] * original_registers
                registers[4], registers[7] = 4600, address
                memory = bytearray((n * 29 + 7) & 255 for n in range(512))
                for word, data in enumerate(words):
                    location = address + word * 8
                    if 4096 <= location <= 4096 + 512 - 8 and location <= U64:
                        memory[location-4096:location-4096+8] = data.to_bytes(8, 'little')
                require(row['input'] == registers and row['ram'] == memory.hex(),
                        'state input differs from the fixed checked-C profile')
        require(status != 'passed' or not mismatch and not suspended, 'false endpoint success')
        require(status != 'counterexample' or mismatch, 'missing concrete mismatch')
    witness = check['witness']
    require((witness is None) == (status in ['passed', 'not_applied']), 'witness status')
    if witness is not None:
        require(witness == 'loop-recovery.witness.txt', 'witness name')
        digest = sha(directory / witness)
        require(check.get('witness_sha256', digest) == digest, 'witness hash')
        result['endpoint']['witness_sha256'] = digest
    if retained:
        require(value['status'] == status, 'aggregate status')
    result['status'] = status
    return result


def attach(value, row, directory, requested, step_limit, *, required):
    if value is None and not required:
        return
    try:
        require(required and value is not None, 'explicit evaluation profile required')
        parameters = row['stage_checks']['selected_c']['parameter_registers']
        row['loop_recovery'] = validate(value, directory, requested, step_limit, parameters,
                                        row['stage_checks']['original_registers'])
    except (ProtocolError, OSError, ValueError, KeyError, TypeError, IndexError) as error:
        row['loop_recovery'] = {'status': 'evaluator_error', 'reason': str(error)}
    status = row['loop_recovery']['status']
    row.setdefault('stages', {})['loop_recovery'] = status
    if status in ['counterexample', 'rejected', 'evaluator_error']:
        row['status'] = status
        row.setdefault('failures', []).append({'stage': 'loop_recovery', 'status': status,
                                               'error': 'see retained loop recovery evidence'})


def summary(rows):
    return dict(Counter(row.get('loop_recovery', {}).get('status', 'not_run') for row in rows))


def entry_summary(rows):
    def status(row):
        record = row.get('loop_recovery', {})
        if record.get('schema') == 'nirvana-loop-recovery-evaluation-v2':
            return (record.get('entry_attempt') or {}).get('status', 'not_attempted')
        return 'legacy_unrecorded' if record.get('schema') else 'not_run'
    return dict(Counter(status(row) for row in rows))
