"""Replay source-bound signed storage and its actual selected C local widths.

Rust checks the SSA semantics and sign-extension invariants. This reader checks
the retained shapes, membership and source/SSA/C hash bindings separately.
"""
import json
import re

from .analysis_checks import MAX_BYTES, counts, require
from .selected_storage import LOCAL_FIELDS, register_list
from .semantics import sha
from .semantic_pairs import unique_object

MODEL = 'nirvana-selected-signed-storage-v1'
CHECKER = 'signed_width::validate+selected_signed_storage::validate_locals'
SIGNED_FIELDS = {'registers', 'narrow_registers', 'values', 'constants', 'blocks',
                 'phi_inputs', 'assignments', 'reads', 'expressions'}
EVIDENCE_FIELDS = SIGNED_FIELDS | {'local_variables', 'local_members', 'signed_locals',
                                 'signed_members', 'parameters'}
MANIFEST_FIELDS = {'schema', 'scope', 'status', 'source_phase', 'registers', 'entry',
                   'certificate', 'parameters', 'locals', 'reason'}
ARTIFACTS = {'input_ir': 'selected-signed-input.ir.txt', 'input_ssa': 'selected-signed-ssa.txt',
             'selected_signed_storage': 'selected-signed-storage.json',
             'emitted_c': 'selected-signed-readable.c'}


def certificate_counts(report, registers, entry):
    fields = {'schema', 'scope', 'status', 'evidence', 'widths', 'values',
              'entry', 'registers', 'reason'}
    require(isinstance(report, dict) and set(report) == fields
            and report['schema'] == 'nirvana-signed-storage-v1'
            and report['scope'] == 'source-entry-sign-extension-observations'
            and report['status'] == 'checked' and report['reason'] is None,
            'selected signed checked certificate')
    require(type(report['registers']) is int and report['registers'] == registers
            and type(report['entry']) is int and report['entry'] == entry,
            'selected signed certificate boundary')
    evidence = report['evidence']
    counts(evidence, SIGNED_FIELDS, maximum=32_000_000)
    widths, values = report['widths'], report['values']
    require(isinstance(widths, list) and len(widths) == registers
            and all(type(w) is int and w in [8, 16, 32, 64] for w in widths)
            and isinstance(values, list) and len(values) <= 65536,
            'selected signed candidate dimensions')
    constants = 0
    for value in values:
        require(isinstance(value, dict) and len(value) == 1,
                'selected signed value fields')
        if set(value) == {'constant'}:
            require(type(value['constant']) is int and 0 <= value['constant'] < 2**64,
                    'selected signed exact constant')
            constants += 1
        else:
            require(set(value) == {'signed_bits'} and type(value['signed_bits']) is int
                    and value['signed_bits'] in [8, 16, 32, 64],
                    'selected signed representation fact')
    require(evidence['registers'] == registers and evidence['values'] == len(values)
            and evidence['constants'] == constants
            and evidence['narrow_registers'] == sum(w < 64 for w in widths)
            and evidence['blocks'] <= 2048 and evidence['assignments'] <= 16384
            and evidence['phi_inputs'] <= 262144
            and evidence['reads'] <= evidence['expressions'],
            'selected signed evidence correspondence')
    return evidence


def manifest_counts(report):
    require(isinstance(report, dict) and set(report) == MANIFEST_FIELDS
            and report['schema'] == MODEL
            and report['scope'] == 'selected-c-sign-extension-observations'
            and report['status'] in ['checked', 'unavailable', 'rejected'],
            'selected signed manifest schema')
    if report['status'] != 'checked':
        require(all(report[k] is None for k in
                    ['source_phase', 'registers', 'entry', 'certificate', 'parameters', 'locals'])
                and isinstance(report['reason'], str) and 0 < len(report['reason']) <= 4096,
                'selected signed fallback cannot retain partial facts')
        return report['status'], None, report['reason']
    require(report['source_phase'] == 'prepared-display' and report['reason'] is None
            and type(report['registers']) is int and 0 <= report['registers'] <= 4096
            and type(report['entry']) is int and 0 <= report['entry'] < 2**64,
            'selected signed source boundary')
    registers = report['registers']
    evidence = certificate_counts(report['certificate'], registers, report['entry'])
    parameters = register_list(report['parameters'], registers)
    locals_ = report['locals']
    require(isinstance(locals_, list) and len(locals_) <= 100_000, 'selected signed local bound')
    names, assigned = set(), set(parameters)
    members = signed_locals = signed_members = 0
    for local in locals_:
        require(isinstance(local, dict) and set(local) == LOCAL_FIELDS
                and isinstance(local['name'], str) and 0 < len(local['name']) <= 256
                and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', local['name']) is not None
                and local['name'] not in names, 'selected signed local name or fields')
        names.add(local['name'])
        for field in ['unsigned_bits', 'signed_bits', 'address_bits']:
            value = local[field]
            require((field != 'unsigned_bits' and value is None)
                    or type(value) is int and value in [8, 16, 32, 64],
                    'selected signed local representation width')
        registers_ = register_list(local['registers'], registers, nonempty=True)
        require(not assigned.intersection(registers_), 'selected signed member assigned twice')
        assigned.update(registers_)
        members += len(registers_)
        require(members <= 1_000_000, 'selected signed total member bound')
        if local['signed_bits'] is not None:
            require(local['unsigned_bits'] == 64 and local['address_bits'] is None
                    and local['signed_bits'] < 64
                    and all(report['certificate']['widths'][r] <= local['signed_bits']
                            for r in registers_), 'selected signed local narrower than certificate')
            signed_locals += 1
            signed_members += len(registers_)
    return 'passed', {**evidence, 'local_variables': len(locals_), 'local_members': members,
                      'signed_locals': signed_locals, 'signed_members': signed_members,
                      'parameters': len(parameters)}, None


def validate(entry, directory, *, retained=False):
    fields = {'name', 'model', 'checker', 'status', *ARTIFACTS, 'evidence', 'reason'}
    hashes = {name + '_sha256' for name in ARTIFACTS}
    require(isinstance(entry, dict) and set(entry) - hashes == fields
            and entry['name'] == 'selected_signed_storage' and entry['model'] == MODEL
            and entry['checker'] == CHECKER
            and entry['status'] in ['passed', 'unavailable', 'rejected'],
            'selected signed check contract')
    passed = entry['status'] == 'passed'
    require(all(entry[key] == (name if passed or key == 'selected_signed_storage' else None)
                for key, name in ARTIFACTS.items()), 'selected signed artifact names')
    for field, filename in ARTIFACTS.items():
        if entry[field] is None:
            require(field + '_sha256' not in entry, 'unexpected selected signed artifact hash')
            continue
        path = directory / filename
        require(path.stat().st_size <= MAX_BYTES, 'selected signed artifact size bound')
        digest = sha(path)
        require((not retained or field + '_sha256' in entry)
                and entry.get(field + '_sha256', digest) == digest,
                'selected signed artifact hash')
        entry[field + '_sha256'] = digest
    report = json.loads((directory / ARTIFACTS['selected_signed_storage']).read_text(),
                        object_pairs_hook=unique_object)
    require((entry['status'], entry['evidence'], entry['reason']) == manifest_counts(report),
            'selected signed outcome correspondence')
    if passed:
        counts(entry['evidence'], EVIDENCE_FIELDS, maximum=32_000_000)
        for key, pattern, expected in [
            ('input_ir', r'entry=([0-9]+) registers=([0-9]+)',
             (report['entry'], report['registers'])),
            ('input_ssa', r'entry=([0-9]+) registers=([0-9]+) values=([0-9]+)',
             (report['entry'], report['registers'], report['certificate']['evidence']['values'])),
        ]:
            source = (directory / ARTIFACTS[key]).read_text().splitlines()
            match = re.fullmatch(pattern, source[0]) if len(source) >= 2 else None
            require(match is not None and tuple(map(int, match.groups())) == expected,
                    'selected signed source/SSA binding')
        require(entry['emitted_c_sha256'] == sha(directory.parent / 'readable.c'),
                'selected signed emitted C binding')
    return entry
