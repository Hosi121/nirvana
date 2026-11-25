"""Replay selected-C unsigned storage facts, separate from source IR facts.

The retained Rust checker establishes source semantics. This consumer checks the
certificate shape, local membership, and bindings to that source and emitted C.
Signed and address widths describe separate representation decisions.
"""
import json
import re

from .analysis_checks import MAX_BYTES, STORAGE_FIELDS, counts, require, storage_counts
from .semantics import sha
from .semantic_pairs import unique_object

MODEL = 'nirvana-selected-storage-v1'
CHECKER = 'value_width::validate+selected_storage::validate_locals'
EVIDENCE_FIELDS = STORAGE_FIELDS | {'local_variables', 'local_members', 'parameters'}
MANIFEST_FIELDS = {'schema', 'scope', 'status', 'source_phase', 'registers', 'entry',
                   'certificate', 'parameters', 'locals', 'reason'}
LOCAL_FIELDS = {'name', 'registers', 'unsigned_bits', 'signed_bits', 'address_bits'}
ARTIFACTS = {'input_ir': 'selected-storage-input.ir.txt',
             'selected_storage': 'selected-storage.json', 'emitted_c': 'selected-readable.c'}


def register_list(value, registers, *, nonempty=False):
    require(isinstance(value, list) and len(value) <= min(registers, 1_000_000)
            and (bool(value) or not nonempty)
            and all(type(r) is int and 0 <= r < registers for r in value)
            and len(set(value)) == len(value), 'selected storage register members')
    return value


def manifest_counts(report):
    require(isinstance(report, dict) and set(report) == MANIFEST_FIELDS
            and report['schema'] == MODEL
            and report['scope'] == 'selected-c-unsigned-width-observations'
            and report['status'] in ['checked', 'unavailable', 'rejected'],
            'selected storage manifest schema')
    if report['status'] != 'checked':
        require(all(report[field] is None for field in
                    ['source_phase', 'registers', 'entry', 'certificate', 'parameters', 'locals'])
                and isinstance(report['reason'], str) and 0 < len(report['reason']) <= 4096,
                'selected storage fallback cannot retain partial facts')
        return report['status'], None, report['reason']
    require(report['reason'] is None
            and report['source_phase'] in ['before-presentation', 'display-after-dce']
            and type(report['registers']) is int and 0 <= report['registers'] <= 1_000_000
            and type(report['entry']) is int and 0 <= report['entry'] < 2**64,
            'selected storage source boundary')
    registers = report['registers']
    status, evidence, _ = storage_counts(report['certificate'], registers, report['entry'])
    require(status == 'passed', 'selected storage requires checked certificate')
    parameters = register_list(report['parameters'], registers)
    locals_ = report['locals']
    require(isinstance(locals_, list) and len(locals_) <= 100_000, 'selected storage local bound')
    names = set()
    member_count = 0
    for local in locals_:
        require(isinstance(local, dict) and set(local) == LOCAL_FIELDS
                and isinstance(local['name'], str) and 0 < len(local['name'].encode('utf-8')) <= 256
                and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', local['name']) is not None
                and local['name'] not in names, 'selected storage local name or fields')
        names.add(local['name'])
        for field in ['unsigned_bits', 'signed_bits', 'address_bits']:
            width = local[field]
            require((field != 'unsigned_bits' and width is None)
                    or type(width) is int and width in [8, 16, 32, 64],
                    'selected storage local representation width')
        members = register_list(local['registers'], registers, nonempty=True)
        member_count += len(members)
        require(member_count <= 1_000_000, 'selected storage total member bound')
        require(all(local['unsigned_bits'] >= report['certificate']['widths'][r] for r in members),
                'selected storage local narrower than certificate')
    return 'passed', {**evidence, 'local_variables': len(locals_),
                      'local_members': member_count, 'parameters': len(parameters)}, None


def validate(entry, directory, *, retained=False):
    fields = {'name', 'model', 'checker', 'status', 'input_ir', 'selected_storage',
              'emitted_c', 'evidence', 'reason'}
    hashes = {field + '_sha256' for field in ARTIFACTS}
    require(isinstance(entry, dict) and set(entry) - hashes == fields
            and entry['name'] == 'selected_storage' and entry['model'] == MODEL
            and entry['checker'] == CHECKER
            and entry['status'] in ['passed', 'unavailable', 'rejected'],
            'selected storage check contract')
    passed = entry['status'] == 'passed'
    require(all(entry[field] == (filename if passed or field == 'selected_storage' else None)
                for field, filename in ARTIFACTS.items()), 'selected storage artifact names')
    for field, filename in ARTIFACTS.items():
        if entry[field] is None:
            require(field + '_sha256' not in entry, 'unexpected selected storage artifact hash')
            continue
        path = directory / filename
        require(path.stat().st_size <= MAX_BYTES, 'selected storage artifact size bound')
        digest = sha(path)
        require((not retained or field + '_sha256' in entry)
                and entry.get(field + '_sha256', digest) == digest, 'selected storage artifact hash')
        entry[field + '_sha256'] = digest
    report = json.loads((directory / ARTIFACTS['selected_storage']).read_text(),
                        object_pairs_hook=unique_object)
    require((entry['status'], entry['evidence'], entry['reason']) == manifest_counts(report),
            'selected storage outcome correspondence')
    if passed:
        counts(entry['evidence'], EVIDENCE_FIELDS, maximum=10_000_000)
        source = (directory / ARTIFACTS['input_ir']).read_text().splitlines()
        match = re.fullmatch(r'entry=([0-9]+) registers=([0-9]+)', source[0]) if source else None
        require(match is not None and int(match.group(1)) == report['entry']
                and int(match.group(2)) == report['registers'], 'selected storage source register binding')
        require(entry['emitted_c_sha256'] == sha(directory.parent / 'readable.c'),
                'selected storage emitted C binding')
    return entry
