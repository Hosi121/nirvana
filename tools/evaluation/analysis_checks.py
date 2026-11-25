"""Retained Rust checker evidence: shape/count/hash replay, not an SSA verifier."""
from collections import Counter
import json
import re

from .semantics import ProtocolError, sha
from .semantic_pairs import unique_object

NAMES = ('memory_ssa_graph', 'memory_ssa_queries')
V5_NAMES = NAMES + ('memory_addresses', 'unsigned_bounds')
V6_NAMES = V5_NAMES + ('storage_widths',)
VERSION_NAMES = {4: NAMES, 5: V5_NAMES, 6: V6_NAMES}
SCHEMA_NAMES = {f'nirvana-evaluation-stages-v{version}': names for version, names in VERSION_NAMES.items()}
MODELS = ('nirvana-memory-ssa-graph-v1', 'nirvana-memory-ssa-coverage-v1',
          'nirvana-modular-address-v1', 'nirvana-unsigned-bounds-v1', 'nirvana-storage-widths-v1')
CHECKERS = ('memory_ssa::validate_graph', 'memory_ssa::validate',
            'memory_ssa::validate', 'type_infer::check_bounds', 'value_width::validate')
GRAPH_FIELDS = {'blocks', 'definitions', 'accesses', 'phi_inputs', 'opaque_effects'}
QUERY_FIELDS = {'queries', 'states', 'links', 'candidate_bytes'}
ADDRESS_FIELDS = {'accesses', 'modular_forms', 'phi_inputs', 'source_atoms', 'basis_evaluations'}
BOUND_FIELDS = {'values', 'assignments', 'phi_inputs', 'expressions'}
STORAGE_FIELDS = {'registers', 'narrow_registers', 'blocks', 'edges', 'assignments', 'reads', 'expressions'}
REPORT_FIELDS = ('memory_ssa', 'memory_ssa', 'memory_ssa', 'type_constraints', 'storage_widths')
REPORT_NAMES = ('memory-ssa.json', 'memory-ssa.json', 'memory-ssa.json',
                'type-constraints.json', 'storage-widths.json')
MAX_BYTES = 16 * 1024 * 1024


def require(condition, message):
    if not condition:
        raise ProtocolError('analysis ' + message)


def counts(value, fields, maximum=8_000_000):
    require(isinstance(value, dict) and set(value) == fields
            and all(type(n) is int and 0 <= n <= maximum for n in value.values()), 'evidence counts')


def members(value):
    require(isinstance(value, list) and len(value) <= 1_000_000, 'artifact member bound')
    return value


def names_for_schema(schema):
    return SCHEMA_NAMES.get(schema, NAMES)


def names_for_rows(rows):
    return max((names_for_schema(row.get('stage_checks', {}).get('schema')) for row in rows),
               key=len, default=NAMES)


def report_counts(report):
    require(isinstance(report, dict)
            and report.get('schema') == 'nirvana-memory-ssa-v1'
            and report.get('status') == 'analyzed'
            and report.get('scope') == 'function-entry-normal-continuations'
            and report.get('reads') == 'syntactic-possible', 'artifact schema')
    definitions, blocks, accesses = (members(report[k]) for k in ['definitions', 'blocks', 'accesses'])
    require(all(d['id'] == n and type(d['id']) is int
                and d['kind'] in ['initial', 'phi', 'store', 'opaque'] for n, d in enumerate(definitions)),
            'definition records')
    require(all(a['id'] == n and type(a['id']) is int and a['kind'] in ['read', 'write']
                and type(a['width']) is int and a['width'] in [8, 16, 32, 64]
                for n, a in enumerate(accesses)), 'access records')
    phi_inputs = sum(len(members(d['inputs'])) for d in definitions if d['kind'] == 'phi')
    graph = dict(blocks=len(blocks), definitions=len(definitions), accesses=len(accesses),
                 phi_inputs=phi_inputs, opaque_effects=sum(d['kind'] == 'opaque' for d in definitions))
    verification = report.get('verification')
    require(verification is not None, 'missing graph verification record')
    if verification is not None:
        require(isinstance(verification, dict)
                and set(verification) == GRAPH_FIELDS | {'model', 'scope', 'query_coverage'}
                and verification['model'] == MODELS[0]
                and verification['scope'] == 'source-bound-generations', 'graph verification record')
        counts({k: verification[k] for k in GRAPH_FIELDS}, GRAPH_FIELDS)
        require(all(verification[k] == n for k, n in graph.items()), 'graph count correspondence')
    queries = report['queries']
    require(isinstance(queries, dict) and queries.get('status') in ['analyzed', 'unavailable'], 'query status')
    coverage = verification.get('query_coverage') if verification else None
    if queries['status'] == 'unavailable':
        require(set(queries) == {'status', 'reason'} and isinstance(queries['reason'], str)
                and bool(queries['reason']) and coverage is None, 'unavailable query record')
        return graph, None
    require(set(queries) == {'status', 'reads', 'certificates'}, 'query proof fields')
    reads, certificates = members(queries['reads']), members(queries['certificates'])
    require(all(type(q['access']) is int and 0 <= q['access'] < len(accesses)
                for q in reads + certificates), 'query/certificate access IDs')
    expected = [a['id'] for a in accesses if a['kind'] == 'read']
    require(sorted(q['access'] for q in reads) == expected
            and sorted(q['access'] for q in certificates) == expected, 'query/certificate denominator')
    state_count = sum(len(members(c['states'])) for c in certificates)
    for query in reads:
        for candidate in members(query['candidates']):
            require(type(candidate['definition']) is int and 0 <= candidate['definition'] < len(definitions)
                    and type(candidate['byte_mask']) is int and 1 <= candidate['byte_mask'] <= 255
                    and type(candidate['unknown_bytes']) is int and 0 <= candidate['unknown_bytes'] <= 255
                    and len(candidate['byte_sources']) == 8
                    and all(type(n) is int and 0 <= n <= 255 for n in candidate['byte_sources']), 'candidate shape')
    for proof in certificates:
        require(set(proof) == {'access', 'states'}, 'certificate fields')
        for state in proof['states']:
            require(set(state) == {'memory', 'byte_mask', 'address'}
                    and type(state['memory']) is int and 0 <= state['memory'] < len(definitions)
                    and type(state['byte_mask']) is int and 1 <= state['byte_mask'] <= 255, 'certificate state shape')
    if coverage is not None:
        require(isinstance(coverage, dict) and coverage.get('model') == MODELS[1], 'query verification model')
        counts({k: v for k, v in coverage.items() if k != 'model'}, QUERY_FIELDS)
        require(coverage['queries'] == len(reads) and coverage['states'] == state_count
                and len(reads) <= coverage['links'] <= len(reads) + state_count * (phi_inputs + 1)
                and coverage['candidate_bytes'] <= state_count * 8, 'query count correspondence')
    return graph, coverage


def modular_counts(report):
    verification = report.get('address_verification')
    require(isinstance(verification, dict)
            and set(verification) == ADDRESS_FIELDS | {'model', 'status', 'scope', 'phi_checked'}
            and verification['model'] == MODELS[2] and verification['status'] == 'checked'
            and verification['scope'] == 'u64-affine-equalities'
            and type(verification['phi_checked']) is bool, 'modular verification record')
    evidence = {k: verification[k] for k in ADDRESS_FIELDS}
    counts(evidence, ADDRESS_FIELDS)
    forms = 0
    for access in members(report['accesses']):
        require('identity' in access, 'missing modular identity')
        identity = access['identity']
        if identity is None:
            continue
        require(isinstance(identity, dict) and set(identity) == {'offset', 'terms'}
                and type(identity['offset']) is int and 0 <= identity['offset'] < 2**64,
                'modular identity shape')
        terms = members(identity['terms'])
        require(len(terms) <= 16 and all(isinstance(t, dict) and set(t) == {'value', 'coefficient'}
                and type(t['value']) is int and 0 <= t['value'] < 65536
                and type(t['coefficient']) is int and 0 < t['coefficient'] < 2**64 for t in terms)
                and [t['value'] for t in terms] == sorted(set(t['value'] for t in terms)),
                'canonical modular terms')
        forms += 1
    require(evidence['accesses'] == len(report['accesses'])
            and evidence['modular_forms'] == forms + evidence['phi_inputs']
            and evidence['basis_evaluations'] >= evidence['modular_forms'], 'modular count correspondence')
    if not verification['phi_checked']:
        require(evidence['phi_inputs'] == 0 and report['queries']['status'] == 'unavailable',
                'unchecked phi identities require unavailable queries')
    return {**evidence, 'phi_checked': verification['phi_checked']}


def bounds_counts(report, original_registers):
    require(isinstance(report, dict) and report.get('schema') == 'nirvana-type-constraints-v1'
            and report.get('identity') == 'ssa' and report.get('access_model') == 'syntactic-possible'
            and report.get('interpretations') == 'tentative', 'unsigned bound artifact schema')
    verification = report.get('bounds_verification')
    require(isinstance(verification, dict)
            and set(verification) == BOUND_FIELDS | {'model', 'status', 'scope'}
            and verification['model'] == MODELS[3] and verification['status'] == 'checked'
            and verification['scope'] == 'u64-integer-upper-bounds', 'unsigned bound verification record')
    evidence = {k: verification[k] for k in BOUND_FIELDS}
    counts(evidence, BOUND_FIELDS)
    values = members(report['values'])
    require(len(values) <= 65536, 'unsigned value bound')
    assignments = phi_inputs = 0
    for index, value in enumerate(values):
        require(isinstance(value, dict) and type(value.get('id')) is int and value['id'] == index
                and type(value.get('maximum_bits')) is int and 0 <= value['maximum_bits'] <= 64,
                'unsigned value records')
        origin = value['origin']
        require(isinstance(origin, dict) and origin.get('kind') in ['initial', 'assignment', 'phi']
                and type(origin.get('register')) is int and 0 <= origin['register'] < original_registers,
                'unsigned value origin')
        if origin['kind'] == 'initial':
            require(set(origin) == {'kind', 'register'} and value['maximum_bits'] == 64,
                    'unsigned initial boundary')
        elif origin['kind'] == 'assignment':
            site = origin.get('site')
            require(set(origin) == {'kind', 'register', 'site'} and isinstance(site, dict)
                    and set(site) == {'instruction', 'assignment'}
                    and type(site['instruction']) is int and 0 <= site['instruction'] < 2**64
                    and type(site['assignment']) is int and 0 <= site['assignment'] < 16384,
                    'unsigned assignment source site')
            assignments += 1
        else:
            require(set(origin) == {'kind', 'register', 'block', 'inputs'}
                    and type(origin['block']) is int and 0 <= origin['block'] < 2**64,
                    'unsigned phi source block')
            inputs = members(origin['inputs'])
            require(bool(inputs) and all(isinstance(edge, dict) and set(edge) == {'predecessor', 'value'}
                    and (edge['predecessor'] is None or type(edge['predecessor']) is int
                         and 0 <= edge['predecessor'] < 2**64)
                    and type(edge['value']) is int and 0 <= edge['value'] < len(values)
                    for edge in inputs), 'unsigned phi inputs')
            phi_inputs += len(inputs)
    require(evidence['values'] == len(values) and evidence['assignments'] == assignments
            and evidence['phi_inputs'] == phi_inputs and assignments <= 16384 and phi_inputs <= 262144
            and assignments <= evidence['expressions'] <= 65536, 'unsigned count correspondence')
    return evidence


def storage_counts(report, original_registers, input_entry):
    fields = {'schema', 'scope', 'status', 'evidence', 'widths', 'incoming',
              'entry_block', 'block_starts', 'reason'}
    require(isinstance(report, dict) and set(report) == fields
            and report['schema'] == MODELS[4]
            and report['scope'] == 'source-entry-storage-observations'
            and report['status'] in ['checked', 'unavailable', 'rejected'], 'storage artifact schema')
    require(0 <= input_entry < 2**64, 'storage input entry PC')
    if report['status'] != 'checked':
        require(all(report[field] is None for field in
                    ['evidence', 'widths', 'incoming', 'entry_block', 'block_starts'])
                and isinstance(report['reason'], str) and 0 < len(report['reason']) <= 4096,
                'storage fallback cannot retain partial facts')
        return report['status'], None, report['reason']
    require(report['reason'] is None, 'checked storage reason')
    evidence = report['evidence']
    counts(evidence, STORAGE_FIELDS, maximum=10_000_000)
    widths, incoming, starts = (members(report[field]) for field in ['widths', 'incoming', 'block_starts'])
    require(len(widths) == original_registers
            and all(type(width) is int and width in [8, 16, 32, 64] for width in widths), 'storage widths')
    require(0 < len(incoming) <= 100_000 and len(starts) == len(incoming)
            and (len(incoming) + 4) * original_registers <= 1_000_000
            and all(type(start) is int and 0 <= start < 2**64 for start in starts)
            and starts == sorted(set(starts)), 'storage CFG rows')
    for row in incoming:
        require(row is None or isinstance(row, list) and len(row) == original_registers
                and all(type(bits) is int and 0 <= bits <= 64 for bits in row), 'storage incoming row')
    entry = report['entry_block']
    require(type(entry) is int and 0 <= entry < len(incoming) and starts[entry] == input_entry
            and incoming[entry] == [64] * original_registers, 'storage arbitrary initial boundary')
    require(evidence['registers'] == original_registers
            and evidence['narrow_registers'] == sum(width < 64 for width in widths)
            and evidence['blocks'] == sum(row is not None for row in incoming)
            and evidence['edges'] <= 2 * evidence['blocks']
            and evidence['reads'] <= evidence['expressions'] <= 10_000_000
            and evidence['assignments'] <= min(100_000, evidence['expressions']),
            'storage count correspondence')
    return 'passed', evidence, None


def validate(entries, directory, original_registers, *, retained=False, version=4):
    names = VERSION_NAMES.get(version, ())
    require(version in VERSION_NAMES and isinstance(entries, list) and len(entries) == len(names)
            and all(isinstance(e, dict) for e in entries)
            and [e['name'] for e in entries] == list(names), 'check names')
    reports = {}
    for i, entry in enumerate(entries):
        report_field, report_name = REPORT_FIELDS[i], REPORT_NAMES[i]
        fields = {'name', 'model', 'checker', 'status', 'input_ir', report_field, 'evidence', 'reason'}
        require(isinstance(entry, dict)
                and set(entry) - {'input_ir_sha256', report_field + '_sha256'} == fields
                and entry['model'] == MODELS[i] and entry['checker'] == CHECKERS[i], 'check contract')
        require(entry['status'] in ['passed', 'unavailable', 'rejected'], 'check status')
        require(entry['input_ir'] == 'analysis-input.ir.txt'
                and entry[report_field] in [None, report_name], 'artifact names')
        require(i != 4 or entry[report_field] == report_name, 'storage certificate artifact required')
        for field in ['input_ir', report_field]:
            name = entry[field]
            if name is None:
                require(field + '_sha256' not in entry, 'unexpected artifact hash')
                continue
            path = directory / name
            require(path.stat().st_size <= MAX_BYTES, 'artifact size bound')
            digest = sha(path)
            require((not retained or field + '_sha256' in entry)
                    and entry.get(field + '_sha256', digest) == digest, 'artifact hash')
            entry[field + '_sha256'] = digest
            if field == 'input_ir':
                header = path.read_text().splitlines()[0]
                match = re.fullmatch(r'entry=([0-9]+) registers=' + str(original_registers), header)
                require(match is not None, 'original Low IR register binding')
                input_entry = int(match.group(1))
            elif name not in reports:
                raw = json.loads(path.read_text(), object_pairs_hook=unique_object)
                if field == 'memory_ssa':
                    graph, coverage = report_counts(raw)
                    reports[name] = [graph, {k: v for k, v in (coverage or {}).items() if k != 'model'}]
                    if version >= 5:
                        reports[name].append(modular_counts(raw))
                elif field == 'type_constraints':
                    reports[name] = bounds_counts(raw, original_registers)
                else:
                    reports[name] = storage_counts(raw, original_registers, input_entry)
        if i == 4:
            require((entry['status'], entry['evidence'], entry['reason']) == reports[report_name],
                    'storage certificate outcome correspondence')
        if entry['status'] == 'passed':
            require(entry['reason'] is None and entry[report_field] is not None, 'passed evidence artifacts')
            evidence = entry['evidence']
            count_fields = [GRAPH_FIELDS, QUERY_FIELDS, ADDRESS_FIELDS, BOUND_FIELDS, STORAGE_FIELDS][i]
            if i == 2:
                require(isinstance(evidence, dict) and type(evidence.get('phi_checked')) is bool,
                        'modular phi check boolean')
                counts({k: v for k, v in evidence.items() if k != 'phi_checked'}, count_fields)
            else:
                counts(evidence, count_fields, maximum=10_000_000 if i == 4 else 8_000_000)
            record = reports[entry[report_field]]
            if i == 4:
                expected = record[1]
            elif i == 3:
                expected = record
            else:
                expected = record[i]
            require(evidence == expected, 'checker evidence correspondence')
            require(i not in [1, 2] or entries[0]['status'] == 'passed', 'query/address graph prerequisite')
        else:
            require(entry['evidence'] is None and isinstance(entry['reason'], str)
                    and 0 < len(entry['reason']) <= 4096, 'unavailable or rejected reason')
    require(all(entry['memory_ssa'] == entries[0]['memory_ssa'] for entry in entries[:3 if version >= 5 else 2]),
            'shared analysis artifact')
    if version >= 5 and entries[1]['status'] == 'passed':
        require(entries[2]['status'] == 'passed' and entries[2]['evidence']['phi_checked'],
                'query check modular phi prerequisite')
    return entries


def summary(rows, names=None):
    names = names_for_rows(rows) if names is None else names
    return {name: dict(Counter(next((e['status'] for e in row.get('stage_checks', {}).get('analysis_checks', [])
                                     if e['name'] == name), 'not_run') for row in rows)) for name in names}
