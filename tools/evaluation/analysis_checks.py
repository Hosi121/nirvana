"""Retained Rust checker evidence: shape/count/hash replay, not an SSA verifier."""
from collections import Counter
import json
import re

from .semantics import ProtocolError, sha
from .semantic_pairs import unique_object

NAMES = ('memory_ssa_graph', 'memory_ssa_queries')
MODELS = ('nirvana-memory-ssa-graph-v1', 'nirvana-memory-ssa-coverage-v1')
CHECKERS = ('memory_ssa::validate_graph', 'memory_ssa::validate')
GRAPH_FIELDS = {'blocks', 'definitions', 'accesses', 'phi_inputs', 'opaque_effects'}
QUERY_FIELDS = {'queries', 'states', 'links', 'candidate_bytes'}
MAX_BYTES = 16 * 1024 * 1024


def require(condition, message):
    if not condition:
        raise ProtocolError('analysis ' + message)


def counts(value, fields):
    require(isinstance(value, dict) and set(value) == fields
            and all(type(n) is int and 0 <= n <= 8_000_000 for n in value.values()), 'evidence counts')


def members(value):
    require(isinstance(value, list) and len(value) <= 1_000_000, 'artifact member bound')
    return value


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


def validate(entries, directory, original_registers, *, retained=False):
    require(isinstance(entries, list) and len(entries) == 2
            and [e['name'] for e in entries] == list(NAMES), 'check names')
    reports = {}
    for i, entry in enumerate(entries):
        fields = {'name', 'model', 'checker', 'status', 'input_ir', 'memory_ssa', 'evidence', 'reason'}
        require(isinstance(entry, dict)
                and set(entry) - {'input_ir_sha256', 'memory_ssa_sha256'} == fields
                and entry['model'] == MODELS[i] and entry['checker'] == CHECKERS[i], 'check contract')
        require(entry['status'] in ['passed', 'unavailable', 'rejected'], 'check status')
        require(entry['input_ir'] == 'analysis-input.ir.txt'
                and entry['memory_ssa'] in [None, 'memory-ssa.json'], 'artifact names')
        for field in ['input_ir', 'memory_ssa']:
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
                require(re.fullmatch(r'entry=[0-9]+ registers=' + str(original_registers), header) is not None,
                        'original Low IR register binding')
            elif name not in reports:
                reports[name] = report_counts(json.loads(path.read_text(), object_pairs_hook=unique_object))
        if entry['status'] == 'passed':
            require(entry['reason'] is None and entry['memory_ssa'] is not None, 'passed evidence artifacts')
            counts(entry['evidence'], GRAPH_FIELDS if i == 0 else QUERY_FIELDS)
            graph, coverage = reports[entry['memory_ssa']]
            require(entry['evidence'] == (graph if i == 0 else
                    {k: v for k, v in (coverage or {}).items() if k != 'model'}), 'checker evidence correspondence')
            require(i != 1 or entries[0]['status'] == 'passed', 'query check graph prerequisite')
        else:
            require(entry['evidence'] is None and isinstance(entry['reason'], str)
                    and 0 < len(entry['reason']) <= 4096, 'unavailable or rejected reason')
    require(entries[0]['memory_ssa'] == entries[1]['memory_ssa'], 'shared analysis artifact')
    return entries


def summary(rows):
    return {name: dict(Counter(next((e['status'] for e in row.get('stage_checks', {}).get('analysis_checks', [])
                                     if e['name'] == name), 'not_run') for row in rows)) for name in NAMES}
