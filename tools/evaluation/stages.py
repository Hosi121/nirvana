"""Source-entry architecture checks and Low IR coverage, independent of C ABI."""
from .semantics import ProtocolError, sha
from collections import Counter
from . import semantic_pairs, middle_pairs, analysis_checks, load_consumer_pairs

LEGACY_NAMES = ('low_middle', 'middle_predicates', 'selected_semantic')
EXECUTION_NAMES = ('low_middle', 'middle_predicates', 'middle_memory', 'middle_saved', 'selected_semantic')
V9_EXECUTION_NAMES = EXECUTION_NAMES + ('selected_load_consumer',)
COMPARISONS = {name: ['direct_middle', 'lowered'] for name in EXECUTION_NAMES}
COMPARISONS['middle_saved'] = ['direct_middle', 'saved_zero', 'saved_ones']
COMPARISONS['selected_semantic'] = ['lowered_zero', 'lowered_ones']
COMPARISONS['selected_load_consumer'] = ['lowered_zero', 'lowered_ones']
ANALYSIS_SCHEMAS = tuple(analysis_checks.SCHEMA_NAMES)
MEMORY_SCHEMAS = ('nirvana-evaluation-stages-v3',) + ANALYSIS_SCHEMAS


def execution_names(schema):
    return V9_EXECUTION_NAMES if schema == 'nirvana-evaluation-stages-v9' else EXECUTION_NAMES


def execution_names_for_rows(rows):
    return max((execution_names(row.get('stage_checks', {}).get('schema')) for row in rows),
               key=len, default=EXECUTION_NAMES)


def execution_summary(rows, names=None):
    names = execution_names_for_rows(rows) if names is None else names
    return {name: dict(Counter(next((e['status'] for e in row.get('stage_checks', {}).get('execution', [])
                                     if e['name'] == name), 'not_run') for row in rows))
            for name in names}


def validate(value, step_limit, directory, requested_cases, original_registers=None, *, retained=False):
    def require(condition, message):
        if not condition:
            raise ProtocolError(message)
    versions = [('nirvana-evaluation-stages-v1', 'nirvana-entry-full-state-v1'),
                ('nirvana-evaluation-stages-v2', 'nirvana-stage-input-state-v2'),
                ('nirvana-evaluation-stages-v3', 'nirvana-stage-input-state-v3'),
                ('nirvana-evaluation-stages-v4', 'nirvana-stage-input-state-v4'),
                ('nirvana-evaluation-stages-v5', 'nirvana-stage-input-state-v5'),
                ('nirvana-evaluation-stages-v6', 'nirvana-stage-input-state-v6'),
                ('nirvana-evaluation-stages-v7', 'nirvana-stage-input-state-v7'),
                ('nirvana-evaluation-stages-v8', 'nirvana-stage-input-state-v8'),
                ('nirvana-evaluation-stages-v9', 'nirvana-stage-input-state-v9')]
    require(isinstance(value, dict)
            and (value.get('schema'), value.get('contract')) in versions, 'stage check schema or contract')
    extended = value['schema'] != versions[0][0]
    memory_stages = value['schema'] in [v[0] for v in versions[2:]]
    analysis = value['schema'] in [v[0] for v in versions[3:]]
    require(analysis or 'analysis_checks' not in value, 'analysis checks require stage v4 or later')
    if extended:
        require(type(original_registers) is int and 0 <= original_registers <= 4096
                and type(value['original_registers']) is int
                and value['original_registers'] == original_registers, 'stage original register binding')
    budgets = value['prefix_budgets']
    require(isinstance(budgets, list) and bool(budgets) and all(type(n) is int and 0 <= n <= step_limit for n in budgets)
            and budgets == sorted(set(budgets)) and budgets[0] == 0 and budgets[-1] == step_limit,
            'stage prefix budgets')
    execution = value['execution']
    names = list(execution_names(value['schema']) if memory_stages else LEGACY_NAMES if extended else LEGACY_NAMES[:2])
    require([entry['name'] for entry in execution] == names, 'stage execution names')
    statuses = []
    for entry in execution:
        status = entry['status']
        comparisons = COMPARISONS[entry['name']] if memory_stages else ['direct', 'lowered']
        if memory_stages:
            require(entry['comparisons'] == comparisons, 'stage comparison variants')
        count = requested_cases * len(budgets) * len(comparisons)
        require(status in ['passed', 'not_applied', 'unavailable', 'budget_exhausted', 'rejected', 'counterexample'], 'stage status')
        require(type(entry['observations']) is int and entry['observations'] >= 0
                and entry['observations'] <= count
                and (status != 'passed' or entry['observations'] == count)
                and (status != 'not_applied' or entry['observations'] == 0), 'stage observation count')
        require(entry['name'] != 'low_middle' or status != 'not_applied', 'missing base Middle IR check')
        if entry['name'] == 'selected_load_consumer':
            require((status not in ['passed', 'counterexample'] or entry['transition'] is not None)
                    and (status != 'not_applied' or entry['transition'] is None),
                    'load-consumer transition evidence')
            if entry['transition'] is not None:
                load_consumer_pairs.validate(entry, budgets, requested_cases, directory,
                                             original_registers, retained=retained)
        if entry['name'] in ['middle_memory', 'middle_saved']:
            evidence = entry['transition']
            require((status not in ['passed', 'counterexample'] or evidence is not None)
                    and (status != 'not_applied' or evidence is None), 'MIR transition evidence')
            if evidence is not None:
                fields = {'model', 'source_registers', 'lowered_registers', 'input_ir', 'lowered_ir',
                          'middle_ir', 'facts', 'state_pairs'}
                require(isinstance(evidence, dict)
                        and set(evidence) - {'input_ir_sha256', 'lowered_ir_sha256', 'middle_ir_sha256'} == fields
                        and evidence['model'] == 'middle-memory-transition-v1', 'MIR transition model')
                require(type(evidence['source_registers']) is int and evidence['source_registers'] == original_registers
                        and type(evidence['lowered_registers']) is int
                        and original_registers <= evidence['lowered_registers'] <= 1_000_000,
                        'MIR transition register projection')
                facts = evidence['facts']
                if entry['name'] == 'middle_memory':
                    require(isinstance(facts, dict) and set(facts) == {'loads', 'proved_loads', 'refined_loads', 'analysis_complete'}
                            and all(type(facts[k]) is int and 0 <= facts[k] <= 2**32 - 1
                                    for k in ['loads', 'proved_loads', 'refined_loads'])
                            and 0 < facts['refined_loads'] <= facts['proved_loads'] <= facts['loads']
                            and type(facts['analysis_complete']) is bool
                            and evidence['lowered_registers'] == original_registers, 'MIR memory facts')
                else:
                    require(isinstance(facts, dict) and set(facts) == {'annotated_reads', 'phi_values', 'merged_snapshots',
                                'proved_loads', 'snapshot_values', 'replaced_reads'}
                            and all(type(n) is int and 0 <= n <= 2**32 - 1 for n in facts.values())
                            and min(facts['annotated_reads'], facts['proved_loads'], facts['replaced_reads']) > 0,
                            'MIR saved-value facts')
                for field, suffix in [('input_ir', 'input.ir.txt'), ('lowered_ir', 'lowered.ir.txt'), ('middle_ir', 'mir.txt')]:
                    require(evidence[field] == entry['name'] + '.' + suffix, 'MIR transition artifact name')
                    digest = sha(directory / evidence[field])
                    require(evidence.get(field + '_sha256', digest) == digest, 'MIR transition artifact hash')
                    evidence[field + '_sha256'] = digest
                evidence['state_pairs'] = middle_pairs.validate(evidence['state_pairs'], entry, evidence,
                    budgets, requested_cases, directory, original_registers, retained=retained)
        if entry['name'] == 'selected_semantic':
            evidence = entry['semantic']
            require((status not in ['passed', 'counterexample'] or evidence is not None)
                    and (status != 'not_applied' or evidence is None), 'Semantic IR execution evidence')
            if evidence is not None:
                fields = {'model', 'source_registers', 'lowered_registers', 'fresh_initializers',
                          'inputs', 'divisions', 'remainders', 'replaced_subtrees', 'input_ir', 'lowered_ir'}
                require(isinstance(evidence, dict)
                        and set(evidence) - {'input_ir_sha256', 'lowered_ir_sha256', 'state_pairs'} == fields
                        and evidence['model'] == 'selected-semantic-input-state-v1', 'Semantic IR model')
                counts = [evidence[k] for k in ['inputs', 'divisions', 'remainders', 'replaced_subtrees']]
                require(all(type(n) is int and 0 <= n <= 4096 for n in counts)
                        and min(counts[0], counts[1] + counts[2], counts[3]) > 0
                        and sum(counts[:3]) <= 4096, 'Semantic IR capture counts')
                require(type(evidence['source_registers']) is int
                        and original_registers <= evidence['source_registers'] <= 4096
                        and type(evidence['lowered_registers']) is int
                        and evidence['lowered_registers'] == evidence['source_registers'] + sum(counts[:3]),
                        'Semantic IR register projection')
                initializers = evidence['fresh_initializers']
                require(isinstance(initializers, list) and all(type(n) is int for n in initializers)
                        and initializers == [0, 2**64 - 1], 'Semantic IR private initializers')
                for field, filename in [('input_ir', 'selected-semantic-input.ir.txt'),
                                        ('lowered_ir', 'selected-semantic-lowered.ir.txt')]:
                    require(evidence[field] == filename, 'Semantic IR artifact name')
                    digest = sha(directory / filename)
                    require(evidence.get(field + '_sha256', digest) == digest, 'Semantic IR artifact hash')
                    evidence[field + '_sha256'] = digest
                if 'state_pairs' in evidence:
                    evidence['state_pairs'] = semantic_pairs.validate(evidence['state_pairs'], entry, evidence,
                        budgets, requested_cases, directory, original_registers, retained=retained)
        witness = entry['witness']
        if witness is not None:
            require(isinstance(witness, str) and witness == entry['name'] + '.witness.txt', 'stage witness name')
            digest = sha(directory / witness)
            require(entry.get('witness_sha256', digest) == digest, 'stage witness hash')
            entry['witness_sha256'] = digest
        require(status != 'counterexample' or witness is not None, 'missing stage counterexample')
        statuses.append(status)
    if analysis:
        analysis_checks.validate(value['analysis_checks'], directory, original_registers, retained=retained,
                                 version=next(index + 1 for index, pair in enumerate(versions)
                                              if value['schema'] == pair[0]))
        statuses.extend(e['status'] for e in value['analysis_checks'])
    expected = ('counterexample' if 'counterexample' in statuses else 'rejected' if 'rejected' in statuses
                else 'inconclusive' if any(s in statuses for s in ['unavailable', 'budget_exhausted']) else 'passed')
    require(value['status'] == expected, 'stage aggregate status')
    coverage = value['low_coverage']
    fields = ['steps_started', 'syntactic_steps', 'transfers_observed', 'syntactic_transfers']
    require(all(type(coverage[k]) is int and coverage[k] >= 0 for k in fields)
            and coverage['steps_started'] <= coverage['syntactic_steps']
            and coverage['transfers_observed'] <= coverage['syntactic_transfers'], 'Low IR coverage counts')
    unseen = coverage['unobserved_transfers']
    require(isinstance(unseen, list) and all(isinstance(e, list) and len(e) == 2
                and all(type(n) is int and 0 <= n < 2**64 for n in e) for e in unseen)
            and len({tuple(e) for e in unseen}) == len(unseen)
            and len(unseen) == coverage['syntactic_transfers'] - coverage['transfers_observed'],
            'Low IR transfer coverage denominator')
    c = value['selected_c']
    require(all(type(c[k]) is bool for k in ['input_structure_checked', 'display_structure_checked', 'fallback_goto'])
            and type(c['saved_value_rounds']) is int and c['saved_value_rounds'] >= 0, 'selected C checks')
    if 'parameter_registers' in c:
        parameters = c['parameter_registers']
        require(isinstance(parameters, list) and len(parameters) <= 1024
                and all(type(n) is int and 0 <= n < 2**32 for n in parameters)
                and len(parameters) == len(set(parameters)), 'selected C parameter registers')
    if value['schema'] == 'nirvana-evaluation-stages-v9':
        transition = execution[-1]['transition']
        require('parameter_registers' in c and (transition is None
                or transition['parameters'] == c['parameter_registers']),
                'load-consumer selected parameter binding')
    if c['predicates'] is not None:
        require(isinstance(c['predicates'], dict)
                and set(c['predicates']) == {'pruned_branches', 'constant_assignments', 'blocks_before', 'blocks_after'}
                and all(type(n) is int and n >= 0 for n in c['predicates'].values()), 'predicate evidence counts')
    continuation = c.get('continuations')
    if continuation is not None:
        version = continuation.get('model') if isinstance(continuation, dict) else None
        fields = {'model', 'removed_conditions', 'compared_graph_nodes'}
        if version in ['c-fragment-continuation-v2', 'c-fragment-continuation-v3', 'c-fragment-continuation-v4']:
            fields.add('shared_fragments')
        if version == 'c-fragment-continuation-v3':
            fields.add('store_order')
        if version == 'c-fragment-continuation-v4':
            fields.add('effect_order')
        require(isinstance(continuation, dict)
                and set(continuation) == fields
                and version in ['c-fragment-continuation-v1', 'c-fragment-continuation-v2', 'c-fragment-continuation-v3', 'c-fragment-continuation-v4']
                and type(continuation['removed_conditions']) is int
                and 0 <= continuation['removed_conditions'] <= 4096
                and type(continuation['compared_graph_nodes']) is int
                and 0 < continuation['compared_graph_nodes'] <= 16384
                and not c['fallback_goto'], 'C continuation evidence')
        shared = continuation.get('shared_fragments', 0)
        require(type(shared) is int and 0 <= shared <= 4096
                and (shared > 0 or continuation['removed_conditions'] > 0), 'C continuation progress')
        if version == 'c-fragment-continuation-v3':
            order = continuation['store_order']
            require(isinstance(order, dict) and set(order) == {'prefix_nodes', 'range_witnesses', 'swapped_pairs'}
                    and all(type(n) is int and 0 < n <= 4096 for n in order.values()), 'C store-order evidence')
        if version == 'c-fragment-continuation-v4':
            order = continuation['effect_order']
            require(isinstance(order, dict)
                    and set(order) == {'prefix_nodes', 'range_witnesses', 'store_pairs', 'local_pairs'}
                    and all(type(n) is int and 0 <= n <= 4096 for n in order.values())
                    and min(order['prefix_nodes'], order['range_witnesses'], order['local_pairs']) > 0
                    and order['store_pairs'] + order['local_pairs'] <= 4096, 'C effect-order evidence')
    return value


def attach(value, row, directory, step_limit, requested_cases, original_registers=None):
    if value is None:
        row['stage_checks'] = {'status': 'not_run'}
        return
    try:
        row['stage_checks'] = validate(value, step_limit, directory, requested_cases, original_registers)
    except (ProtocolError, OSError, KeyError, TypeError, IndexError, ValueError) as error:
        row['stage_checks'] = {'status': 'evaluator_error', 'reason': str(error)}
    status = row['stage_checks']['status']
    row.setdefault('stages', {})['architecture'] = status
    if status in ['counterexample', 'rejected', 'evaluator_error']:
        row['status'] = status
        row.setdefault('failures', []).append({'stage': 'architecture', 'status': status,
                                               'error': 'see retained stage_checks and witnesses'})
