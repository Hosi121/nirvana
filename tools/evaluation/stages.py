"""Source-entry architecture checks and Low IR coverage, independent of C ABI."""
from .semantics import ProtocolError, sha


def validate(value, step_limit, directory, requested_cases):
    def require(condition, message):
        if not condition:
            raise ProtocolError(message)
    require(isinstance(value, dict) and value.get('schema') == 'nirvana-evaluation-stages-v1'
            and value.get('contract') == 'nirvana-entry-full-state-v1', 'stage check schema or contract')
    budgets = value['prefix_budgets']
    require(isinstance(budgets, list) and bool(budgets) and all(type(n) is int and 0 <= n <= step_limit for n in budgets)
            and budgets == sorted(set(budgets)) and budgets[0] == 0 and budgets[-1] == step_limit,
            'stage prefix budgets')
    execution = value['execution']
    require([entry['name'] for entry in execution] == ['low_middle', 'middle_predicates'], 'stage execution names')
    statuses = []
    for entry in execution:
        status = entry['status']
        require(status in ['passed', 'not_applied', 'unavailable', 'budget_exhausted', 'rejected', 'counterexample'], 'stage status')
        require(type(entry['observations']) is int and entry['observations'] >= 0
                and entry['observations'] <= requested_cases * len(budgets) * 2
                and (status != 'passed' or entry['observations'] == requested_cases * len(budgets) * 2)
                and (status != 'not_applied' or entry['observations'] == 0), 'stage observation count')
        require(entry['name'] != 'low_middle' or status != 'not_applied', 'missing base Middle IR check')
        witness = entry['witness']
        if witness is not None:
            require(isinstance(witness, str) and witness == entry['name'] + '.witness.txt', 'stage witness name')
            digest = sha(directory / witness)
            require(entry.get('witness_sha256', digest) == digest, 'stage witness hash')
            entry['witness_sha256'] = digest
        require(status != 'counterexample' or witness is not None, 'missing stage counterexample')
        statuses.append(status)
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
    if c['predicates'] is not None:
        require(isinstance(c['predicates'], dict)
                and set(c['predicates']) == {'pruned_branches', 'constant_assignments', 'blocks_before', 'blocks_after'}
                and all(type(n) is int and n >= 0 for n in c['predicates'].values()), 'predicate evidence counts')
    continuation = c.get('continuations')
    if continuation is not None:
        version = continuation.get('model') if isinstance(continuation, dict) else None
        fields = {'model', 'removed_conditions', 'compared_graph_nodes'}
        if version in ['c-fragment-continuation-v2', 'c-fragment-continuation-v3']:
            fields.add('shared_fragments')
        if version == 'c-fragment-continuation-v3':
            fields.add('store_order')
        require(isinstance(continuation, dict)
                and set(continuation) == fields
                and version in ['c-fragment-continuation-v1', 'c-fragment-continuation-v2', 'c-fragment-continuation-v3']
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
    return value


def attach(value, row, directory, step_limit, requested_cases):
    if value is None:
        row['stage_checks'] = {'status': 'not_run'}
        return
    try:
        row['stage_checks'] = validate(value, step_limit, directory, requested_cases)
    except (ProtocolError, OSError, KeyError, TypeError, IndexError, ValueError) as error:
        row['stage_checks'] = {'status': 'evaluator_error', 'reason': str(error)}
    status = row['stage_checks']['status']
    row.setdefault('stages', {})['architecture'] = status
    if status in ['counterexample', 'rejected', 'evaluator_error']:
        row['status'] = status
        row.setdefault('failures', []).append({'stage': 'architecture', 'status': status,
                                               'error': 'see retained stage_checks and witnesses'})
