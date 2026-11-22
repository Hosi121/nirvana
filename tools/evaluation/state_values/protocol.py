"""Bind optional state-value observations to AST, ABI and solver artifacts.

Replay rebuilds typed graphs and the exact query, and replays SAT values. It
uses the recorded solver verdict, rather than checking a proof certificate.
"""
import json
from pathlib import Path

from ..semantics import sha
from . import MODEL, MEMORY_PROFILE, measure, Unsupported

NAMES = {'graph': 'state-values.graph.json', 'query': 'state-values.smt2', 'solver': 'state-values.solver.json'}
STATUSES = {'equivalent_under_model', 'counterexample_under_model', 'unknown', 'unsupported', 'unavailable', 'evaluator_error', 'not_run'}


def implementation():
    return {p.name: sha(p) for p in sorted(Path(__file__).parent.glob('*.py'))}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def arguments(directory, row):
    return ((directory / 'source_ast.stdout.txt').read_text(), (directory / 'generated_ast.stdout.txt').read_text(),
            row['function'], row['stage_checks']['selected_c']['parameter_registers'])


def fixed_layout(row):
    profile = row.get('semantics', {}).get('profile', {})
    return all(type(profile.get(k)) is int and profile[k] == v for k,v in MEMORY_PROFILE.items())


def attach(args, row, directory):
    row['state_values'] = {'status': 'not_run'}
    if not args.state_values: return
    if (row['c_footprint']['status'] != 'measured' or 'prepare_stdout_sha256' not in row['semantics']
            or 'parameter_registers' not in row.get('stage_checks', {}).get('selected_c', {})):
        row['state_values'] = {'model': MODEL, 'status': 'unavailable', 'reason': 'requires measured C AST and bound ABI metadata'}
    elif not fixed_layout(row):
        row['state_values'] = {'model': MODEL, 'status': 'unavailable', 'reason': 'requires fixed state[4] entry memory layout'}
    else:
        try:
            result = measure(*arguments(directory, row), args.value_solver, args.value_seconds)
            contents = {'graph': json.dumps(result.graph, indent=2) + '\n', 'query': result.query + '(check-sat)\n',
                        'solver': json.dumps(result.solver_outputs, indent=2) + '\n'}
            artifacts = {}
            for key, text in contents.items():
                path = directory / NAMES[key]; path.write_text(text)
                artifacts[key] = {'file': NAMES[key], 'sha256': sha(path)}
            row['state_values'] = {**result.report, 'artifacts': artifacts}
        except Unsupported as error:
            row['state_values'] = {'model': MODEL, 'status': 'unsupported', 'reason': str(error)}
        except Exception as error:
            row['state_values'] = {'model': MODEL, 'status': 'evaluator_error', 'reason': str(error)}
    row.setdefault('stages', {})['state_values'] = row['state_values']['status']


def replay(directory, row):
    value = row.get('state_values', {'status': 'not_run'})
    if not isinstance(value, dict) or value.get('status') not in STATUSES:
        raise ValueError('state value status')
    status = value['status']
    if status in ['not_run', 'unavailable', 'evaluator_error']: return status
    if (row.get('c_footprint', {}).get('status') != 'measured'
            or 'prepare_stdout_sha256' not in row.get('semantics', {})
            or 'parameter_registers' not in row.get('stage_checks', {}).get('selected_c', {})):
        raise ValueError('state values require retained AST and bound ABI metadata')
    if not fixed_layout(row): raise ValueError('state value entry memory layout')
    if value.get('model') != MODEL: raise ValueError('state value model')
    if status == 'unsupported':
        try: measure(*arguments(directory, row), None, 2, recorded=[], failure_reason='solver_unavailable')
        except Unsupported as error:
            if canonical(value) != canonical({'model': MODEL, 'status': 'unsupported', 'reason': str(error)}):
                raise ValueError('state value unsupported reason') from error
            return status
        raise ValueError('unexpected loss of supported value model')
    artifacts = value['artifacts']
    if set(artifacts) != set(NAMES): raise ValueError('state value artifact denominator')
    texts = {}
    for key, expected in NAMES.items():
        record = artifacts[key]
        if set(record) != {'file', 'sha256'} or record['file'] != expected or sha(directory / expected) != record['sha256']:
            raise ValueError('state value artifact hash or name')
        texts[key] = (directory / expected).read_text()
    result = measure(*arguments(directory, row), None, value['solver_seconds'],
                     recorded=json.loads(texts['solver']), failure_reason=value.get('reason'))
    if (result.query + '(check-sat)\n' != texts['query'] or canonical(result.graph) != canonical(json.loads(texts['graph']))
            or canonical({**result.report, 'artifacts': artifacts}) != canonical(value)):
        raise ValueError('state value graph, query or verdict differs from retained inputs')
    return status
