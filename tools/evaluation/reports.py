"""Replay retained M0 witnesses and compare identical input/observation contracts.

Search intervals are reported solver results. Replay checks the feasible mapping
cost, artifact hashes and concrete observer outputs; it does not certify that a
search exhausted all mappings or prove the generated C for unobserved inputs.
"""
from collections import Counter
import json
from pathlib import Path

from . import control_graph as cg, semantics, stages


class Incompatible(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Incompatible(message)


def artifact(root, relative):
    path = (root / relative).resolve()
    require(path.is_relative_to(root.resolve()), 'artifact outside report directory')
    return path


def hashed(path, expected):
    require(isinstance(expected, str) and semantics.sha(path) == expected,
            f'artifact hash mismatch: {path.name}')
    return path


def index(report):
    require(report['schema'] == 'nirvana-structure-report-v1', 'report schema')
    require(report['metric'] == cg.METRIC, 'metric version')
    rows = report['rows']
    result = {row['id']: row for row in rows}
    require(len(result) == len(rows) == report['requested_profiles'] == report['summary']['requested'],
            'duplicate, missing or incomplete profile denominator')
    require(bool(rows), 'empty report')
    require(dict(Counter(row['cohort'] for row in rows)) == report['summary']['cohorts'],
            'cohort denominator')
    return result


def replay(root, row):
    """Verify artifacts that are present; failures remain named report rows."""
    directory = artifact(root, row['artifacts'])
    for field, name in [('preprocessed_sha256', 'source.i'), ('object_sha256', 'input.o'),
                        ('readable_sha256', 'readable.c')]:
        if field in row:
            hashed(directory / name, row[field])
    result = {'structure': row['structure_status'], 'semantics': row['semantics']['status']}
    require((row['structure_status'] == 'measured') == ('distance' in row),
            'missing or unexpected measured distance')
    if 'distance' in row:
        graphs = []
        for stage in ['source_cfg', 'generated_cfg']:
            saved = row[stage]
            path = hashed(directory / f'{stage}.json', saved['graph_sha256'])
            dump = hashed(directory / f'{stage}.stderr.txt', saved['dump_sha256'])
            graph = cg.graph_from_json(json.loads(path.read_text())['graph'])
            raw, stats = cg.parse_dump(dump.read_text(), row['function'] if stage == 'source_cfg' else 'nirvana_readable')
            restored, removed = cg.normalize(raw)
            require(graph == restored and all(saved[k] == v for k, v in {**stats, **removed}.items()),
                    'normalized graph differs from retained compiler dump')
            require(len(graph['nodes']) == saved['nodes'] and len(graph['edges']) == saved['edges'],
                    'graph size summary')
            graphs.append(graph)
        distance = row['distance']
        lo, hi = distance['lower_bound'], distance['upper_bound']
        require(distance['metric'] == cg.METRIC and distance['status'] in ['exact', 'upper_bound'],
                'distance metric or status')
        require(type(lo) is int and type(hi) is int and 0 <= lo <= hi, 'distance interval')
        require(distance['status'] != 'exact' or lo == hi, 'exact distance interval')
        pairs = distance['mapping']
        require(len(dict(pairs)) == len(pairs), 'duplicate mapping source')
        require(cg.mapping_cost(*graphs, dict(pairs)) == hi, 'mapping witness cost')
        result['mapping_cost'] = hi
    semantic = row['semantics']
    architecture = row.get('stage_checks', {'status': 'not_run'})
    if 'schema' in architecture:
        stages.validate(architecture, semantic['profile']['step_limit'], directory / 'semantics',
                        semantic['profile']['requested_cases'])
    result['architecture'] = architecture['status']
    if 'profile' in semantic:
        require(semantic['contract'] == semantics.CONTRACT, 'semantic contract')
        profile = semantic['profile']
        destination = directory / 'semantics'
        for name in semantics.FILES:
            hashed(destination / name, semantic['inputs'][name])
        observed = {}
        for label, prefix, width in [('native', 'native', 5), ('generated_O0', 'generated', 69),
                                     ('generated_O2', 'generated', 69)]:
            if label not in semantic['checks']:
                require(semantic['status'] != 'passed', 'missing passed semantic check')
                continue
            recorded = semantic['checks'][label]
            actual = (directory / f'{label}_run.stdout.txt').read_text()
            check = semantics.compare((destination / f'{prefix}-expected.txt').read_text(),
                                      actual, (destination / f'{prefix}-inputs.txt').read_text(), width)
            require(check == recorded, f'{label} observer replay differs')
            require(check['cases'] == profile['native_cases' if label == 'native' else 'checked_cases'],
                    'semantic observation denominator')
            observed[label] = check['status']
        if semantic['status'] == 'passed':
            require(len(observed) == 3 and all(v == 'passed' for v in observed.values())
                    and profile['suspended'] == 0 and profile['native_cases'] == profile['vectors'],
                    'incomplete passed semantic profile')
        result['checks'] = observed
    else:
        require(semantic['status'] not in ['passed', 'counterexample', 'inconclusive'],
                'missing semantic observation profile')
    return result


def interval_change(before, after):
    if before is None or after is None:
        return 'unmeasured'
    a, b = before, after
    if a['status'] == b['status'] == 'exact' and a['upper_bound'] == b['upper_bound']:
        return 'equal'
    if b['upper_bound'] < a['lower_bound']:
        return 'improved'
    if b['lower_bound'] > a['upper_bound']:
        return 'regressed'
    return 'overlapping_bounds'


def tool_identity(value):
    if value is None:
        return None
    return {key: value.get(key) for key in ['sha256', 'version', 'returncode']}


def commands(row, root):
    """Compare compiler flags while allowing output-directory relocation."""
    result = {}
    for command in row['commands']:
        stage = command['stage']
        if stage not in ['preprocess', 'input_compile', 'recompile', 'source_cfg', 'generated_cfg',
                         'native_compile', 'generated_O0_compile', 'generated_O2_compile']:
            continue
        require(stage not in result, 'duplicate command stage')
        result[stage] = ['$TOOL', *[str(arg).replace(str(root.resolve()), '$ARTIFACTS')
                                  for arg in command['argv'][1:]]]
    return result


def compare(before_path, after_path):
    before_path, after_path = Path(before_path), Path(after_path)
    before, after = (json.loads(path.read_text()) for path in [before_path, after_path])
    left, right = index(before), index(after)
    require(left.keys() == right.keys(), 'different requested profile IDs')
    for key in ['evaluation', 'budgets', 'emission']:
        require(before[key] == after[key], f'changed {key}')
    require(before['corpus']['sha256'] == after['corpus']['sha256'], 'changed corpus manifest')
    for key in ['clang', 'c_compiler']:
        require(tool_identity(before[key]) == tool_identity(after[key]), f'changed {key} tool')
    require({k: tool_identity(v) for k, v in before['compilers'].items()}
            == {k: tool_identity(v) for k, v in after['compilers'].items()}, 'changed input compiler')
    require(before['semantics']['contract'] == after['semantics']['contract'], 'changed observation contract')
    require((before.get('semantic_inputs') or {}).get('sha256')
            == (after.get('semantic_inputs') or {}).get('sha256'), 'changed semantic input file')
    require((before.get('toolchain_manifest') or {}).get('sha256')
            == (after.get('toolchain_manifest') or {}).get('sha256'), 'changed toolchain manifest')
    rows = []
    for key, a in left.items():
        b = right[key]
        for field in ['family', 'cohort', 'source_sha256', 'function', 'compiler', 'optimization']:
            require(a[field] == b[field], f'{key}: changed {field}')
        # Absence on both sides retains failures in the requested denominator.
        # A new successful stage may provide a hash that the baseline lacks.
        for field in ['preprocessed_sha256', 'object_sha256']:
            if field in a and field in b:
                require(a[field] == b[field], f'{key}: changed {field}')
        ac, bc = commands(a, before_path.parent), commands(b, after_path.parent)
        for stage in ac.keys() & bc.keys():
            require(ac[stage] == bc[stage], f'{key}: changed {stage} flags')
        ar, br = replay(before_path.parent, a), replay(after_path.parent, b)
        sa, sb = a['semantics'], b['semantics']
        if 'profile' in sa and 'profile' in sb:
            require(sa['profile'] == sb['profile'], f'{key}: changed semantic profile')
            for name in ['native-inputs.txt', 'native-expected.txt',
                         'generated-inputs.txt', 'generated-expected.txt']:
                require(sa['inputs'][name] == sb['inputs'][name], f'{key}: changed {name}')
        if 'source_cfg' in a and 'source_cfg' in b:
            require(a['source_cfg']['graph_sha256'] == b['source_cfg']['graph_sha256'],
                    f'{key}: changed source graph')
        same_graphs = all(a.get(stage, {}).get('graph_sha256') is not None
                          and a[stage]['graph_sha256'] == b.get(stage, {}).get('graph_sha256')
                          for stage in ['source_cfg', 'generated_cfg'])
        rows.append({'id': key, 'cohort': a['cohort'],
                     'distance': 'equal' if same_graphs else interval_change(a.get('distance'), b.get('distance')),
                     'distance_basis': 'identical_graphs' if same_graphs else 'recorded_search_intervals',
                     'before_interval': [a['distance']['lower_bound'], a['distance']['upper_bound']]
                        if 'distance' in a else None,
                     'after_interval': [b['distance']['lower_bound'], b['distance']['upper_bound']]
                        if 'distance' in b else None,
                     'before_semantics': sa['status'], 'after_semantics': sb['status'],
                     'structure_regression': a['structure_status'] == 'measured' and b['structure_status'] != 'measured',
                     'architecture_regression': ar['architecture'] == 'passed' and br['architecture'] != 'passed',
                     'semantic_regression': sa['status'] == 'passed' and sb['status'] != 'passed',
                     'before_replay': ar, 'after_replay': br})
    return {'schema': 'nirvana-structure-comparison-v1', 'metric': cg.METRIC,
            'before': {'revision': before['workspace_revision'], 'dirty': before['workspace_dirty'],
                       'decompiler_sha256': before['decompiler']['sha256'],
                       'report_sha256': semantics.sha(before_path)},
            'after': {'revision': after['workspace_revision'], 'dirty': after['workspace_dirty'],
                      'decompiler_sha256': after['decompiler']['sha256'],
                      'report_sha256': semantics.sha(after_path)},
            'requested': len(rows),
            'structure': dict(Counter(row['distance'] for row in rows)),
            'structure_regressions': sum(row['structure_regression'] for row in rows),
            'candidate_semantics': dict(Counter(row['after_semantics'] for row in rows)),
            'architecture_regressions': sum(row['architecture_regression'] for row in rows),
            'candidate_architecture': dict(Counter(row['after_replay']['architecture'] for row in rows)),
            'semantic_regressions': sum(row['semantic_regression'] for row in rows),
            'resources': 'See per-command samples; timing comparisons need controlled repeated runs.',
            'rows': rows}


def reanalyze(path, *, max_states=None, seconds=None):
    """Refine saved graph distances after replay, preserving original run costs.

    The result belongs beside the original report, where its retained artifact
    paths resolve. Caller writes to a new filename; no native/C rerun is claimed.
    """
    path = Path(path)
    report = json.loads(path.read_text())
    index(report)
    original_evaluation = dict(report['evaluation'])
    budgets = report['budgets']
    max_states = budgets['search_states'] if max_states is None else max_states
    seconds = budgets['search_seconds'] if seconds is None else seconds
    require(type(max_states) is int and max_states >= 1 and 0 < seconds < float('inf'),
            'positive finite graph search budgets required')
    for row in report['rows']:
        replay(path.parent, row)
        if 'distance' not in row:
            continue
        directory = artifact(path.parent, row['artifacts'])
        graphs = [cg.graph_from_json(json.loads((directory / f'{stage}.json').read_text())['graph'])
                  for stage in ['source_cfg', 'generated_cfg']]
        row['distance'] = cg.distance(*graphs, max_states=max_states, seconds=seconds)
    budgets.update(search_states=max_states, search_seconds=seconds)
    report['evaluation']['metric_sha256'] = semantics.sha(cg.__file__)
    report['summary']['distances'] = dict(Counter(row['distance']['status'] for row in report['rows'] if 'distance' in row))
    report['reanalysis'] = {'source_report': path.name, 'source_report_sha256': semantics.sha(path),
                            'original_evaluation': original_evaluation,
                            'replay_sha256': semantics.sha(__file__),
                            'resources': 'Original command samples retained; only graph search was rerun.'}
    return report
