"""Retained M0 artifacts for report-reader protocol tests."""
import json
from evaluation import control_graph as cg, semantics

DUMP = '''uint64_t fixture(void)
 [B2 (ENTRY)]
   Succs (1): B1
 [B1]
   1: return 7;
   Succs (1): B0
 [B0 (EXIT)]
'''


def save(root, name, text):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    return semantics.sha(path)


def fixture(root):
    row = dict(id='sample-gcc-O2', family='sample', cohort='development', source_sha256='a' * 64,
               function='fixture', compiler='gcc', optimization='O2', artifacts='sample-gcc-O2',
               structure_status='measured', commands=[])
    directory = root / row['artifacts']
    for field, name, text in [('preprocessed_sha256', 'source.i', 'source'),
                              ('object_sha256', 'input.o', 'object'),
                              ('readable_sha256', 'readable.c', 'generated')]:
        row[field] = save(directory, name, text)
    for stage in ['source_cfg', 'generated_cfg']:
        dump = DUMP if stage == 'source_cfg' else DUMP.replace('fixture', 'nirvana_readable')
        raw, stats = cg.parse_dump(dump, 'fixture' if stage == 'source_cfg' else 'nirvana_readable')
        graph, removed = cg.normalize(raw)
        row[stage] = {**stats, **removed, 'nodes': len(graph['nodes']), 'edges': len(graph['edges']),
                      'graph_sha256': save(directory, stage + '.json', json.dumps({'graph': graph})),
                      'dump_sha256': save(directory, stage + '.stderr.txt', dump)}
    row['distance'] = cg.distance(graph, graph)
    profile = dict(vectors=1, native_cases=1, checked_cases=1, suspended=0)
    inputs = {}
    for name in semantics.FILES:
        text = (' '.join(['0'] * (5 if name.startswith('native') else 69)) + '\n'
                if name.endswith('expected.txt') else '1 2 3 4\n' if name.endswith('inputs.txt') else 'harness')
        inputs[name] = save(directory / 'semantics', name, text)
    checks = {}
    for label, prefix, width in [('native', 'native', 5), ('generated_O0', 'generated', 69),
                                 ('generated_O2', 'generated', 69)]:
        save(directory, label + '_run.stdout.txt', ' '.join(['0'] * width) + '\n')
        checks[label] = dict(status='passed', cases=1)
    row['semantics'] = dict(status='passed', contract=semantics.CONTRACT, profile=profile,
                             inputs=inputs, checks=checks)
    row['commands'] = [dict(stage='input_compile', argv=['cc', '-O2', str(directory / 'source.i'),
                                                       '-o', str(directory / 'input.o')])]
    tool = dict(sha256='b' * 64, version='compiler-v1', returncode=0)
    report = dict(schema='nirvana-structure-report-v1', metric=cg.METRIC,
                  requested_profiles=1, summary=dict(requested=1, cohorts=dict(development=1)),
                  evaluation=dict(metric_sha256='c' * 64), budgets=dict(search_states=100, search_seconds=1), emission='readable-c',
                  corpus=dict(sha256='d' * 64), clang=tool, c_compiler=tool, compilers=dict(gcc=tool),
                  semantics=dict(contract=semantics.CONTRACT), workspace_revision='revision',
                  workspace_dirty=False, decompiler=dict(sha256='e' * 64), rows=[row])
    return report



def architecture(requested_cases=24, budgets=None):
    budgets = [0, 4096] if budgets is None else budgets
    observations = requested_cases * len(budgets) * 2
    return dict(schema='nirvana-evaluation-stages-v1', contract='nirvana-entry-full-state-v1',
                status='passed', prefix_budgets=budgets,
                execution=[dict(name='low_middle', status='passed', observations=observations, witness=None),
                           dict(name='middle_predicates', status='not_applied', observations=0, witness=None)],
                selected_c=dict(predicates=None, input_structure_checked=True, display_structure_checked=True,
                                saved_value_rounds=0, fallback_goto=False),
                low_coverage=dict(steps_started=2, syntactic_steps=3, transfers_observed=1,
                                  syntactic_transfers=2, unobserved_transfers=[[1, 2]]))


def semantic_architecture(requested_cases=24, budgets=None):
    value = architecture(requested_cases, budgets)
    value.update(schema='nirvana-evaluation-stages-v2', contract='nirvana-stage-input-state-v2',
                 original_registers=32)
    value['execution'].append(dict(name='selected_semantic', status='passed', observations=requested_cases * len(value['prefix_budgets']) * 2, witness=None,
        semantic=dict(model='selected-semantic-input-state-v1', source_registers=32,
                      lowered_registers=35, fresh_initializers=[0, 2**64 - 1],
                      inputs=1, divisions=1, remainders=1, replaced_subtrees=4,
                      input_ir='selected-semantic-input.ir.txt', lowered_ir='selected-semantic-lowered.ir.txt')))
    return value


def retain_semantic_ir(directory, value):
    for entry in value['execution']:
        evidence = entry.get('semantic')
        if evidence:
            for field in ['input_ir', 'lowered_ir']:
                save(directory, evidence[field], 'retained ' + field + '\n')


