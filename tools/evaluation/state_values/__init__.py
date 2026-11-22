"""State[4] value correspondence for bounded C models, independent of lifting."""
from dataclasses import asdict, dataclass
from .. import state_memory as sm
from .. import c_footprint as cf
from .ast import observe
from .terms import Graph, Unsupported
from .solver import compare

MODEL = 'nirvana-state4-values-v1'


@dataclass
class Evaluation:
    report: dict
    query: str
    solver_outputs: list
    graph: dict


def measure(source_text, generated_text, name, parameters, solver, seconds=2):
    try: memory = sm.measure(source_text, generated_text, name, parameters)
    except cf.Unsupported as error: raise Unsupported('state ABI: ' + str(error)) from error
    graph = Graph()
    a = observe(graph, source_text, name)
    b = observe(graph, generated_text, 'nirvana_readable', parameters.index(sm.STATE_REGISTER), False)
    proof = compare(graph, a, b, solver, seconds)
    def summary(model):
        return {'syntactic_paths': model.paths, 'expanded_assignments': model.expanded_assignments,
                'scalar_declarations': model.scalar_declarations, **graph.summary(model.outputs)}
    report = {'model': MODEL, 'status': proof.status,
              'profile': {**memory['profile'], 'integer_abi': 'x86-64-lp64', 'pointer': 'valid-state-only',
                          'control': 'closed-if-return', 'observations': ['return', 'state_bytes']},
              'source': summary(a), 'generated': summary(b), 'reason': proof.reason, 'witness': proof.witness}
    raw = {'schema': 'nirvana-state4-value-graph-v1', 'nodes': [asdict(n) for n in graph.nodes],
           'source_outputs': a.outputs, 'generated_outputs': b.outputs}
    return Evaluation(report, proof.query, proof.responses, raw)
