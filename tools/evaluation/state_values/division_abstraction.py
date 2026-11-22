"""A sound overapproximation of constant division, not a quotient heuristic.

Each width has an arbitrary quotient function. Signed denominators use their
unsigned magnitude and a separate result sign; remainder is n-q*d. Actual
total division supplies one interpretation, so abstract UNSAT proves the exact
query. Abstract SAT may be spurious and always falls back to exact arithmetic.
"""

MODEL='constant-division-congruence-v1'


def operation(graph,node):
    if node.op not in ['/','%','total_sdiv']: return None
    a,b=node.args;divisor=graph.constant(b)
    if divisor is None: return None
    bits=node.type.bits
    signed=node.op=='total_sdiv' or graph.type(a).signed
    negative=signed and bool(divisor >> (bits-1))
    magnitude=(-divisor if negative else divisor) % (1 << bits)
    name=f'quotient_{"signed_magnitude" if signed else "unsigned"}_{bits}'
    return name,bits,magnitude,negative


def declarations(graph):
    operations=(operation(graph,n) for n in graph.nodes)
    functions={info[:2] for info in operations if info is not None}
    return ''.join(f'(declare-fun {name} ((_ BitVec {bits}) (_ BitVec {bits})) (_ BitVec {bits}))\n'
                   for name,bits in sorted(functions))


def term(graph,node):
    info=operation(graph,node)
    if info is None: return None
    name,bits,magnitude,negative=info;a,_=node.args
    divisor=f'(_ bv{magnitude} {bits})';quotient=f'({name} v{a} {divisor})'
    if node.op=='%': return f'(bvsub v{a} (bvmul {quotient} {divisor}))'
    return f'(bvneg {quotient})' if negative else quotient
