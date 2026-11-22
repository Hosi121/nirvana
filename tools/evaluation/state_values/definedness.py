"""Check C signed-operation premises independently of interval proposals.

The SMT predicates and concrete replay use mathematical ranges and widened
arithmetic, without interval assumptions. All modeled values are checked, which
is conservative for expressions built under a path guard.
"""
from .intervals import domain, number


def predicates(graph):
    result=[]
    for i,n in enumerate(graph.nodes):
        if not n.type.signed: continue
        args=[f'v{a}' for a in n.args];bits=n.type.bits;term=None
        literal=lambda value,width=bits:f'(_ bv{value%2**width} {width})'
        extend=lambda value,by:f'((_ sign_extend {by}) {value})'
        if n.op=='cast':
            before=graph.type(n.args[0]);width=max(bits,before.bits)+1
            value=f'((_ {"sign_extend" if before.signed else "zero_extend"} {width-before.bits}) {args[0]})'
            lo,hi=domain(n.type)
            term=f'(and (bvsle {literal(lo,width)} {value}) (bvsle {value} {literal(hi,width)}))'
        elif n.op in ['+','-','*']:
            extra=bits if n.op=='*' else 1
            operands=' '.join(extend(a,extra) for a in args)
            operator={'+' : 'bvadd','-':'bvneg' if len(args)==1 else 'bvsub','*':'bvmul'}[n.op]
            term=f'(= ({operator} {operands}) {extend(f"v{i}",extra)})'
        elif n.op in ['/','%']:
            term=f'(not (and (= {args[0]} {literal(-(1 << (bits-1)))}) (= {args[1]} {literal(-1)})))'
        elif n.op in ['<<','>>']:
            term=f'(bvsge {args[0]} {literal(0)})'
            if n.op=='<<':
                count=graph.constant(n.args[1])
                wide=f'(bvshl ((_ zero_extend {bits}) {args[0]}) {literal(count,bits*2)})'
                term=f'(and {term} (bvsge v{i} {literal(0)}) (= {wide} ((_ zero_extend {bits}) v{i})))'
        if term is not None: result.append((i,term))
    return result


def violations(graph,values):
    bad=[]
    for i,n in enumerate(graph.nodes):
        if not n.type.signed or not n.args: continue
        args=[number(values[a],graph.type(a)) for a in n.args]
        lo,hi=domain(n.type);invalid=False
        if n.op=='cast': invalid=not lo<=args[0]<=hi
        elif n.op in ['+','-','*']:
            value=(-args[0] if len(args)==1 else args[0]+args[1] if n.op=='+'
                   else args[0]-args[1] if n.op=='-' else args[0]*args[1])
            invalid=not lo<=value<=hi
        elif n.op in ['/','%']: invalid=args==[lo,-1]
        elif n.op in ['<<','>>']:
            invalid=args[0]<0 or n.op=='<<' and args[0] << args[1] > hi
        if invalid: bad.append(i)
    return bad
