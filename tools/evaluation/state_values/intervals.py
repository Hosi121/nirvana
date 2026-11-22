"""Conservative numeric intervals of immutable C bit-vector values.

They overapproximate all four input words, independently of path guards. Signed
operations enter the graph only after their mathematical range fits the type.
Unsigned wrap loses precision when an interval crosses a modular boundary.
"""


def domain(typ):
    return (-(1 << (typ.bits-1)), (1 << (typ.bits-1))-1) if typ.signed else (0,(1 << typ.bits)-1)


def number(value,typ):
    return value-(1 << typ.bits) if typ.signed and value >> (typ.bits-1) else value


def wrap(bounds,typ):
    lo,hi=bounds;modulus=1 << typ.bits
    minimum,maximum=domain(typ)
    if minimum<=lo<=hi<=maximum: return bounds
    if lo//modulus != hi//modulus: return domain(typ)
    lo,hi=lo%modulus,hi%modulus
    if not typ.signed: return lo,hi
    half=modulus//2
    if hi<half: return lo,hi
    if lo>=half: return lo-modulus,hi-modulus
    return domain(typ)


def arithmetic(op,a,b):
    if op=='+': return a[0]+b[0],a[1]+b[1]
    if op=='-': return a[0]-b[1],a[1]-b[0]
    products=[x*y for x in a for y in b]
    return min(products),max(products)


def derive(node,bounds):
    op,typ=node.op,node.type
    full=domain(typ)
    if op=='input': return full
    if op=='const':
        value=number(node.value,typ);return value,value
    if op in ['cast','bitcast']: return wrap(bounds[0],typ)
    if op=='truth':
        lo,hi=bounds[0]
        return (0,0) if hi==lo==0 else (1,1) if lo>0 or hi<0 else (0,1)
    if op=='ite': return min(b[0] for b in bounds[1:]),max(b[1] for b in bounds[1:])
    if op=='extract':
        if bounds[0][0]<0: return full
        return 0,min(full[1],bounds[0][1] >> node.value)
    if op=='pack': return tuple(sum(b[k] << (i*8) for i,b in enumerate(bounds)) for k in [0,1])
    if op in ['==','!=','<','<=','>','>=']: return 0,1
    if len(bounds)==1:
        lo,hi=bounds[0]
        if op=='-': return wrap((-hi,-lo),typ)
        if op=='~':
            return (-hi-1,-lo-1) if typ.signed else (full[1]-hi,full[1]-lo)
        return full
    a,b=bounds
    if op in ['+','-','*']: return wrap(arithmetic(op,a,b),typ)
    if op=='&':
        positive=[r[1] for r in bounds if r[0]>=0]
        return (0,min(positive)) if positive else full
    if op in ['|','^']:
        return (0,(1 << max(a[1],b[1]).bit_length())-1) if min(a[0],b[0])>=0 else full
    if op in ['<<','>>'] and b[0]==b[1] and 0<=b[0]<typ.bits and a[0]>=0:
        return wrap((a[0] << b[0],a[1] << b[0]),typ) if op=='<<' else (a[0] >> b[0],a[1] >> b[0])
    if op in ['/','%'] and b[0]==b[1] and b[0]!=0:
        divisor=b[0]
        if op=='/':
            def quotient(n): return abs(n)//abs(divisor)*(-1 if (n<0)!=(divisor<0) else 1)
            ends=[quotient(n) for n in a]
            return wrap((min(ends),max(ends)),typ)
        bound=abs(divisor)-1
        return max(a[0],-bound) if a[0]<0 else 0,min(a[1],bound) if a[1]>0 else 0
    return full
