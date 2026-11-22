"""Typed, immutable bit-vector values for the state[4] C evaluation profile.

Explicit casts preserve C widths and signed extension. Unknown signed overflow,
out-of-range signed conversions, zero divisors and nonconstant shifts remain
outside this first profile. Graph IDs and storage/local identities are separate.
"""
from dataclasses import dataclass
import hashlib
import json


class Unsupported(ValueError):
    pass


@dataclass(frozen=True)
class Type:
    bits: int
    signed: bool = False

    def __post_init__(self):
        if (type(self.bits) is not int or self.bits not in [1, 8, 16, 32, 64] or type(self.signed) is not bool
                or self.bits == 1 and self.signed):
            raise Unsupported('scalar type outside profile')


U64 = Type(64)
BYTE = Type(8)
BOOL = Type(1)


@dataclass(frozen=True)
class Node:
    op: str
    type: Type
    args: tuple = ()
    value: int | None = None


def mask(typ):
    return (1 << typ.bits) - 1


def number(value, typ):
    return value - (1 << typ.bits) if typ.signed and value >> (typ.bits - 1) else value


class Graph:
    def __init__(self):
        self.nodes, self.ids = [], {}
        self.inputs = [self.intern(Node('input', U64, value=i)) for i in range(4)]

    def intern(self, node):
        if node in self.ids: return self.ids[node]
        if len(self.nodes) >= 4096: raise Unsupported('value graph node budget')
        identity = len(self.nodes)
        if any(type(i) is not int or not 0 <= i < identity for i in node.args):
            raise Unsupported('value graph operand order')
        self.ids[node] = identity
        self.nodes.append(node)
        return identity

    def type(self, value): return self.nodes[value].type
    def constant(self, value):
        n = self.nodes[value]
        return n.value if n.op == 'const' else None

    def const(self, value, typ=U64):
        return self.intern(Node('const', typ, value=value & mask(typ)))

    def cast(self, value, typ):
        before = self.type(value)
        if before == typ: return value
        if typ == BOOL: return self.truth(value)
        constant = self.constant(value)
        if typ.signed:
            if constant is not None:
                n = number(constant, before)
                if not -(1 << (typ.bits - 1)) <= n < 1 << (typ.bits - 1):
                    raise Unsupported('out-of-range signed conversion')
            elif typ.bits < before.bits or typ.bits == before.bits and not before.signed:
                raise Unsupported('unknown signed conversion range')
        if constant is not None: return self.const(number(constant, before), typ)
        return self.intern(Node('cast', typ, (value,)))

    def truth(self, value):
        if self.type(value) == BOOL: return value
        constant = self.constant(value)
        if constant is not None: return self.const(int(constant != 0), BOOL)
        return self.intern(Node('truth', BOOL, (value,)))

    def choose(self, condition, a, b):
        condition = self.truth(condition)
        if self.type(a) != self.type(b): raise Unsupported('conditional result types')
        constant = self.constant(condition)
        if constant is not None: return a if constant else b
        if a == b: return a
        return self.intern(Node('ite', self.type(a), (condition, a, b)))

    def unary(self, op, value, typ):
        if op == '!': return self.cast(self.binary('==', value, self.const(0, self.type(value)), BOOL), typ)
        if self.type(value) != typ: raise Unsupported('unary promotion')
        if op == '+': return value
        if op not in ['-', '~']: raise Unsupported('unary operator')
        n = self.constant(value)
        if op == '-' and typ.signed:
            if n is None or number(n, typ) == -(1 << (typ.bits - 1)):
                raise Unsupported('unknown signed negation range')
        if n is not None: return self.const(-n if op == '-' else ~n, typ)
        return self.intern(Node(op, typ, (value,)))

    def binary(self, op, a, b, typ):
        if op in ['&&', '||']:
            value = self.binary('&' if op == '&&' else '|', self.truth(a), self.truth(b), BOOL)
            return self.cast(value, typ)
        before = self.type(a)
        compare = op in ['==', '!=', '<', '<=', '>', '>=']
        if op in ['<<', '>>']:
            count = self.constant(b)
            if count is None or not 0 <= number(count, self.type(b)) < before.bits:
                raise Unsupported('unknown or invalid shift count')
            b = self.const(count, Type(before.bits))
            if typ != before or before.signed: raise Unsupported('signed shift outside profile')
        elif self.type(b) != before or not compare and typ != before:
            raise Unsupported('binary operand promotions')
        if op not in ['+', '-', '*', '&', '|', '^', '/', '%', '<<', '>>', '==', '!=', '<', '<=', '>', '>=']:
            raise Unsupported('binary operator')
        x, y = self.constant(a), self.constant(b)
        if before == typ == BOOL and op in ['&', '|', '^']:
            if a == b: return self.const(0, BOOL) if op == '^' else a
            if op == '&':
                if 0 in [x, y]: return self.const(0, BOOL)
                if x == 1: return b
                if y == 1: return a
            if op == '|':
                if 1 in [x, y]: return self.const(1, BOOL)
                if x == 0: return b
                if y == 0: return a
            if op == '^':
                if x == 0: return b
                if y == 0: return a
        if before.signed and op in ['+', '-', '*', '/', '%'] and (x is None or y is None):
            raise Unsupported('unknown signed arithmetic range')
        if op in ['/', '%'] and (y is None or y == 0): raise Unsupported('unknown or zero divisor')
        if (before.signed and op in ['/', '%'] and x is not None
                and number(x, before) == -(1 << (before.bits - 1)) and number(y, before) == -1):
            raise Unsupported('signed quotient overflow')
        if x is not None and y is not None:
            value = self.calculate(Node(op, typ, (a, b)), [x, y])
            if before.signed and op in ['+', '-', '*', '/', '%'] and not -(1 << (typ.bits - 1)) <= value < 1 << (typ.bits - 1):
                raise Unsupported('signed arithmetic overflow')
            return self.const(value, typ)
        return self.intern(Node(op, typ, (a, b)))

    def extract(self, value, start, bits=8):
        typ = Type(bits)
        if not 0 <= start <= self.type(value).bits - bits: raise Unsupported('bit extraction range')
        if start == 0 and bits == self.type(value).bits: return self.cast(value, typ)
        n = self.constant(value)
        if n is not None: return self.const(n >> start, typ)
        return self.intern(Node('extract', typ, (value,), start))

    def pack(self, little_endian):
        if len(little_endian) not in [1, 2, 4, 8] or any(self.type(n) != BYTE for n in little_endian):
            raise Unsupported('byte packing width')
        if len(little_endian) == 1: return little_endian[0]
        typ = Type(len(little_endian) * 8)
        parts = [self.nodes[n] for n in little_endian]
        if all(n.op == 'const' for n in parts):
            return self.const(sum(n.value << (i * 8) for i, n in enumerate(parts)), typ)
        if (all(n.op == 'extract' and n.value == i * 8 and n.args == parts[0].args for i, n in enumerate(parts))
                and self.type(parts[0].args[0]).bits == typ.bits):
            return self.cast(parts[0].args[0], typ)
        return self.intern(Node('pack', typ, tuple(little_endian)))

    def calculate(self, node, values):
        op, typ = node.op, node.type
        if op == 'cast': return number(values[0], self.type(node.args[0])) & mask(typ)
        if op == 'truth': return int(values[0] != 0)
        if op == 'ite': return values[1] if values[0] else values[2]
        if op == 'extract': return values[0] >> node.value
        if op == 'pack': return sum(v << (i * 8) for i, v in enumerate(values))
        if len(values) == 1: return -values[0] if op == '-' else ~values[0]
        before = self.type(node.args[0])
        x, y = (number(v, before) for v in values)
        if op in ['/', '%']:
            quotient = abs(x) // abs(y) * (-1 if (x < 0) != (y < 0) else 1)
            return quotient if op == '/' else x - quotient * y
        return {'+': lambda: x + y, '-': lambda: x - y, '*': lambda: x * y,
                '&': lambda: x & y, '|': lambda: x | y, '^': lambda: x ^ y,
                '<<': lambda: x << y, '>>': lambda: x >> y,
                '==': lambda: int(x == y), '!=': lambda: int(x != y),
                '<': lambda: int(x < y), '<=': lambda: int(x <= y),
                '>': lambda: int(x > y), '>=': lambda: int(x >= y)}[op]()

    def evaluate(self, roots, inputs):
        if len(inputs) != 4 or any(type(v) is not int or not 0 <= v < 2**64 for v in inputs):
            raise Unsupported('state input words')
        values = []
        for node in self.nodes:
            value = inputs[node.value] if node.op == 'input' else node.value if node.op == 'const' else self.calculate(node, [values[i] for i in node.args])
            values.append(value & mask(node.type))
        return [values[i] for i in roots]

    def summary(self, roots):
        fingerprints = []
        for n in self.nodes:
            content = [n.op, n.type.bits, n.type.signed, n.value, [fingerprints[a] for a in n.args]]
            fingerprints.append(hashlib.sha256(json.dumps(content, separators=(',', ':')).encode()).hexdigest())
        seen, pending = set(), list(roots)
        while pending:
            i = pending.pop()
            if i not in seen:
                seen.add(i); pending.extend(self.nodes[i].args)
        return {'reachable_value_nodes': len(seen), 'output_fingerprints': [fingerprints[i] for i in roots]}

    def smt(self):
        ref = lambda i: f'v{i}'
        def literal(n, typ): return f'(_ bv{n} {typ.bits})'
        lines = ['(set-logic QF_BV)\n']
        for i, node in enumerate(self.nodes):
            op, typ = node.op, node.type
            args = [ref(a) for a in node.args]
            if op == 'input':
                lines.append(f'(declare-fun word{node.value} () (_ BitVec 64))\n')
                term = f'word{node.value}'
            elif op == 'const': term = literal(node.value, typ)
            elif op == 'cast':
                before = self.type(node.args[0]); a = args[0]
                term = (a if typ.bits == before.bits else f'((_ extract {typ.bits - 1} 0) {a})' if typ.bits < before.bits
                        else f'((_ {"sign_extend" if before.signed else "zero_extend"} {typ.bits - before.bits}) {a})')
            elif op == 'truth': term = f'(ite (distinct {args[0]} {literal(0, self.type(node.args[0]))}) #b1 #b0)'
            elif op == 'ite': term = f'(ite (= {args[0]} #b1) {args[1]} {args[2]})'
            elif op == 'extract': term = f'((_ extract {node.value + typ.bits - 1} {node.value}) {args[0]})'
            elif op == 'pack':
                term = args[-1]
                for a in reversed(args[:-1]): term = f'(concat {term} {a})'
            elif len(args) == 1: term = f'({"bvneg" if op == "-" else "bvnot"} {args[0]})'
            elif op in ['==', '!=', '<', '<=', '>', '>=']:
                signed = self.type(node.args[0]).signed
                operator = {'==': '=', '!=': 'distinct', '<': 'bvslt' if signed else 'bvult',
                            '<=': 'bvsle' if signed else 'bvule', '>': 'bvsgt' if signed else 'bvugt',
                            '>=': 'bvsge' if signed else 'bvuge'}[op]
                term = f'(ite ({operator} {args[0]} {args[1]}) {literal(1, typ)} {literal(0, typ)})'
            else:
                operator = {'+': 'bvadd', '-': 'bvsub', '*': 'bvmul', '&': 'bvand', '|': 'bvor', '^': 'bvxor',
                            '/': 'bvudiv', '%': 'bvurem', '<<': 'bvshl', '>>': 'bvlshr'}[op]
                term = f'({operator} {args[0]} {args[1]})'
            lines.append(f'(define-fun v{i} () (_ BitVec {typ.bits}) {term})\n')
        return ''.join(lines)
