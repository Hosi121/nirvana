"""Static memory sites aligned through the fixed state[4] / SysV RDI ABI.

Counts describe C syntax, not dynamic effects or value equivalence. Addresses
are relative to the entry state pointer. Unknown roots/indices remain visible;
field names, local names and source coordinates are never address evidence.
"""
from collections import Counter
from dataclasses import dataclass

from . import c_footprint as cf

METRIC = 'nirvana-state4-memory-sites-v1'
STATE_REGISTER = 7
STATE_BYTES = 32
MASK = 2**64 - 1
HELPERS = {'nirvana_load': ('read', 'scalar', 3), 'nirvana_store': ('write', 'scalar', 4),
           'nirvana_view_load': ('read', 'view', 3), 'nirvana_view_store': ('write', 'view', 4)}
ADAPTERS = {'nirvana_location_address', 'nirvana_location_view', 'nirvana_view_index',
            'nirvana_offset', 'nirvana_test_read_offset'}


def strip(node):
    while (node.get('kind') in ['ParenExpr', 'ConstantExpr']
           or node.get('kind') == 'GenericSelectionExpr'
           or node.get('kind') == 'ImplicitCastExpr' and node.get('castKind') in
           ['LValueToRValue', 'NoOp', 'ArrayToPointerDecay', 'FunctionToPointerDecay']):
        parts = cf.children(node)
        if node.get('kind') == 'GenericSelectionExpr':
            selected = [n for n in parts if n.get('selected') is True]
            if len(selected) != 1 or not cf.children(selected[0]):
                raise cf.Unsupported('state memory generic selection')
            node = cf.children(selected[0])[-1]
            continue
        if len(parts) != 1: raise cf.Unsupported('state memory wrapper shape')
        node = parts[0]
    return node


def integer_type(node):
    text = cf.type_key(node).replace('const ', '').replace(' ', '')
    for bits, names in [(8, ['uint8_t', 'unsignedchar']), (16, ['uint16_t', 'unsignedshort']),
                        (32, ['uint32_t', 'unsignedint']), (64, ['uint64_t', 'unsignedlong', 'unsignedlonglong'])]:
        if text in names: return bits, False
    if text in ['int', 'signedint']: return 32, True
    if text in ['long', 'longlong']: return 64, True
    return None


def integer_value(value, node):
    kind = integer_type(node)
    if kind is None: return None
    bits, signed = kind
    if not signed: return value & (2**bits - 1)
    return value if -2**(bits - 1) <= value < 2**(bits - 1) else None


def u64_type(node, pointer=False):
    text = cf.type_key(node).replace('const ', '').replace('volatile ', '').replace(' ', '')
    if pointer:
        if not text.endswith('*'): return False
        text = text[:-1]
    return text in ['uint64_t', 'unsignedlong', 'unsignedlonglong']


def callee(node):
    parts = cf.children(node)
    if node.get('kind') != 'CallExpr' or not parts: return None
    ref = cf.strip(parts[0]).get('referencedDecl', {})
    return ref.get('name') if ref.get('kind') == 'FunctionDecl' else None


@dataclass(frozen=True)
class Address:
    # None means a known state base with an unresolved displacement.
    offset: int | None


class Resolver:
    def __init__(self, root, parameter):
        params = [n for n in cf.children(root) if n.get('kind') == 'ParmVarDecl']
        self.root = params[parameter]['id']
        self.declarations, self.fields, self.mutated = {}, {}, set()
        pending = [root]
        while pending:
            node = pending.pop(); kind = node.get('kind'); parts = cf.children(node)
            if kind == 'VarDecl': self.declarations[node['id']] = node
            if kind == 'RecordDecl':
                fields = [n for n in parts if n.get('kind') == 'FieldDecl']
                self.fields.update({n['id']: i for i, n in enumerate(fields)})
            if ((kind in ['BinaryOperator', 'CompoundAssignOperator'] and node.get('opcode') == '=')
                    or kind == 'CompoundAssignOperator'
                    or kind == 'UnaryOperator' and node.get('opcode') in ['++', '--', '&']):
                if parts:
                    target = strip(parts[0])
                    if target.get('kind') == 'DeclRefExpr': self.mutated.add(target['referencedDecl']['id'])
            pending.extend(parts)

    def initial(self, node, seen=frozenset(), depth=0):
        if depth > 32: return None
        node = strip(node)
        if node.get('kind') == 'DeclRefExpr':
            identity = node.get('referencedDecl', {}).get('id')
            declaration = self.declarations.get(identity)
            if declaration is not None and identity not in self.mutated and identity not in seen:
                typename = cf.type_key(declaration)
                parts = cf.children(declaration)
                # Top-level const scalar/record values only. A pointer to const
                # data does not make the pointer variable immutable.
                if typename.startswith('const ') and '*' not in typename and 'volatile' not in typename and len(parts) == 1:
                    return self.initial(parts[0], seen | {identity}, depth + 1)
        if node.get('kind') == 'MemberExpr' and not node.get('isArrow'):
            if 'volatile' in cf.type_key(node): return None
            parts = cf.children(node)
            index = self.fields.get(node.get('referencedMemberDecl'))
            base = self.initial(parts[0], seen, depth + 1) if len(parts) == 1 else None
            if base is not None and base.get('kind') == 'InitListExpr' and index is not None:
                values = cf.children(base)
                if index < len(values): return self.initial(values[index], seen, depth + 1)
            if base is not None and base.get('kind') == 'InitListExpr' and cf.type_key(base) == 'struct nirvana_view':
                values = cf.children(base)
                if len(values) == 1 and u64_type(node): return self.initial(values[0], seen, depth + 1)
            return None
        return node

    def constant(self, node, depth=0):
        if depth > 32: return None
        node = self.initial(node)
        if node is None: return None
        parts = cf.children(node); kind = node.get('kind')
        if kind == 'IntegerLiteral': return integer_value(int(node['value']), node)
        if kind in ['ImplicitCastExpr', 'CStyleCastExpr'] and len(parts) == 1:
            value = self.constant(parts[0], depth + 1)
            return None if value is None else integer_value(value, node)
        if kind == 'UnaryOperator' and len(parts) == 1 and node.get('opcode') in ['+', '-']:
            value = self.constant(parts[0], depth + 1)
            return None if value is None else integer_value(value if node['opcode'] == '+' else -value, node)
        if kind == 'BinaryOperator' and len(parts) == 2 and node.get('opcode') in ['+', '-', '*']:
            a, b = (self.constant(n, depth + 1) for n in parts)
            if a is None or b is None: return None
            return integer_value({'+': lambda: a + b, '-': lambda: a - b, '*': lambda: a * b}[node['opcode']](), node)
        return None

    def address(self, node, mode, depth=0):
        if depth > 32: return None
        node = self.initial(node)
        if node is None: return None
        kind = node.get('kind'); parts = cf.children(node)
        if (kind in ['ImplicitCastExpr', 'CStyleCastExpr'] and len(parts) == 1 and mode != 'pointer'
                and integer_type(node) == integer_type(parts[0]) == (64, False)):
            return self.address(parts[0], mode, depth + 1)
        if kind == 'DeclRefExpr' and node.get('referencedDecl', {}).get('id') == self.root:
            return None if self.root in self.mutated else Address(0)
        if mode == 'view' and kind == 'InitListExpr' and cf.type_key(node) == 'struct nirvana_view' and len(parts) == 1:
            return self.address(parts[0], 'scalar', depth + 1)
        if kind == 'CallExpr' and mode != 'pointer':
            name = callee(node); args = parts[1:]
            if name == 'nirvana_location_address' and len(args) == 1:
                return self.address(args[0], 'scalar', depth + 1)
            if name == 'nirvana_location_view' and len(args) == 1:
                return self.address(args[0], 'view', depth + 1)
            if name == 'nirvana_view_index' and len(args) == 4:
                base = self.address(args[0], 'view', depth + 1)
                index, stride, offset = (self.constant(n) for n in args[1:])
                delta = None if None in [index, stride, offset] else index * stride + offset
                return self.add(base, delta, True)
        if kind == 'BinaryOperator' and len(parts) == 2 and node.get('opcode') in ['+', '-']:
            scale = 8 if mode == 'pointer' else 1
            base, delta = self.address(parts[0], mode, depth + 1), self.constant(parts[1])
            if base is not None:
                if delta is not None: delta *= scale * (-1 if node['opcode'] == '-' else 1)
                return self.add(base, delta, mode != 'pointer')
            if node['opcode'] == '+':
                base, delta = self.address(parts[1], mode, depth + 1), self.constant(parts[0])
                return self.add(base, None if delta is None else delta * scale, mode != 'pointer')
        return None

    @staticmethod
    def add(base, delta, wrapping):
        if base is None: return None
        if base.offset is None or delta is None: return Address(None)
        value = base.offset + delta
        return Address(value & MASK if wrapping else value)

    def place(self, node):
        node = strip(node); parts = cf.children(node)
        if node.get('kind') == 'ArraySubscriptExpr' and len(parts) == 2:
            base = self.address(parts[0], 'pointer')
            index = self.constant(parts[1])
            return self.add(base, None if index is None else index * 8, False), 8 if u64_type(node) else None
        if node.get('kind') == 'UnaryOperator' and node.get('opcode') == '*' and len(parts) == 1:
            return self.address(parts[0], 'pointer'), 8 if u64_type(node) else None
        if node.get('kind') == 'MemberExpr': return None, None
        return None


def observe(text, name, parameter, source):
    cf.measure(text, name)  # Reuse the bounded C11 AST grammar and VLA exclusion.
    root = cf.function(text, name)
    resolver = Resolver(root, parameter)
    known, unknown, calls = Counter(), Counter(), Counter()

    def record(access, place):
        if place is None: return
        address, width = place
        if width not in [1, 2, 4, 8]: unknown[(access, 'width')] += 1
        elif address is None: unknown[(access, 'root')] += 1
        elif address.offset is None: unknown[(access, 'offset')] += 1
        else: known[(access, address.offset, width)] += 1

    pending = [root]
    while pending:
        node = pending.pop(); kind = node.get('kind'); parts = cf.children(node)
        if kind == 'UnaryExprOrTypeTraitExpr': continue
        if kind == 'GenericSelectionExpr':
            pending.extend(n for n in parts if n.get('selected') is True)
            continue
        if kind == 'CallExpr':
            target = callee(node)
            if not source and target in HELPERS:
                access, mode, arity = HELPERS[target]
                args = parts[1:]
                if len(args) != arity: raise cf.Unsupported('state memory helper arity')
                record(access, (resolver.address(args[1], mode), resolver.constant(args[2])))
            elif source or target not in ADAPTERS:
                calls[target or '<indirect>'] += 1
        if source:
            if kind == 'ImplicitCastExpr' and node.get('castKind') == 'LValueToRValue' and len(parts) == 1:
                record('read', resolver.place(parts[0]))
            if kind == 'BinaryOperator' and node.get('opcode') == '=' and len(parts) == 2:
                record('write', resolver.place(parts[0]))
            if kind == 'CompoundAssignOperator' or kind == 'UnaryOperator' and node.get('opcode') in ['++', '--']:
                place = resolver.place(parts[0])
                record('read', place); record('write', place)
        pending.extend(parts)
    sites = [{'access': access, 'byte_offset': offset, 'width': width, 'count': count,
              'state_word': offset // 8 if 0 <= offset < STATE_BYTES and offset % 8 == 0 and width == 8 else None}
             for (access, offset, width), count in sorted(known.items())]
    outside = sum(n['count'] for n in sites if not 0 <= n['byte_offset'] <= STATE_BYTES - n['width'])
    return {'status': 'partial' if unknown or calls or outside else 'measured', 'sites': sites,
            'resolved_sites': sum(known.values()), 'unresolved_sites': sum(unknown.values()),
            'outside_state_sites': outside,
            'unresolved': [{'access': access, 'reason': reason, 'count': count} for (access, reason), count in sorted(unknown.items())],
            'unclassified_calls': dict(sorted(calls.items()))}


def measure(source_text, generated_text, name, parameters):
    if (not isinstance(parameters, list) or len(parameters) > 1024
            or any(type(n) is not int or not 0 <= n < 2**32 for n in parameters)
            or len(set(parameters)) != len(parameters) or STATE_REGISTER not in parameters):
        raise cf.Unsupported('missing unique state-register ABI descriptor')
    a = cf.function(source_text, name); b = cf.function(generated_text, 'nirvana_readable')
    source_params = [n for n in cf.children(a) if n.get('kind') == 'ParmVarDecl']
    generated_params = [n for n in cf.children(b) if n.get('kind') == 'ParmVarDecl']
    if len(source_params) != 1 or not u64_type(source_params[0], pointer=True):
        raise cf.Unsupported('source outside the state[4] ABI')
    if len(generated_params) != len(parameters) + 3 or not all(u64_type(n) for n in generated_params[:len(parameters)]):
        raise cf.Unsupported('generated parameters differ from the ABI descriptor')
    source = observe(source_text, name, 0, True)
    generated = observe(generated_text, 'nirvana_readable', parameters.index(STATE_REGISTER), False)
    return {'metric': METRIC, 'status': 'measured' if source['status'] == generated['status'] == 'measured' else 'partial',
            'profile': {'state_register': STATE_REGISTER, 'source_parameter': 0,
                        'generated_parameter': parameters.index(STATE_REGISTER), 'state_bytes': STATE_BYTES, 'word_bytes': 8},
            'source': source, 'generated': generated, 'source_generated_delta': delta(source, generated)}


def delta(before, after):
    def inventory(value, field):
        if field == 'sites':
            return {f"{n['access']}@{n['byte_offset']}:{n['width']}": n['count'] for n in value[field]}
        return {f"{n['access']}:{n['reason']}": n['count'] for n in value[field]}
    def difference(a, b):
        return {key: b.get(key, 0) - a.get(key, 0) for key in sorted(a.keys() | b.keys())
                if a.get(key, 0) != b.get(key, 0)}
    result = {field: difference(inventory(before, field), inventory(after, field)) for field in ['sites', 'unresolved']}
    result['unclassified_calls'] = difference(before['unclassified_calls'], after['unclassified_calls'])
    return result
