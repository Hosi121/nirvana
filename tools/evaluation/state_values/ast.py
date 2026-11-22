"""Translate a closed C11 if/return subset into immutable state values.

This oracle owns local snapshots and 32 individual state bytes. Scalar calls,
loops, goto, volatile objects and unresolved addresses stay unsupported. The
generated side uses the fixed Nirvana checked-memory helper contracts; C
storage names and view field spellings do not identify values or addresses.
"""
from dataclasses import dataclass

from .. import c_footprint as cf, state_memory as sm
from .terms import Graph, Type, U64, BYTE, BOOL, Unsupported


def ctype(node):
    text = cf.type_key(node)
    if 'volatile' in text: raise Unsupported('volatile scalar')
    result = sm.integer_type(node)
    if result is not None: return Type(*result)
    text = text.replace('const ', '').replace(' ', '')
    if text == '_Bool': return BOOL
    if text in ['signedchar', 'int8_t']: return Type(8, True)
    if text in ['short', 'shortint', 'signedshort', 'signedshortint', 'int16_t']: return Type(16, True)
    raise Unsupported('scalar type: ' + text)


@dataclass
class State:
    guard: int
    locals: dict
    memory: list

    def copy(self, guard): return State(guard, self.locals.copy(), self.memory.copy())


@dataclass
class Model:
    outputs: list
    paths: int
    expanded_assignments: int
    scalar_declarations: int


class Interpreter:
    def __init__(self, graph, text, name, parameter, source):
        cf.measure(text, name)
        self.root = cf.function(text, name)
        self.resolver = sm.Resolver(self.root, parameter)
        self.graph, self.source = graph, source
        self.memory_context = None
        self.parameters = [n for n in cf.children(self.root) if n.get('kind') == 'ParmVarDecl']
        self.returns, self.work, self.assignments, self.declarations = [], 10000, 0, set()
        if cf.type_key(self.root).split('(')[0].strip() not in ['uint64_t', 'unsigned long', 'unsigned long long']:
            raise Unsupported('return outside uint64_t profile')
        if source:
            if parameter != 0 or len(self.parameters) != 1 or not sm.u64_type(self.parameters[0], pointer=True):
                raise Unsupported('source outside state-pointer ABI')
        elif (not 0 <= parameter < len(self.parameters) - 3
              or any(not sm.u64_type(p) for p in self.parameters[:-3])
              or cf.type_key(self.parameters[-3]).replace(' ', '') not in ['uint8_t*', 'unsignedchar*']
              or any(not sm.u64_type(p) for p in self.parameters[-2:])):
            raise Unsupported('generated parameters outside fixed ABI')
        pending = [self.root]
        while pending:
            node = pending.pop()
            if 'volatile' in cf.type_key(node): raise Unsupported('volatile object')
            pending.extend(cf.children(node))

    def spend(self):
        self.work -= 1
        if self.work < 0: raise Unsupported('C value evaluation work budget')

    def location(self, address, width):
        if (address is None or address.offset is None or width not in [1, 2, 4, 8]
                or not 0 <= address.offset <= 32 - width):
            raise Unsupported('memory outside resolved state bytes')
        return address.offset, width

    def place(self, node):
        address, width = self.resolver.place(node)
        return self.location(address, width)

    def helper_place(self, node):
        parts = cf.children(node); target = sm.callee(node); args = parts[1:]
        if self.source or target not in sm.HELPERS and target not in ['nirvana_offset', 'nirvana_test_read_offset']:
            raise Unsupported('call outside checked-memory contracts')
        if target in sm.HELPERS:
            access, mode, arity = sm.HELPERS[target]
        else:
            access, mode, arity = 'check', 'scalar', 3
        if len(args) != arity: raise Unsupported('checked-memory helper arity')
        context = sm.strip(args[0]); children = cf.children(context)
        if (context.get('kind') != 'UnaryOperator' or context.get('opcode') != '&' or len(children) != 1
                or sm.strip(children[0]).get('referencedDecl', {}).get('id') != self.memory_context
                or self.memory_context is None):
            raise Unsupported('checked-memory context differs from ABI')
        place = self.location(self.resolver.address(args[1], mode), self.resolver.constant(args[2]))
        return access, place, args

    def load(self, state, place):
        offset, width = place
        return self.graph.pack(state.memory[offset:offset + width])

    def store(self, state, place, value):
        offset, width = place
        value = self.graph.cast(value, U64)
        state.memory[offset:offset + width] = [self.graph.extract(value, i * 8) for i in range(width)]
        self.assignments += 1

    def value(self, original, state):
        self.spend()
        node = sm.strip(original); parts = cf.children(node); kind = node.get('kind'); g = self.graph
        if kind == 'IntegerLiteral': return g.const(int(node['value']), ctype(node))
        if kind == 'DeclRefExpr':
            identity = node.get('referencedDecl', {}).get('id')
            result = state.locals.get(identity)
            if result is None: raise Unsupported('scalar read lacks a defined local value')
            return result
        if kind in ['ImplicitCastExpr', 'CStyleCastExpr'] and len(parts) == 1:
            return g.cast(self.value(parts[0], state), ctype(node))
        if kind == 'UnaryOperator' and node.get('opcode') in ['+', '-', '~', '!'] and len(parts) == 1:
            return g.unary(node['opcode'], self.value(parts[0], state), ctype(node))
        if kind == 'BinaryOperator' and len(parts) == 2:
            a, b = [self.value(n, state) for n in parts]
            return g.binary(node['opcode'], a, b, ctype(node))
        if kind == 'ConditionalOperator' and len(parts) == 3:
            c, a, b = [self.value(n, state) for n in parts]
            return g.choose(c, a, b)
        if kind == 'CallExpr':
            access, place, _ = self.helper_place(node)
            if access == 'read': return g.cast(self.load(state, place), U64)
            if access == 'check': return g.const(128 + place[0])
            raise Unsupported('store inside a scalar expression')
        if kind == 'ArraySubscriptExpr' or kind == 'UnaryOperator' and node.get('opcode') == '*':
            if not self.source: raise Unsupported('raw generated pointer dereference')
            return g.cast(self.load(state, self.place(node)), ctype(node))
        raise Unsupported('scalar expression: ' + str(kind))

    def lvalue(self, original, state, value=None):
        node = sm.strip(original); g = self.graph
        if node.get('kind') == 'DeclRefExpr':
            identity = node.get('referencedDecl', {}).get('id')
            if identity not in state.locals: raise Unsupported('assignment outside local scalar storage')
            if value is None:
                if state.locals[identity] is None: raise Unsupported('uninitialized compound assignment')
                return state.locals[identity]
            state.locals[identity] = g.cast(value, ctype(node)); self.assignments += 1
        else:
            if not self.source: raise Unsupported('generated assignment outside local storage')
            place = self.place(node)
            if value is None: return self.load(state, place)
            self.store(state, place, value)

    def address_initializer(self, node):
        node = sm.strip(node)
        if node.get('kind') == 'InitListExpr':
            return all(self.address_initializer(n) for n in cf.children(node))
        address = self.resolver.address(node, 'scalar')
        return address is not None and address.offset is not None or self.resolver.constant(node) is not None

    def declaration(self, node, state):
        parts = cf.children(node); g = self.graph
        typename = cf.type_key(node).replace('const ', '')
        if typename == 'struct nirvana_memory' and not self.source:
            if self.memory_context is not None or len(parts) != 1 or parts[0].get('kind') != 'InitListExpr':
                raise Unsupported('memory context initializer')
            args = [sm.strip(n) for n in cf.children(parts[0])]
            if (len(args) != 3 or [n.get('referencedDecl', {}).get('id') for n in args]
                    != [n['id'] for n in self.parameters[-3:]]):
                raise Unsupported('memory context is not the fixed ABI')
            self.memory_context = node['id']; return
        if typename.startswith('struct '):
            if self.source or len(parts) != 1 or not self.address_initializer(parts[0]):
                raise Unsupported('record outside immutable address setup')
            return
        typ = ctype(node)
        identity = node['id']
        if identity in state.locals: raise Unsupported('repeated scalar declaration')
        if len(parts) > 1: raise Unsupported('scalar initializer shape')
        if parts and self.resolver.address(parts[0], 'scalar') is not None:
            if not self.address_initializer(parts[0]): raise Unsupported('unresolved address initializer')
            # Pure captured addresses are used by Resolver, rather than as
            # scalar source values. Any value escape remains unsupported.
            return
        state.locals[identity] = g.cast(self.value(parts[0], state), typ) if parts else None
        self.declarations.add(identity)

    def statement(self, node, state):
        self.spend()
        kind, parts, g = node.get('kind'), cf.children(node), self.graph
        if kind == 'CompoundStmt': return self.sequence(parts, [state])
        if kind == 'IfStmt' and len(parts) in [2, 3]:
            condition = g.truth(self.value(parts[0], state))
            yes = g.binary('&', state.guard, condition, BOOL)
            no = g.binary('&', state.guard, g.unary('!', condition, BOOL), BOOL)
            return self.statement(parts[1], state.copy(yes)) + (self.statement(parts[2], state.copy(no)) if len(parts) == 3 else [state.copy(no)])
        if kind == 'ReturnStmt' and len(parts) == 1:
            result = g.cast(self.value(parts[0], state), U64)
            words = [g.pack(state.memory[n:n + 8]) for n in range(0, 32, 8)]
            self.returns.append((state.guard, [result, *words])); return []
        if kind == 'DeclStmt':
            for declaration in parts:
                if declaration.get('kind') == 'VarDecl': self.declaration(declaration, state)
                elif declaration.get('kind') not in ['RecordDecl', 'TypedefDecl']: raise Unsupported('local declaration kind')
        elif kind == 'BinaryOperator' and node.get('opcode') == '=' and len(parts) == 2:
            self.lvalue(parts[0], state, self.value(parts[1], state))
        elif kind == 'CompoundAssignOperator' and len(parts) == 2:
            left = self.lvalue(parts[0], state)
            lhs_type = ctype({'type': node.get('computeLHSType', node['type'])})
            result_type = ctype({'type': node.get('computeResultType', node['type'])})
            op = node['opcode'][:-1]
            right = self.value(parts[1], state)
            if op not in ['<<', '>>']: right = g.cast(right, result_type)
            result = g.binary(op, g.cast(left, lhs_type), right, result_type)
            self.lvalue(parts[0], state, result)
        elif kind == 'UnaryOperator' and node.get('opcode') in ['++', '--'] and len(parts) == 1:
            old = self.lvalue(parts[0], state)
            result = g.binary('+' if node['opcode'] == '++' else '-', old, g.const(1, ctype(parts[0])), ctype(parts[0]))
            self.lvalue(parts[0], state, result)
        elif kind == 'CallExpr':
            access, place, args = self.helper_place(node)
            if access == 'write': self.store(state, place, self.value(args[3], state))
            elif access not in ['read', 'check']: raise Unsupported('expression statement call')
        elif kind == 'CStyleCastExpr' and cf.type_key(node) == 'void' and len(parts) == 1:
            value = sm.strip(parts[0])
            if not (value.get('kind') == 'DeclRefExpr' and value.get('referencedDecl', {}).get('id') in {p['id'] for p in self.parameters}):
                self.value(parts[0], state)
        elif kind not in ['NullStmt']:
            raise Unsupported('control or statement: ' + str(kind))
        return [state]

    def sequence(self, statements, states):
        for statement in statements:
            states = [next_state for state in states for next_state in self.statement(statement, state)]
            if len(states) + len(self.returns) > 64: raise Unsupported('C path budget')
        return states

    def model(self):
        bodies = [n for n in cf.children(self.root) if n.get('kind') == 'CompoundStmt']
        if len(bodies) != 1: raise Unsupported('function body shape')
        memory = [self.graph.extract(self.graph.inputs[n // 8], n % 8 * 8) for n in range(32)]
        active = self.statement(bodies[0], State(self.graph.const(1, BOOL), {}, memory))
        if active or not self.returns: raise Unsupported('function may fall through')
        outputs = self.returns[-1][1]
        for guard, values in reversed(self.returns[:-1]):
            outputs = [self.graph.choose(guard, a, b) for a, b in zip(values, outputs)]
        return Model(outputs, len(self.returns), self.assignments, len(self.declarations))


def observe(graph, text, name, parameter=0, source=True):
    try: return Interpreter(graph, text, name, parameter, source).model()
    except (cf.Unsupported, IndexError, KeyError, RecursionError) as error:
        raise Unsupported('C AST profile: ' + str(error)) from error
