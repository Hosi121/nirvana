"""Translate a closed C11 subset into immutable state values.

This oracle owns local snapshots and 32 individual state bytes. Function-body
forward gotos retain their snapshots; bounded structured loops retain an
explicit incomplete guard. Nested label scopes, scalar calls,
volatile objects and unresolved addresses stay unsupported. The
generated side uses the fixed Nirvana checked-memory helper contracts; C
storage names and view field spellings do not identify values or addresses.
"""
from dataclasses import dataclass,field
from itertools import chain, islice

from .. import c_footprint as cf, state_memory as sm
from .terms import Graph, Type, U64, BYTE, BOOL, Unsupported, number
from . import helpers
from .records import Records,View

LOOP_LIMIT = 16


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
    records:dict=field(default_factory=dict)

    def copy(self, guard): return State(guard, self.locals.copy(), self.memory.copy(),self.records.copy())


@dataclass
class Model:
    outputs: list
    paths: int
    expanded_assignments: int
    scalar_declarations: int
    incomplete: int


class Interpreter:
    def __init__(self, graph, text, name, parameter, source):
        cf.measure(text, name)
        self.root = cf.function(text, name)
        self.resolver = sm.Resolver(self.root, parameter)
        self.graph, self.source = graph, source
        self.records=Records(graph,self.resolver)
        self.parameter=parameter
        self.memory_context = None
        self.parameters = [n for n in cf.children(self.root) if n.get('kind') == 'ParmVarDecl']
        self.returns, self.work, self.assignments, self.declarations = [], 10000, 0, set()
        self.gotos, self.labels, self.loops, self.truncated = [], {}, [], []
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
        bodies = [n for n in cf.children(self.root) if n.get('kind') == 'CompoundStmt']
        if len(bodies) != 1: raise Unsupported('function body shape')
        statements = self.statements = cf.children(bodies[0])
        for index, statement in enumerate(statements):
            if statement.get('kind') == 'LabelStmt':
                parts = cf.children(statement)
                if len(parts) != 1: raise Unsupported('label body shape')
                self.labels[statement['declId']] = index
        for index, statement in enumerate(statements):
            pending = [statement]
            while pending:
                node = pending.pop()
                if node.get('kind') == 'LabelStmt' and node is not statement:
                    raise Unsupported('label outside function body sequence')
                if node.get('kind') == 'GotoStmt':
                    target = self.labels.get(node.get('targetLabelDeclId'))
                    if target is None or target <= index:
                        raise Unsupported('goto outside forward function-body control')
                pending.extend(cf.children(node))

    def spend(self):
        self.work -= 1
        if self.work < 0: raise Unsupported('C value evaluation work budget')

    def location(self, address, width):
        if (address is None or address.offset is None or width not in [1, 2, 4, 8]
                or not 0 <= address.offset <= 32 - width):
            raise Unsupported('memory outside resolved state bytes')
        return address.offset, width

    def constant(self, node, state):
        result = self.resolver.constant(node)
        if result is not None: return result
        value = self.value(node, state)
        constant = self.graph.constant(value)
        return None if constant is None else number(constant, self.graph.type(value))

    def pointer(self, node, state, depth=0):
        if depth > 32: raise Unsupported('evaluated address depth')
        result = self.resolver.address(node, 'pointer')
        node = sm.strip(node); parts = cf.children(node); kind = node.get('kind')
        if kind == 'DeclRefExpr': return result
        if kind == 'BinaryOperator' and len(parts) == 2 and node.get('opcode') in ['+', '-']:
            base = self.pointer(parts[0], state, depth+1)
            if base is not None:
                delta = self.constant(parts[1], state)
                if delta is not None: delta *= 8 * (-1 if node['opcode']=='-' else 1)
                result = self.resolver.add(base, delta, False)
            elif node['opcode'] == '+':
                base = self.pointer(parts[1], state, depth+1)
                delta = self.constant(parts[0], state) if base is not None else None
                result = self.resolver.add(base, None if delta is None else delta*8, False)
            else: return None
            if result is not None and result.offset is not None and not 0 <= result.offset <= 32:
                raise Unsupported('source pointer arithmetic outside its state object')
            return result
        return None

    def place(self, node, state):
        address, width = self.resolver.place(node)
        if self.source or address is None or address.offset is None:
            node = sm.strip(node); parts = cf.children(node)
            if node.get('kind') == 'ArraySubscriptExpr' and len(parts) == 2:
                base, index = self.pointer(parts[0], state), self.constant(parts[1], state)
                address = self.resolver.add(base, None if index is None else index*8, False)
            elif node.get('kind') == 'UnaryOperator' and node.get('opcode') == '*' and len(parts) == 1:
                address = self.pointer(parts[0], state)
        return self.location(address, width)

    def helper_place(self, node, state):
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
        if mode=='view':
            view=self.records.evaluate(args[1],state,self.value)
            if not isinstance(view,View): raise Unsupported('checked-memory view argument')
            address=view.address
        else: address=self.value(args[1],state)
        raw=self.graph.constant(address)
        place=self.location(sm.Address(None if raw is None else (raw-4224)&sm.MASK),self.constant(args[2],state))
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
        if kind=='MemberExpr' and not self.source:
            result=self.records.evaluate(node,state,self.value)
            if type(result) is not int: raise Unsupported('record used as a scalar')
            return g.cast(result,ctype(node))
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
            if not self.source and sm.callee(node) in helpers.NAMES:
                value=helpers.lower(g,sm.callee(node),[self.value(n,state) for n in parts[1:]])
                if ctype(node)!=g.type(value): raise Unsupported('integer helper result type')
                return value
            access, place, _ = self.helper_place(node, state)
            if access == 'read': return g.cast(self.load(state, place), U64)
            if access == 'check': return g.const(128 + place[0])
            raise Unsupported('store inside a scalar expression')
        if kind == 'ArraySubscriptExpr' or kind == 'UnaryOperator' and node.get('opcode') == '*':
            if not self.source: raise Unsupported('raw generated pointer dereference')
            return g.cast(self.load(state, self.place(node, state)), ctype(node))
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
            place = self.place(node, state)
            if value is None: return self.load(state, place)
            self.store(state, place, value)

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
            if self.source or len(parts) != 1:
                raise Unsupported('record outside immutable address setup')
            state.records.pop(node['id'],None)
            state.records[node['id']]=self.records.evaluate(parts[0],state,self.value)
            return
        typ = ctype(node)
        identity = node['id']
        if len(parts) > 1: raise Unsupported('scalar initializer shape')
        # A loop re-enters this declaration with a fresh automatic object. Its
        # old iteration's value cannot initialize a read of the new object.
        state.locals[identity] = None
        if parts: state.locals[identity] = g.cast(self.value(parts[0], state), typ)
        self.declarations.add(identity)

    def statement(self, node, state):
        self.spend()
        kind, parts, g = node.get('kind'), cf.children(node), self.graph
        if g.constant(state.guard) == 0: return []
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
        if kind == 'GotoStmt':
            self.gotos.append((node['targetLabelDeclId'], state)); return []
        if kind == 'LabelStmt' and len(parts) == 1:
            return self.statement(parts[0], state)
        if kind in ['WhileStmt', 'ForStmt', 'DoStmt']:
            return self.loop(node, state)
        if kind in ['BreakStmt', 'ContinueStmt']:
            if not self.loops: raise Unsupported('loop transfer outside a supported loop')
            self.loops[-1]['break' if kind == 'BreakStmt' else 'continue'].append(state)
            return []
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
            access, place, args = self.helper_place(node, state)
            if access == 'write': self.store(state, place, self.value(args[3], state))
            elif access not in ['read', 'check']: raise Unsupported('expression statement call')
        elif kind == 'CStyleCastExpr' and cf.type_key(node) == 'void' and len(parts) == 1:
            value = sm.strip(parts[0])
            if not (value.get('kind') == 'DeclRefExpr' and value.get('referencedDecl', {}).get('id') in {p['id'] for p in self.parameters}):
                self.value(parts[0], state)
        elif kind not in ['NullStmt']:
            raise Unsupported('control or statement: ' + str(kind))
        return [state]

    def split(self, state, condition):
        g = self.graph
        value = g.truth(self.value(condition, state)) if condition is not None else g.const(1, BOOL)
        yes = state.copy(g.binary('&', state.guard, value, BOOL))
        no = state.copy(g.binary('&', state.guard, g.unary('!', value, BOOL), BOOL))
        return [yes] if g.constant(yes.guard) != 0 else [], [no] if g.constant(no.guard) != 0 else []

    def loop(self, node, state):
        parts, kind = cf.children(node), node['kind']
        init, increment = None, None
        if kind == 'WhileStmt' and len(parts) == 2: condition, body = parts
        elif kind == 'DoStmt' and len(parts) == 2: body, condition = parts
        elif kind == 'ForStmt' and len(parts) == 5 and not parts[1]:
            init, _, condition, increment, body = parts
            init = init if init else None
            condition = condition if condition else None
            increment = increment if increment else None
        else: raise Unsupported('loop AST shape')
        active = self.statement(init, state) if init else [state]
        context = {'break': [], 'continue': []}
        self.loops.append(context)
        exits = context['break']
        try:
            for iteration in range(LOOP_LIMIT + 1):
                entered = []
                for current in active:
                    yes, no = ([current], []) if kind == 'DoStmt' and iteration == 0 else self.split(current, condition)
                    entered.extend(yes); exits.extend(no)
                if iteration == LOOP_LIMIT:
                    self.truncated.extend(current.guard for current in entered)
                    self.path_budget([])
                    break
                active = [next_state for current in entered for next_state in self.statement(body, current)]
                active.extend(context['continue']); context['continue'].clear()
                if increment:
                    active = [next_state for current in active for next_state in self.statement(increment, current)]
                self.path_budget(active)
                if not active: break
            return exits
        finally:
            self.loops.pop()

    def path_budget(self, active):
        count = len(active) + len(self.returns) + len(self.gotos) + len(self.truncated)
        count += sum(len(states) for context in self.loops for states in context.values())
        if count > 64: raise Unsupported('C path budget')

    def sequence(self, statements, states):
        for statement in statements:
            if not states: break
            states = [next_state for state in states for next_state in self.statement(statement, state)]
            self.path_budget(states)
        return states

    def model(self):
        bodies = [n for n in cf.children(self.root) if n.get('kind') == 'CompoundStmt']
        if len(bodies) != 1: raise Unsupported('function body shape')
        memory = [self.graph.extract(self.graph.inputs[n // 8], n % 8 * 8) for n in range(32)]
        locals={}
        if not self.source:
            locals[self.parameters[self.parameter]['id']]=self.graph.const(4224)
            for parameter,value in zip(self.parameters[-2:],[4096,512]): locals[parameter['id']]=self.graph.const(value)
        active = self.statement(bodies[0], State(self.graph.const(1, BOOL), locals, memory))
        while self.gotos:
            target, state = self.gotos.pop()
            index = self.labels[target]
            continuation = chain(cf.children(self.statements[index]), islice(self.statements, index + 1, None))
            active.extend(self.sequence(continuation, [state]))
        if active: raise Unsupported('function may fall through')
        incomplete = self.graph.const(0, BOOL)
        for guard in self.truncated: incomplete = self.graph.binary('|', incomplete, guard, BOOL)
        if not self.returns and not self.truncated: raise Unsupported('function lacks a return')
        outputs = [self.graph.const(0)] * 5
        for guard, values in reversed(self.returns):
            outputs = [self.graph.choose(guard, a, b) for a, b in zip(values, outputs)]
        return Model(outputs, len(self.returns), self.assignments, len(self.declarations), incomplete)


def observe(graph, text, name, parameter=0, source=True):
    try: return Interpreter(graph, text, name, parameter, source).model()
    except (cf.Unsupported, IndexError, KeyError, RecursionError) as error:
        raise Unsupported('C AST profile: ' + str(error)) from error
