"""Versioned C AST syntax observations, independent of topology/equivalence.

Clang 18 JSON is an evaluation input. Counts describe the selected function's
syntax, including its local address adapters. They are not dynamic effect
counts or semantic distances. Condition fingerprints preserve local binding
identity but do not identify the value held by a mutable local at each use.
"""
from collections import Counter
import hashlib
import json
import re

METRIC = 'nirvana-c-ast-footprint-v1'
MAX_BYTES = 16 * 1024 * 1024
MAX_NODES = 100_000
MAX_DEPTH = 128
WRAPPERS = {'ImplicitCastExpr', 'ParenExpr', 'ConstantExpr'}
KINDS = set('''FunctionDecl ParmVarDecl VarDecl RecordDecl FieldDecl TypedefDecl
CompoundStmt DeclStmt IfStmt ForStmt WhileStmt DoStmt SwitchStmt CaseStmt DefaultStmt
BreakStmt ContinueStmt ReturnStmt LabelStmt GotoStmt NullStmt AttributedStmt
ParenExpr ImplicitCastExpr CStyleCastExpr BinaryOperator CompoundAssignOperator
UnaryOperator ConditionalOperator BinaryConditionalOperator CallExpr ArraySubscriptExpr
MemberExpr DeclRefExpr IntegerLiteral CharacterLiteral StringLiteral FloatingLiteral
InitListExpr ImplicitValueInitExpr CompoundLiteralExpr UnaryExprOrTypeTraitExpr ConstantExpr GenericSelectionExpr
BuiltinType PointerType RecordType TypedefType ElaboratedType ConstantArrayType
EnumDecl EnumConstantDecl EnumType'''.split())
HELPERS = {'nirvana_load': 'checked_read', 'nirvana_view_load': 'checked_read',
           'nirvana_store': 'checked_write', 'nirvana_view_store': 'checked_write',
           'nirvana_test_read_offset': 'check_read', 'nirvana_offset': 'check_write'}


class Unsupported(ValueError):
    pass


def children(node):
    result = node.get('inner', [])
    if not isinstance(result, list) or not all(isinstance(n, dict) for n in result):
        raise Unsupported('AST child shape')
    if 'array_filler' in node:
        filler = node['array_filler']
        if not isinstance(filler, list) or not all(isinstance(n, dict) for n in filler):
            raise Unsupported('AST array filler shape')
        result = [*result, *filler]
    return result


def function(text, name):
    if len(text.encode()) > MAX_BYTES:
        raise Unsupported('AST byte budget')
    decoder = json.JSONDecoder()
    cursor, definitions, visited = 0, [], 0
    # -ast-dump-filter uses substring matching and can emit several JSON roots.
    # Read every root, selecting exactly one definition of the exact name.
    while cursor < len(text):
        while cursor < len(text) and text[cursor].isspace():
            cursor += 1
        if cursor == len(text):
            break
        try:
            root, cursor = decoder.raw_decode(text, cursor)
        except (ValueError, RecursionError) as error:
            raise Unsupported('invalid AST JSON') from error
        pending = [root]
        while pending:
            node = pending.pop()
            visited += 1
            if visited > MAX_NODES or not isinstance(node, dict):
                raise Unsupported('AST root budget or shape')
            if (node.get('kind') == 'FunctionDecl' and node.get('name') == name
                    and any(n.get('kind') == 'CompoundStmt' for n in children(node))):
                definitions.append(node)
            else:
                pending.extend(children(node))
    if len(definitions) != 1:
        raise Unsupported('require exactly one named C function definition')
    return definitions[0]


def type_key(node):
    value = node.get('type', {})
    text = value.get('desugaredQualType', value.get('qualType', ''))
    # Anonymous record spellings embed source filenames and positions.
    return re.sub(r'\((?:unnamed|anonymous)[^)]*\)', '<anonymous>', text)


def strip(node):
    while node.get('kind') in WRAPPERS or node.get('kind') == 'GenericSelectionExpr':
        parts = children(node)
        if node.get('kind') == 'GenericSelectionExpr':
            selected = [p for p in parts if p.get('selected') is True]
            if len(selected) != 1 or not children(selected[0]):
                raise Unsupported('AST generic selection')
            node = children(selected[0])[-1]
            continue
        if len(parts) != 1:
            raise Unsupported('AST expression wrapper shape')
        node = parts[0]
    return node


def memory_form(node):
    node = strip(node)
    return {'ArraySubscriptExpr': 'array', 'MemberExpr': 'member'}.get(node.get('kind'),
            'pointer' if node.get('kind') == 'UnaryOperator' and node.get('opcode') == '*' else None)


def measure(text, name):
    root = function(text, name)
    binders, labels = {}, {}
    pending = [(root, 0)]
    count = 0
    while pending:
        node, depth = pending.pop()
        count += 1
        if count > MAX_NODES or depth > MAX_DEPTH:
            raise Unsupported('AST node/depth budget')
        kind = node.get('kind')
        if kind is not None and kind not in KINDS:
            raise Unsupported('AST kind outside footprint profile: ' + kind)
        # N1570 6.5.3.4: sizeof a VLA can evaluate its bound/operand. Clang's
        # function JSON also omits some declaration-bound expressions. Keep
        # variably modified types outside this syntax-counting profile.
        for typename in [type_key(node), type_key({'type': node.get('argType', {})})]:
            if any(not re.fullmatch(r'[0-9]+', bound.strip()) for bound in re.findall(r'\[([^]]*)\]', typename)):
                raise Unsupported('array extent outside fixed-size footprint profile')
        if kind in ['ParmVarDecl', 'VarDecl']:
            identity = node.get('id')
            if not isinstance(identity, str) or identity in binders:
                raise Unsupported('AST local declaration identity')
            binders[identity] = len(binders)
        if kind == 'LabelStmt':
            identity = node.get('declId')
            if not isinstance(identity, str) or identity in labels:
                raise Unsupported('AST label declaration identity')
            labels[identity] = len(labels)
        pending.extend((child, depth + 1) for child in reversed(children(node)))

    operations, literals, accesses, calls, types, unevaluated = (Counter() for _ in range(6))
    conditions = []
    conditional_kinds = Counter()
    expression_nodes = 0

    def visit(node, depth=0, evaluated=True):
        nonlocal expression_nodes
        kind = node.get('kind', 'Missing')
        parts = children(node)
        flags = [evaluated] * len(parts)
        if kind == 'UnaryExprOrTypeTraitExpr':
            flags = [False] * len(parts)
        if kind == 'GenericSelectionExpr':
            if sum(p.get('selected') is True for p in parts) != 1:
                raise Unsupported('AST generic selection')
            flags = [evaluated and p.get('selected') is True for p in parts]
        descendants = [visit(child, depth + 1, flag) for child, flag in zip(parts, flags)]
        label = {'kind': kind}
        if 'associationKind' in node:
            label.update(association=node['associationKind'], selected=bool(node.get('selected')))
        typename = type_key(node)
        if typename:
            label['type'] = typename
            types[typename] += 1
        is_expression = (kind.endswith(('Expr', 'Operator', 'Literal'))
                         and kind not in WRAPPERS and kind not in ['ImplicitValueInitExpr', 'GenericSelectionExpr'])
        is_expression = is_expression and evaluated
        cost = int(is_expression) + sum(size for _, size in descendants)
        expression_nodes += int(is_expression)
        if kind in ['BinaryOperator', 'CompoundAssignOperator', 'UnaryOperator']:
            opcode = node.get('opcode')
            if not isinstance(opcode, str):
                raise Unsupported('AST operator opcode')
            form = ('post' if node.get('isPostfix') else 'pre') if kind == 'UnaryOperator' else kind
            (operations if evaluated else unevaluated)[form + ':' + opcode] += 1
            label.update(opcode=opcode, postfix=bool(node.get('isPostfix')))
            if opcode == '=' or kind == 'CompoundAssignOperator':
                if len(parts) != 2:
                    raise Unsupported('AST assignment arity')
                where = memory_form(parts[0])
                if where and evaluated:
                    accesses[where + '_assignment_syntax'] += 1
        if kind in ['ImplicitCastExpr', 'CStyleCastExpr']:
            label['cast'] = node.get('castKind')
            if node.get('castKind') == 'LValueToRValue' and parts and evaluated:
                where = memory_form(parts[0])
                if where:
                    accesses[where + '_read_syntax'] += 1
        if kind in ['ArraySubscriptExpr', 'MemberExpr'] and evaluated:
            accesses[kind] += 1
        if kind.endswith('Literal'):
            value = node.get('value')
            if value is None:
                raise Unsupported('AST literal value')
            label['value'] = value
            literals[json.dumps([kind, typename, value], separators=(',', ':'))] += 1
        if kind in ['ParmVarDecl', 'VarDecl']:
            label['binding'] = binders[node['id']]
        if kind == 'DeclRefExpr':
            ref = node.get('referencedDecl', {})
            if ref.get('id') in binders:
                label['binding'] = binders[ref['id']]
            else:
                if not isinstance(ref.get('name'), str):
                    raise Unsupported('AST external declaration reference')
                label['external'] = [ref.get('kind'), ref['name']]
        if kind == 'MemberExpr':
            label.update(member=node.get('name'), arrow=bool(node.get('isArrow')))
        if kind == 'LabelStmt':
            label['label'] = labels[node['declId']]
        if kind == 'GotoStmt':
            identity = node.get('targetLabelDeclId')
            if identity not in labels:
                raise Unsupported('AST goto outside named function')
            label['label'] = labels[identity]
        if kind == 'UnaryExprOrTypeTraitExpr':
            label.update(trait=node.get('name'), argument_type=type_key({'type': node.get('argType', {})}))
        if kind == 'CallExpr':
            if not parts:
                raise Unsupported('AST empty call')
            callee = strip(parts[0])
            ref = callee.get('referencedDecl', {})
            target = ref.get('name') if ref.get('kind') == 'FunctionDecl' else '<indirect>'
            if not isinstance(target, str):
                raise Unsupported('AST callee identity')
            (calls if evaluated else unevaluated)['call:' + target if not evaluated else target] += 1
            if target in HELPERS and evaluated:
                accesses[HELPERS[target] + '_helper_sites'] += 1
        condition = None
        if kind in ['IfStmt', 'WhileStmt', 'SwitchStmt', 'ConditionalOperator']:
            arities = {'IfStmt': [2, 3], 'WhileStmt': [2], 'SwitchStmt': [2], 'ConditionalOperator': [3]}
            if node.get('hasInit') or node.get('hasVar') or len(parts) not in arities[kind]:
                raise Unsupported('AST conditional form')
            condition = 0
        elif kind == 'DoStmt':
            if len(parts) != 2:
                raise Unsupported('AST do form')
            condition = 1
        elif kind == 'ForStmt':
            if len(parts) != 5:
                raise Unsupported('AST for form')
            if parts[2]:
                condition = 2
        elif kind == 'BinaryConditionalOperator':
            raise Unsupported('GNU binary conditional outside C11 profile')
        if condition is not None and evaluated:
            fingerprint, size = descendants[condition]
            conditional_kinds[kind] += 1
            conditions.append({'kind': kind, 'fingerprint': fingerprint, 'expression_nodes': size})
        fingerprint = hashlib.sha256(json.dumps([label, [h for h, _ in descendants]],
                                                 sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        return fingerprint, cost

    fingerprint, _ = visit(root)
    repeated = Counter(c['fingerprint'] for c in conditions)
    return {'metric': METRIC, 'status': 'measured', 'function_fingerprint': fingerprint,
            'ast_nodes': count, 'expression_nodes': expression_nodes,
            'operations': dict(sorted(operations.items())), 'literals': dict(sorted(literals.items())),
            'unevaluated_syntax': dict(sorted(unevaluated.items())),
            'access_syntax': dict(sorted(accesses.items())), 'calls': dict(sorted(calls.items())),
            'types': dict(sorted(types.items())), 'conditions': conditions,
            'condition_kinds': dict(sorted(conditional_kinds.items())),
            'condition_expression_nodes': sum(c['expression_nodes'] for c in conditions),
            'max_condition_expression_nodes': max((c['expression_nodes'] for c in conditions), default=0),
            'repeated_condition_syntax': sum(n - 1 for n in repeated.values())}


def delta(before, after):
    """Signed syntax counts; no scalar quality score or semantic distance."""
    if before.get('metric') != METRIC or after.get('metric') != METRIC:
        raise Unsupported('C footprint metric mismatch')
    result = {key: after[key] - before[key] for key in ['expression_nodes', 'condition_expression_nodes',
              'max_condition_expression_nodes', 'repeated_condition_syntax']}
    for key in ['operations', 'unevaluated_syntax', 'literals', 'access_syntax', 'calls', 'types']:
        a, b = before[key], after[key]
        result[key] = {name: b.get(name, 0) - a.get(name, 0) for name in sorted(a.keys() | b.keys())
                       if b.get(name, 0) != a.get(name, 0)}
    return result
