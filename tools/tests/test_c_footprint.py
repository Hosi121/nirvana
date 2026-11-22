"""C content controls include topology-invisible changes and local alpha names."""
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import c_footprint as cf


def ast(value='1', *, name='x', identity='0xa'):
    return {'kind': 'FunctionDecl', 'name': 'fixture', 'inner': [
        {'kind': 'ParmVarDecl', 'id': identity, 'name': name, 'type': {'qualType': 'unsigned int'}},
        {'kind': 'CompoundStmt', 'inner': [{'kind': 'ReturnStmt', 'inner': [
            {'kind': 'BinaryOperator', 'opcode': '+', 'type': {'qualType': 'unsigned int'}, 'inner': [
                {'kind': 'DeclRefExpr', 'type': {'qualType': 'unsigned int'}, 'referencedDecl': {
                    'kind': 'ParmVarDecl', 'id': identity, 'name': name}},
                {'kind': 'IntegerLiteral', 'value': value, 'type': {'qualType': 'int'}}]}]}]}]}


class FootprintTests(unittest.TestCase):
    def test_local_names_positions_and_ast_pointers_are_not_content(self):
        a, b = ast(), ast(name='long_parameter', identity='0xffff')
        b['loc'] = {'offset': 912, 'file': '/different/path.c'}
        self.assertEqual(cf.measure(json.dumps(a), 'fixture'), cf.measure(json.dumps(b), 'fixture'))

    def test_literal_change_is_visible_with_the_same_return_topology(self):
        a, b = (cf.measure(json.dumps(ast(n)), 'fixture') for n in ['1', '2'])
        self.assertEqual(a['operations'], b['operations'])
        self.assertNotEqual(a['function_fingerprint'], b['function_fingerprint'])
        self.assertEqual(sum(abs(n) for n in cf.delta(a, b)['literals'].values()), 2)

    def test_filter_substrings_prototypes_and_helper_bodies_are_separate(self):
        prototype = {'kind': 'FunctionDecl', 'name': 'fixture'}
        helper = ast('99'); helper['name'] = 'fixture_helper'
        baseline = cf.measure(json.dumps(ast()), 'fixture')
        stream = '\n'.join(map(json.dumps, [prototype, helper, ast()]))
        self.assertEqual(cf.measure(stream, 'fixture'), baseline)
        for stream in [json.dumps(prototype), json.dumps(ast()) + json.dumps(ast()), '{bad}']:
            with self.assertRaises(cf.Unsupported): cf.measure(stream, 'fixture')

    def test_unknown_nodes_missing_literals_and_budgets_remain_unsupported(self):
        for variant in ['node', 'literal', 'depth', 'reference']:
            value = ast()
            expr = value['inner'][1]['inner'][0]['inner'][0]
            if variant == 'node': expr['kind'] = 'AtomicExpr'
            elif variant == 'literal': del expr['inner'][1]['value']
            elif variant == 'reference': del expr['inner'][0]['referencedDecl']['name'];expr['inner'][0]['referencedDecl']['id'] = 'unknown'
            else:
                for _ in range(cf.MAX_DEPTH + 1): expr = {'kind': 'ParenExpr', 'inner': [expr]}
                value['inner'][1]['inner'][0]['inner'][0] = expr
            with self.subTest(variant=variant), self.assertRaises(cf.Unsupported):
                cf.measure(json.dumps(value), 'fixture')


class ClangFootprints(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.clang = shutil.which(os.environ.get('NIRVANA_CLANG', 'clang'))
        if not cls.clang: raise unittest.SkipTest('requires Clang 18; set NIRVANA_CLANG')

    def measure(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input.c'; path.write_text(source)
            result = subprocess.run([self.clang, '-std=c11', '-fsyntax-only', '-Xclang', '-ast-dump=json',
                                     '-Xclang', '-ast-dump-filter=fixture', path], capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            return cf.measure(result.stdout, 'fixture')

    def test_alpha_names_shadowing_labels_and_input_paths(self):
        source = 'unsigned fixture(unsigned x) { unsigned y=x; {unsigned x=2; if(x) y++;} if(y) goto done; done: return x+y; }'
        changed = 'unsigned fixture(unsigned alpha) { unsigned beta=alpha; {unsigned gamma=2; if(gamma) beta++;} if(beta) goto exit_label; exit_label: return alpha+beta; }'
        self.assertEqual(self.measure(source), self.measure(changed))

    def test_pure_work_and_condition_expansion_have_separate_counts(self):
        a = self.measure('unsigned fixture(unsigned x) { unsigned a=x+1; return a+a; }')
        b = self.measure('unsigned fixture(unsigned x) { unsigned a=x+1; unsigned b=x+1; return a+b; }')
        self.assertEqual(cf.delta(a, b)['operations']['BinaryOperator:+'], 1)
        a = self.measure('unsigned fixture(unsigned x) { if(x) return 1; return 0; }')
        b = self.measure('unsigned fixture(unsigned x) { if((x+1)*(x+2)) return 1; return 0; }')
        self.assertEqual(a['condition_kinds'], b['condition_kinds'])
        self.assertGreater(b['condition_expression_nodes'], a['condition_expression_nodes'])

    def test_memory_accesses_and_calls_keep_their_categories(self):
        a = self.measure('unsigned fixture(unsigned*p) { if(p[0]) p[1]=7; else p[1]=7; return p[1]; }')
        self.assertEqual(a['access_syntax']['array_assignment_syntax'], 2)
        b = self.measure('unsigned read(unsigned*p); unsigned fixture(unsigned*p) { return read(p); }')
        self.assertEqual(b['calls'], {'read': 1})
        self.assertNotIn('checked_read_helper_sites', b['access_syntax'])
        p = self.measure('unsigned read(unsigned*); unsigned fixture(unsigned*p) { return sizeof(read(p)); }')
        self.assertEqual(p['calls'], {})
        self.assertEqual(p['unevaluated_syntax']['call:read'], 1)

    def test_c11_generic_selection_uses_only_the_selected_callee(self):
        p = self.measure('''unsigned a(unsigned); unsigned b(unsigned);
unsigned fixture(unsigned x) { return _Generic((x+1), unsigned:a,default:b)(x); }''')
        self.assertEqual(p['calls'], {'a': 1})
        self.assertEqual(p['operations'], {})
        self.assertEqual(p['unevaluated_syntax']['BinaryOperator:+'], 1)

    def test_control_forms_and_macro_spelling_keep_every_explicit_condition(self):
        p = self.measure('''#define LIMIT 3
unsigned fixture(unsigned x) { for(unsigned i=0;i<LIMIT;i++) { if(x) break; }
while(x>4) x--; do {x++;} while(x<2); switch(x) {case 1:return 2;default:return x?3:4;} }''')
        self.assertEqual(p['condition_kinds'], {'ConditionalOperator': 1, 'DoStmt': 1, 'ForStmt': 1,
                                             'IfStmt': 1, 'SwitchStmt': 1, 'WhileStmt': 1})


if __name__ == '__main__': unittest.main()
