"""Fixed-ABI field correspondence uses addresses, widths and binding identities."""
import os
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import c_footprint as cf, state_memory as sm, reports
from report_fixture import fixture, save

HEADER = '''#include <stdint.h>
struct nirvana_memory {uint8_t *bytes; uint64_t base,size;};
struct nirvana_view {uint64_t address;};
uint64_t nirvana_load(struct nirvana_memory*,uint64_t,unsigned);
void nirvana_store(struct nirvana_memory*,uint64_t,unsigned,uint64_t);
uint64_t nirvana_view_load(struct nirvana_memory*,struct nirvana_view,unsigned);
void nirvana_view_store(struct nirvana_memory*,struct nirvana_view,unsigned,uint64_t);
struct nirvana_view nirvana_location_view(struct nirvana_view);
struct nirvana_view nirvana_location_address(uint64_t);
struct nirvana_view nirvana_view_index(struct nirvana_view,uint64_t,uint64_t,uint64_t);
uint64_t opaque(uint64_t);
'''


class StateMemory(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.clang = shutil.which(os.environ.get('NIRVANA_CLANG', 'clang'))
        if not cls.clang: raise unittest.SkipTest('requires Clang 18; set NIRVANA_CLANG')

    def ast(self, source, name):
        result = subprocess.run([self.clang, '-std=c11', '-Werror', '-fsyntax-only', '-Xclang',
                                 '-ast-dump=json', '-Xclang', '-ast-dump-filter=' + name, '-x', 'c', '-'],
                                input=HEADER + source, text=True, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def pair(self, source, generated, parameters=None):
        a = self.ast('uint64_t fixture(uint64_t *state) {' + source + '}', 'fixture')
        args = 'uint64_t address' if parameters is None or len(parameters) == 1 else 'uint64_t extra,uint64_t address'
        b = self.ast('uint64_t nirvana_readable(' + args + ',uint8_t *memory,uint64_t base,uint64_t size) '
                     '{struct nirvana_memory m={memory,base,size};' + generated + '}', 'nirvana_readable')
        return sm.measure(a, b, 'fixture', [7] if parameters is None else parameters)

    @staticmethod
    def sites(side):
        return {(n['access'], n['byte_offset'], n['width']): n['count'] for n in side['sites']}

    def test_direct_byte_addresses_match_source_words(self):
        value = self.pair('state[2]=state[0]+1; return state[2];',
                          'nirvana_store(&m,address+16,8,nirvana_load(&m,address,8)+1);'
                          'return nirvana_load(&m,address+16,8);')
        self.assertEqual(value['status'], 'measured')
        self.assertEqual(self.sites(value['source']), self.sites(value['generated']))
        self.assertEqual(self.sites(value['source']), {('read', 0, 8): 1, ('read', 16, 8): 1, ('write', 16, 8): 1})

    def test_const_view_field_names_are_not_offsets(self):
        body = ('const struct {struct nirvana_view label;} object={{address+16}};'
                'nirvana_view_store(&m,nirvana_location_view(object.label),8,3);'
                'return nirvana_view_load(&m,nirvana_location_view(object.label),8);')
        a = self.pair('state[2]=3;return state[2];', body)
        b = self.pair('state[2]=3;return state[2];', body.replace('label', 'field_999'))
        self.assertEqual(a, b)
        self.assertEqual(self.sites(a['generated']), {('read', 16, 8): 1, ('write', 16, 8): 1})
        changed = self.pair('state[2]=3;return state[2];', body.replace('address+16', 'address+24'))
        self.assertEqual(self.sites(changed['generated']), {('read', 24, 8): 1, ('write', 24, 8): 1})

    def test_dynamic_indices_mutated_roots_and_unknown_calls_stay_partial(self):
        value = self.pair('state[state[0]&3]+=1;return state[2];', 'return nirvana_load(&m,address+base,8);')
        self.assertEqual(value['status'], 'partial')
        self.assertEqual(value['source']['unresolved_sites'], 2)
        self.assertEqual(value['generated']['unresolved'], [{'access': 'read', 'reason': 'offset', 'count': 1}])
        value = self.pair('return state[0];', 'address+=8; return nirvana_load(&m,address,8);')
        self.assertEqual(value['generated']['unresolved'], [{'access': 'read', 'reason': 'root', 'count': 1}])
        value = self.pair('const volatile uint64_t index=2;return state[index];', 'return nirvana_load(&m,address+16,8);')
        self.assertEqual(value['source']['unresolved_sites'], 1)
        value = self.pair('return opaque(state[0]);', 'return opaque(address);')
        self.assertEqual(value['source']['unclassified_calls'], {'opaque': 1})
        self.assertEqual(value['status'], 'partial')

    def test_integer_widths_preserve_wrapping_constants_and_reject_truncated_bases(self):
        value = self.pair('const uint8_t index=(uint8_t)-254;return state[index];',
                          'const uint64_t offset=UINT64_MAX+17;return nirvana_load(&m,address+offset,8);')
        self.assertEqual(self.sites(value['source']), {('read', 16, 8): 1})
        self.assertEqual(self.sites(value['generated']), {('read', 16, 8): 1})
        value = self.pair('return state[0];', 'const uint8_t low=address;return nirvana_load(&m,low,8);')
        self.assertEqual(value['generated']['resolved_sites'], 0)
        self.assertEqual(value['generated']['unresolved_sites'], 1)

    def test_shadowed_arrays_and_partial_widths_keep_their_scope(self):
        source = '{uint64_t local[4]={1,2,3,4};uint64_t *state=local;(void)state[0];}return state[2];'
        value = self.pair(source, 'return nirvana_load(&m,address+16,4);')
        self.assertEqual(value['source']['unresolved_sites'], 1)
        self.assertEqual(self.sites(value['source']), {('read', 16, 8): 1})
        self.assertEqual(self.sites(value['generated']), {('read', 16, 4): 1})
        self.assertIsNone(value['generated']['sites'][0]['state_word'])

    def test_unevaluated_generic_and_sizeof_operands_have_no_memory_sites(self):
        value = self.pair('return sizeof(state[1])+_Generic(state[0],uint64_t:state[2],default:state[3]);',
                          'return sizeof(nirvana_load(&m,address+8,8))+'
                          '_Generic(address,uint64_t:nirvana_load(&m,address+16,8),default:nirvana_load(&m,address+24,8));')
        self.assertEqual(value['status'], 'measured')
        self.assertEqual(self.sites(value['source']), {('read', 16, 8): 1})
        self.assertEqual(self.sites(value['generated']), {('read', 16, 8): 1})

    def test_compound_updates_and_argument_descriptors_preserve_their_denominators(self):
        value = self.pair('state[1]++;state[2]^=state[3];return state[0];',
                          'nirvana_store(&m,address+8,8,nirvana_load(&m,address+8,8)+1);'
                          'nirvana_store(&m,address+16,8,nirvana_load(&m,address+16,8)^nirvana_load(&m,address+24,8));'
                          'return nirvana_load(&m,address,8);', [1, 7])
        self.assertEqual(value['profile']['generated_parameter'], 1)
        self.assertEqual(self.sites(value['source']), self.sites(value['generated']))
        for parameters in [[1], [7, 7], [True], []]:
            with self.subTest(parameters=parameters), self.assertRaises(cf.Unsupported):
                self.pair('return state[0];', 'return nirvana_load(&m,address,8);', parameters)

    def test_retained_correspondence_replays_ast_addresses_and_bound_registers(self):
        source = self.ast('uint64_t fixture(uint64_t *state){return state[2];}', 'fixture')
        generated = self.ast('uint64_t nirvana_readable(uint64_t address,uint8_t *memory,uint64_t base,uint64_t size)'
                             '{struct nirvana_memory m={memory,base,size};return nirvana_load(&m,address+16,8);}', 'nirvana_readable')
        for change in ['intact', 'address', 'address_type', 'binding', 'denominator', 'coverage']:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory); report = fixture(root); row = report['rows'][0]; path = root / row['artifacts']
                profile = row['semantics']['profile']; profile.update(step_limit=4096, requested_cases=3)
                row['stage_checks'] = dict(schema='nirvana-evaluation-stages-v1', contract='nirvana-entry-full-state-v1',
                    status='passed', prefix_budgets=[0,4096],
                    execution=[dict(name='low_middle', status='passed', observations=12, witness=None),
                               dict(name='middle_predicates', status='not_applied', observations=0, witness=None)],
                    selected_c=dict(parameter_registers=[7], predicates=None, input_structure_checked=True,
                                    display_structure_checked=True, saved_value_rounds=0, fallback_goto=False),
                    low_coverage=dict(steps_started=2, syntactic_steps=3, transfers_observed=1,
                                      syntactic_transfers=2, unobserved_transfers=[[1,2]]))
                row['semantics']['prepare_stdout_sha256'] = save(path, 'semantic_prepare.stdout.txt',
                    json.dumps({**profile, 'stage_checks': copy.deepcopy(row['stage_checks'])}))
                sides = {side: {**cf.measure(raw, name), 'raw_ast_sha256': save(path, side+'_ast.stdout.txt', raw)}
                         for side, raw, name in [('source',source,'fixture'), ('generated',generated,'nirvana_readable')]}
                row['c_footprint'] = dict(metric=cf.METRIC,status='measured',**sides,
                                          source_generated_delta=cf.delta(sides['source'],sides['generated']))
                row['state_memory_sites'] = sm.measure(source,generated,'fixture',[7])
                if change == 'address': row['state_memory_sites']['generated']['sites'][0]['byte_offset'] = 24
                elif change == 'address_type': row['state_memory_sites']['generated']['sites'][0]['byte_offset'] = 16.0
                elif change == 'binding': row['stage_checks']['selected_c']['parameter_registers'] = [1]
                elif change == 'coverage': row['state_memory_sites']['generated']['unresolved_sites'] = 1
                elif change == 'denominator':
                    report['state_memory_sites'] = dict(enabled=True,metric=sm.METRIC)
                    row.pop('state_memory_sites')
                    with self.assertRaisesRegex(ValueError, 'denominator'): reports.index(report)
                    continue
                if change == 'intact':
                    self.assertEqual(reports.replay(root,row)['state_memory_sites'], 'measured')
                else:
                    with self.subTest(change=change), self.assertRaises(ValueError): reports.replay(root,row)


if __name__ == '__main__': unittest.main()
