"""Run with python3 -m unittest discover -s tools/tests -v (no Cargo hook)."""
import copy
import contextlib
import io
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import struct
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('source_recovery', Path(__file__).resolve().parents[1] / 'measure_source_recovery.py')
TOOL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TOOL)


def info(variables=(('first', -24),), producer='GNU C11 13.3.0 -g -O0', extra=''):
    rows = ['Contents of the .debug_info section:', 'Compilation Unit @ offset 0:',
            ' Version: 5', ' Unit Type: DW_UT_compile (1)',
            ' <0><c>: Abbrev Number: 1 (DW_TAG_compile_unit)',
            ' <d> DW_AT_producer : (string) ' + producer,
            ' <1><20>: Abbrev Number: 2 (DW_TAG_subprogram)',
            ' <21> DW_AT_name : (string) fixture',
            ' <22> DW_AT_low_pc : (addr) 0', ' <23> DW_AT_high_pc : (data8) 0x10',
            ' <24> DW_AT_frame_base : (exprloc) 1 byte block: 9c (DW_OP_call_frame_cfa)']
    for index, (name, offset) in enumerate(variables):
        die = 0x30 + index * 0x10
        rows += [f' <2><{die:x}>: Abbrev Number: 3 (DW_TAG_variable)',
                 f' <{die+1:x}> DW_AT_name : (string) {name}',
                 f' <{die+2:x}> DW_AT_type : (ref4) <0x90>',
                 f' <{die+3:x}> DW_AT_location : (exprloc) 2 byte block: 91 68 (DW_OP_fbreg: {offset})']
    rows += [' <2><80>: Abbrev Number: 0', ' <1><90>: Abbrev Number: 4 (DW_TAG_base_type)',
             ' <91> DW_AT_name : (string) long unsigned int', ' <92> DW_AT_byte_size : (data1) 8',
             ' <93> DW_AT_encoding : (data1) 7 (unsigned)', extra]
    return '\n'.join(rows)


FUNCTION = dict(function_start=0, function_size=16)
CFA = dict(span=[0, 16], rows=[dict(pc=0, register='rsp', offset=8), dict(pc=4, register='rbp', offset=16)])
FRAME = 'FORMAT\tnirvana-stack-frame-v1\nPOINT\t0\t0\t?\nPOINT\t4\t-8\t-8\n'


def variables(raw=None):
    result, _ = TOOL.parse_variables(raw or info(), FUNCTION)
    for var in result:
        var['source_id'] = 'source-hash:' + str(var['die'])
    TOOL.verify_frame(copy.deepcopy(CFA), FRAME, result)
    return result


def row(register, local, offset=None, web=None, basis=None):
    return dict(register=register, local=local, offset=offset, width=8 if offset is not None else None,
                web=web, basis=basis or ('store-web' if web is not None else '-'))


class ParserTests(unittest.TestCase):
    def test_simple_frame_relative_variable(self):
        var = variables()[0]
        self.assertEqual(var['entry_rsp_offset'], -16)
        self.assertTrue(var['integer_local_eligible'])

    def test_optimized_or_foreign_producer_rejected(self):
        for producer in ['GNU C11 13.3.0 -O2 -g', 'GNU C11 13.3.0 -O0 -O2 -g', 'clang -O0 -g', 'GNU C++17 13.3.0 -O0 -g']:
            with self.subTest(producer=producer), self.assertRaises(ValueError):
                TOOL.parse_variables(info(producer=producer), FUNCTION)

    def test_single_cu_and_no_external_debug(self):
        for changed in [info().replace('Version: 5', 'Version: 4'), info() + '\nCompilation Unit @ offset 1:',
                        info() + '\n DW_AT_GNU_dwo_name : external.dwo']:
            with self.assertRaises(ValueError):
                TOOL.parse_variables(changed, FUNCTION)

    def test_pieces_registers_and_stack_values_are_not_guessed(self):
        for operation in ['DW_OP_fbreg: -24; DW_OP_piece: 8', 'DW_OP_reg0 (rax)',
                          'DW_OP_fbreg: -24; DW_OP_stack_value']:
            changed = info().replace('DW_OP_fbreg: -24', operation)
            parsed, _ = TOOL.parse_variables(changed, FUNCTION)
            self.assertEqual(parsed[0]['status'], 'unsupported')

    def test_unmodeled_indexed_pc_form_rejected(self):
        with self.assertRaises(ValueError):
            TOOL.parse_variables(info().replace('DW_AT_low_pc : (addr)', 'DW_AT_low_pc : (addrx)'), FUNCTION)

    def test_duplicate_die_and_bad_text_rejected(self):
        for changed in [info().replace('<1><90>', '<1><20>'), info().replace('DW_AT_name :', 'DW_AT_name broken')]:
            with self.assertRaises(ValueError):
                TOOL.parse_variables(changed, FUNCTION)

    def test_wrong_cfa_and_missing_row_proofs_rejected(self):
        altered = copy.deepcopy(CFA)
        altered['rows'][1]['offset'] = 17
        with self.assertRaises(ValueError):
            TOOL.verify_frame(altered, FRAME, [])
        with self.assertRaises(ValueError):
            TOOL.verify_frame(copy.deepcopy(CFA), FRAME.replace('POINT\t4', 'POINT\t5'), [])

    def test_unknown_rsp_and_protocol_rejected(self):
        for frame in [FRAME.replace('POINT\t4\t-8', 'POINT\t4\t?'), FRAME.replace('nirvana-stack-frame-v1', 'other')]:
            with self.assertRaises(ValueError):
                TOOL.verify_frame(copy.deepcopy(CFA), frame, [])

    def test_reused_cells_rejected_even_with_disjoint_scopes(self):
        parsed, _ = TOOL.parse_variables(info((('one', -24), ('two', -24))), FUNCTION)
        parsed[0]['scope_pc'], parsed[1]['scope_pc'] = [0, 4], [4, 16]
        TOOL.verify_frame(copy.deepcopy(CFA), FRAME, parsed)
        self.assertTrue(all(v['overlapping_source_dies'] for v in parsed))
        self.assertTrue(all(not v['integer_local_eligible'] for v in parsed))

    def test_unsupported_extent_blocks_positive_and_unresolved_bounds_block_all(self):
        for extent in [dict(fbreg=-24, size=8), None]:
            parsed, _ = TOOL.parse_variables(info(), FUNCTION)
            opaque = dict(die=999, kind='variable', name='opaque', status='unsupported')
            if extent:
                opaque['opaque_source_extent'] = extent
            parsed.append(opaque)
            TOOL.verify_frame(copy.deepcopy(CFA), FRAME, parsed)
            self.assertFalse(parsed[0]['integer_local_eligible'])

    def test_source_spelling_is_not_identity(self):
        source = variables(info((('same', -24), ('same', -40))))
        measured = TOOL.measure([row(1, 'v', -16, 0), row(2, 'v', -32, 1)], source)
        self.assertEqual(len(measured['mixed_locals']), 1)
        self.assertEqual(measured['observed_integer_source_objects'], 2)

    def test_unknown_is_not_another_source_identity(self):
        source = variables()
        measured = TOOL.measure([row(1, 'v', -16, 0), row(2, 'v')], source)
        self.assertEqual(measured['mixed_locals'], [])
        self.assertEqual(measured['classifications']['missing_association'], 1)

    def test_wrapped_offsets_and_overlap(self):
        self.assertEqual(TOOL.signed_offset((1 << 63) + 2), -(1 << 63) + 2)
        self.assertTrue(TOOL.overlap(-2, 8, 3, 1))
        self.assertFalse(TOOL.overlap(-8, 8, 0, 8))


class MetadataTests(unittest.TestCase):
    def parse(self, rows, basis=False):
        header = '\t'.join(TOOL.COLUMNS + (['basis'] if basis else []))
        return TOOL.parse_metadata(header + '\n' + rows, Path.cwd())

    def test_seven_columns_and_optional_load_cell_basis(self):
        old = self.parse('input.o\tv\t1\t0\t-16\t8\t-\n')
        self.assertEqual(next(iter(old.values()))[0]['basis'], 'store-web')
        new = self.parse('input.o\tv\t1\t-\t-16\t8\t-\tload-cell\n', basis=True)
        self.assertEqual(next(iter(new.values()))[0]['basis'], 'load-cell')

    def test_escaped_literal_backslash_is_consumed_once(self):
        encoded = 'folder' + '\\\\' + 'name.o'
        parsed = self.parse(encoded + '\tv\t1\t0\t-16\t8\t-\n')
        self.assertEqual(next(iter(parsed)), str((Path.cwd() / ('folder' + '\\' + 'name.o')).resolve()))
        with self.assertRaises(ValueError):
            TOOL.unescape('bad' + '\\' + 'q')

    def test_malformed_or_duplicate_metadata_rejected(self):
        rows = ['input.o\tv\t1\t-\t-16\t8\t-\n',
                'input.o\tv\t1\t0\t-16\t3\t-\n',
                'input.o\tv\t-1\t-\t-\t-\t-\n',
                'input.o\tv\t1\t0\t-16\t8\t-\n' * 2]
        for data in rows:
            with self.subTest(data=data), self.assertRaises(ValueError):
                self.parse(data)
        with self.assertRaises(ValueError):
            self.parse('input.o\tv\t1\t-\t-16\t8\t-\tguess\n', basis=True)

    def test_common_and_expanded_coverage_are_separate(self):
        source = variables(info((('one', -24), ('two', -40))))
        before = [row(1, 'old', -16, 0), row(2, 'old')]
        after = [row(1, 'new', -16, 0), row(2, 'new', -32, basis='load-cell')]
        result = TOOL.compare_metadata(before, after, source)
        self.assertEqual(result['common']['registers'], [1])
        self.assertEqual(result['expanded_coverage']['registers'], [2])
        self.assertEqual(result['common']['after']['integer_associated_registers'], 1)
        self.assertEqual(result['expanded_coverage']['after']['integer_associated_registers'], 1)
        self.assertEqual(len(result['full']['after']['mixed_locals']), 1)
        self.assertEqual(result['common']['after']['mixed_locals'], [])
        self.assertFalse(any(result['common']['regressions'].values()))

    def test_common_regressions_do_not_mix_in_new_coverage(self):
        source = variables()
        before = [row(1, 'one', -16, 0), row(2, 'one', -16, 0)]
        after = [row(1, 'one', -16, 0), row(2, 'two', -16, 0)]
        result = TOOL.compare_metadata(before, after, source)
        self.assertEqual(len(result['common']['regressions']['increased_fragmentation']), 1)
        self.assertEqual(result['expanded_coverage']['registers'], [])

    def test_changed_basis_is_not_counted_as_unchanged_common_evidence(self):
        result = TOOL.compare_metadata([row(1, 'v', -16, 0)], [row(1, 'v', -16, basis='load-cell')], variables())
        self.assertEqual(result['common']['registers'], [])
        self.assertEqual(result['changed_association_registers'], [1])
        self.assertEqual(result['expanded_coverage']['registers'], [])

    def test_debug_and_output_flags_rejected(self):
        for flags in [['-O2'], ['-O0', '-g'], ['-O0', '-o', 'somewhere'], ['-O0', '-MMD']]:
            with self.assertRaises(ValueError):
                TOOL.validate_flags(flags)

    def test_machine_mismatch_is_a_fatal_kind(self):
        a = dict(text_bytes=b'a', function_bytes=b'a', function_start=0, function_size=1)
        with self.assertRaises(TOOL.InputMismatch):
            TOOL.compare_machine_bytes(dict(existing=a, debug=dict(a, text_bytes=b'b')))


class NativeToolsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not shutil.which('cc') or not shutil.which('readelf'):
            raise unittest.SkipTest('cc and GNU readelf are optional evaluation dependencies')
        if not subprocess.run(['readelf', '--version'], text=True, capture_output=True).stdout.startswith('GNU readelf'):
            raise unittest.SkipTest('GNU readelf required')
        retain = os.environ.get('NIRVANA_SOURCE_TEST_ARTIFACTS')
        if retain:
            Path(retain).mkdir(parents=True, exist_ok=True)
            cls.root = Path(tempfile.mkdtemp(prefix='source-recovery-', dir=retain)).resolve()
        else:
            temporary = tempfile.TemporaryDirectory(prefix='source-recovery-')
            cls.addClassCleanup(temporary.cleanup)
            cls.root = Path(temporary.name)
        cls.runner = TOOL.Runner(cls.root)
        cls.source = cls.root / 'input.c'
        cls.source.write_text('#include <stdint.h>\nuint64_t fixture(uint64_t *state) { volatile uint64_t local=state[0]; return local; }\n')
        cls.plain, cls.debug = cls.root / 'input.o', cls.root / 'debug.o'
        cls.runner.run(['cc', *TOOL.DEFAULT_FLAGS, '-c', cls.source, '-o', cls.plain])
        cls.runner.run(['cc', *TOOL.DEFAULT_FLAGS, '-g', '-c', cls.source, '-o', cls.debug])
        header = cls.plain.read_bytes()
        if header[:6] != b'\x7fELF\x02\x01' or struct.unpack_from('<H', header, 18)[0] != 62:
            raise unittest.SkipTest('native x86-64 ELF target required')
        cls.raw = cls.runner.run(['readelf', '--wide', '--debug-dump=info', '--debug-dump=no-follow-links', cls.debug])
        if 'Version:       5' not in cls.raw:
            raise unittest.SkipTest('compiler with default DWARF5 debug output required')
        if not any('GNU C' in line for line in cls.raw.splitlines()):
            raise unittest.SkipTest('GNU C debug producer required')

    def test_unresolved_function_relocation_is_rejected(self):
        source = self.root / 'external.c'
        source.write_text('extern unsigned long other(unsigned long);\nunsigned long fixture(unsigned long *s) { return other(s[0]); }\n')
        obj = self.root / 'external.o'
        self.runner.run(['cc', *TOOL.DEFAULT_FLAGS, '-c', source, '-o', obj])
        with self.assertRaisesRegex(ValueError, 'relocation'):
            TOOL.read_elf(obj)

    def test_existing_nonempty_output_is_preserved(self):
        output = self.root / 'preserved'
        output.mkdir()
        (output / 'keep').write_text('existing artifact')
        with contextlib.redirect_stderr(io.StringIO()):
            result = TOOL.main(['--cases', 'missing.json', '--objects', str(self.root),
                '--frame-helper', 'unused', '--before-metadata', 'missing.tsv',
                '--after-metadata', 'missing.tsv', '--out', str(output)])
        self.assertEqual(result, 1)
        self.assertEqual((output / 'keep').read_text(), 'existing artifact')
        self.assertEqual(sorted(p.name for p in output.iterdir()), ['keep'])

    def test_real_plain_debug_bytes_and_variables(self):
        plain, debug = TOOL.read_elf(self.plain), TOOL.read_elf(self.debug)
        TOOL.compare_machine_bytes(dict(existing=plain, plain=plain, debug=debug))
        source, _ = TOOL.parse_variables(self.raw, plain)
        self.assertTrue(any(v['name'] == 'local' and v['status'] == 'pending_cfa_verification' for v in source))

    def test_existing_debug_input_is_rejected(self):
        with self.assertRaises(ValueError):
            TOOL.read_elf(self.debug, require_nondebug=True)

    def test_real_optimized_and_realigned_locations_are_rejected(self):
        optimized = self.root / 'optimized.o'
        self.runner.run(['cc', *[f for f in TOOL.DEFAULT_FLAGS if f != '-O0'], '-O2', '-g', '-c', self.source, '-o', optimized])
        raw = self.runner.run(['readelf', '--wide', '--debug-dump=info', '--debug-dump=no-follow-links', optimized])
        with self.assertRaises(ValueError):
            TOOL.parse_variables(raw, TOOL.read_elf(optimized))
        source = self.root / 'aligned.c'
        source.write_text('#include <stdint.h>\nuint64_t fixture(uint64_t *s) { _Alignas(32) volatile uint64_t cell=s[0]; return cell; }\n')
        aligned = self.root / 'aligned.o'
        self.runner.run(['cc', *TOOL.DEFAULT_FLAGS, '-g', '-c', source, '-o', aligned])
        raw = self.runner.run(['readelf', '--wide', '--debug-dump=info', '--debug-dump=no-follow-links', aligned])
        source, _ = TOOL.parse_variables(raw, TOOL.read_elf(aligned))
        self.assertTrue(all(v['status'] == 'unsupported' for v in source))

    def test_actual_changed_machine_input_is_detected(self):
        source = self.root / 'changed.c'
        source.write_text('unsigned long fixture(unsigned long *s) { return s[0]+1; }\n')
        obj = self.root / 'changed.o'
        self.runner.run(['cc', *TOOL.DEFAULT_FLAGS, '-c', source, '-o', obj])
        with self.assertRaises(TOOL.InputMismatch):
            TOOL.compare_machine_bytes(dict(existing=TOOL.read_elf(self.plain), debug=TOOL.read_elf(obj)))

    def test_optional_actual_frame_helper_cli(self):
        helper = os.environ.get('NIRVANA_FRAME_HELPER')
        if not helper:
            self.skipTest('set NIRVANA_FRAME_HELPER to the built inspect_stack_frame example')
        cases = self.root / 'cases.json'
        cases.write_text(json.dumps([dict(id='input', source='input.c')]))
        metadata = self.root / 'input.tsv'
        metadata.write_text('\t'.join(TOOL.COLUMNS) + '\n' + str(self.plain) + '\tv\t1\t-\t-\t-\t-\n')
        output = self.root / 'evaluation'
        with contextlib.redirect_stdout(io.StringIO()):
            code = TOOL.main(['--cases', str(cases), '--source-root', str(self.root), '--objects', str(self.root),
                '--frame-helper', helper, '--before-metadata', str(metadata), '--after-metadata', str(metadata), '--out', str(output)])
        self.assertEqual(code, 0)
        report = json.loads((output / 'report.json').read_text())
        self.assertEqual(report['summary']['evaluated'], 1)
        self.assertEqual(report['summary']['full']['after']['integer_associated_registers'], 0)
        with self.assertRaises(ValueError):
            self.runner.run(['readelf', '--debug-dump=definitely-not-supported', self.debug])


if __name__ == '__main__':
    unittest.main()
