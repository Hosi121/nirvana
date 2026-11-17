#!/usr/bin/env python3
"""Evaluate source-variable recovery using identical O0 machine inputs.

Evaluation only: GCC produces a debug copy; GNU readelf supplies DWARF5. Source
or debug files are NEVER passed to a decompiler/helper. The frame helper sees
only each existing nondebug object. Compiler DWARF and the helper's stack
analysis remain trusted; lexical scope is not a value-lifetime proof.

Cases JSON: [{"id":"sum-O0", "source":"cases/sum.c", "flags":["-O0",...]}].
Paths in cases are relative to --source-root; object defaults to ID.o under
--objects. An optional "object" overrides that relative path. Flags default to
C11/warnings/-fno-lto/-O0. TSVs use the seven measure_variables columns, with an
optional eighth "basis" column (store-web/load-cell/-). Register ID stability
across the compared display IRs is an input precondition, not proven here.

DWARF5: https://dwarfstd.org/doc/DWARF5.pdf sections 2.5.1.2, 3.3.5, 3.9, 6.4.
Run --help for command options. Exit0 means a report was produced, not that all
cases were supported. No non-stdlib Python package is required.
"""
import argparse
from collections import Counter
import csv
import hashlib
import io
import json
import math
import os
from pathlib import Path
import re
import struct
import subprocess
import sys

DEFAULT_FLAGS = ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic', '-fno-lto', '-O0']
COLUMNS = ['object', 'local', 'register', 'web', 'offset', 'width', 'role']
MOD = 1 << 64
MAX_FILE = 32 * 1024 * 1024


class InputMismatch(ValueError):
    """The debug/plain/existing input code differs; the command must fail."""


def sha256(data):
    return hashlib.sha256(data).hexdigest()


class Runner:
    def __init__(self, cwd, timeout=30):
        self.cwd = Path(cwd).resolve()
        self.timeout = timeout
        self.commands = []
        self.environment = dict(os.environ, LC_ALL='C', DEBUGINFOD_URLS='')

    def run(self, argv):
        argv = [str(a) for a in argv]
        try:
            completed = subprocess.run(argv, cwd=self.cwd, env=self.environment,
                text=True, capture_output=True, timeout=self.timeout)
        except (OSError, subprocess.TimeoutExpired) as error:
            self.commands.append(dict(argv=argv, error=str(error)))
            raise ValueError(f'command failed: {argv[0]}: {error}') from error
        self.commands.append(dict(argv=argv, cwd=str(self.cwd),
            returncode=completed.returncode, stderr=completed.stderr))
        if completed.returncode or completed.stderr:
            raise ValueError(f'command failed or wrote stderr: {argv[0]}: {completed.stderr.strip()}')
        if len(completed.stdout) > MAX_FILE:
            raise ValueError('excessive command output')
        return completed.stdout


def read_elf(path, symbol='fixture', require_nondebug=False):
    """Read ELF bytes, not DWARF. Reject extended/malformed tables and text relocations."""
    with Path(path).open('rb') as stream:
        data = stream.read(MAX_FILE + 1)
    if len(data) < 64 or len(data) > MAX_FILE or data[:6] != b'\x7fELF\x02\x01':
        raise ValueError('require bounded little-endian ELF64')
    if struct.unpack_from('<HH', data, 16) != (1, 62):
        raise ValueError('require x86-64 ET_REL')
    shoff = struct.unpack_from('<Q', data, 40)[0]
    entsize, count, names_index = struct.unpack_from('<HHH', data, 58)
    if entsize != 64 or not 0 < count <= 8192 or names_index >= count or shoff + count*64 > len(data):
        raise ValueError('unsupported section table')
    sections = [struct.unpack_from('<IIQQQQIIQQ', data, shoff+i*64) for i in range(count)]
    def contents(section):
        offset, size = section[4:6]
        if offset + size > len(data):
            raise ValueError('section outside file')
        return data[offset:offset+size]
    strings = contents(sections[names_index])
    def string(table, offset):
        if offset >= len(table):
            raise ValueError('string offset out of range')
        end = table.find(b'\0', offset)
        if end < 0:
            raise ValueError('unterminated string')
        return table[offset:end].decode('utf-8')
    names = [string(strings, s[0]) for s in sections]
    if any(n in names for n in ['.gnu_debuglink','.gnu_debugaltlink','.debug_sup']):
        raise ValueError('external debug information unsupported')
    if require_nondebug and any(n.startswith(('.debug', '.zdebug', '.stab')) or n == '.gnu_debugdata' for n in names):
        raise ValueError('existing input must be nondebug; never pass debug copies to helpers')
    text_ids = [i for i,n in enumerate(names) if n == '.text']
    if len(text_ids) != 1:
        raise ValueError('require unique .text section')
    text_id = text_ids[0]
    text = contents(sections[text_id])
    functions = []
    for section in sections:
        if section[1] != 2:
            continue
        if section[6] >= count or section[9] != 24 or section[5] % 24:
            raise ValueError('unsupported symbol table')
        table = contents(section)
        labels = contents(sections[section[6]])
        for position in range(0,len(table),24):
            label, info, _, index, value, size = struct.unpack_from('<IBBHQQ',table,position)
            if label and string(labels,label)==symbol and info & 15 == 2:
                functions.append((index,value,size))
    if len(functions)!=1 or functions[0][0]!=text_id or not functions[0][2]:
        raise ValueError('require one sized requested function in .text')
    _, start, size = functions[0]
    if start + size > len(text):
        raise ValueError('invalid function span')
    for section in sections:
        if section[1] in (4,9) and section[7]==text_id:
            expected = 24 if section[1]==4 else 16
            if section[9]!=expected or section[5] % expected:
                raise ValueError('unsupported relocation table')
            table=contents(section)
            for position in range(0,len(table),expected):
                offset=struct.unpack_from('<Q',table,position)[0]
                if start <= offset < start+size:
                    raise ValueError('unresolved function relocation')
    return dict(object_sha256=sha256(data),text_sha256=sha256(text),
        function_sha256=sha256(text[start:start+size]),text_size=len(text),
        function_start=start,function_size=size,sections=names,
        text_bytes=text,function_bytes=text[start:start+size])


def compare_machine_bytes(variants):
    existing=variants['existing']
    for label,value in variants.items():
        if any(value[key]!=existing[key] for key in ['text_bytes','function_bytes','function_start','function_size']):
            raise InputMismatch(f'{label}: .text/function machine input changed')


def scalar(raw):
    return int(raw.rsplit(' ', 1)[-1], 0)


def reference(raw):
    match = re.search(r'<0x([0-9a-f]+)>', raw)
    return int(match[1], 16) if match else None


def name(raw):
    if '): ' in raw:
        return raw.rsplit('): ', 1)[-1]
    return re.sub(r'^\(string\)\s*', '', raw)


def dies(text):
    items = {}
    ancestors = []
    current = None
    for line in text.splitlines():
        match = re.match(r'\s*<(\d+)><([0-9a-f]+)>: Abbrev Number: \d+(?: \((DW_TAG_\w+)\))?', line)
        if match:
            depth, offset, tag = int(match[1]), int(match[2], 16), match[3]
            ancestors = ancestors[:depth]
            if depth > 128 or depth > len(ancestors):
                raise ValueError('unsupported DIE nesting')
            if tag and offset in items:
                raise ValueError('duplicate DIE offset')
            if tag:
                parent = ancestors[-1] if ancestors else None
                current = {'id': offset, 'tag': tag, 'parent': parent, 'attrs': {}}
                items[offset] = current
                if len(items) > 100_000:
                    raise ValueError('excessive DIE count')
                ancestors.append(offset)
            else:
                current = None
            continue
        match = re.match(r'\s*<[0-9a-f]+>\s+(DW_AT_\w+)\s*:\s*(.*)', line)
        if match and current is None:
            raise ValueError('DIE attribute outside a DIE')
        if match and current is not None:
            if match[1] in current['attrs']:
                raise ValueError('duplicate DIE attribute')
            current['attrs'][match[1]] = match[2]
        elif ('DW_AT_' in line or 'DW_TAG_' in line) and not match:
            raise ValueError('unrecognized GNU readelf DIE syntax')
    return items


def span(item):
    attrs = item['attrs']
    if 'DW_AT_ranges' in attrs:
        raise ValueError('range list unsupported')
    if 'DW_AT_low_pc' not in attrs or 'DW_AT_high_pc' not in attrs:
        raise ValueError('missing exact PC span')
    if not attrs['DW_AT_low_pc'].startswith('(addr) ') or not re.match(r'\((?:addr|data[1248]|udata)\) ', attrs['DW_AT_high_pc']):
        raise ValueError('indexed or unknown PC forms unsupported')
    low = scalar(attrs['DW_AT_low_pc'])
    high = scalar(attrs['DW_AT_high_pc'])
    if '(addr)' not in attrs['DW_AT_high_pc']:
        high += low
    if high <= low:
        raise ValueError('empty/reversed PC span')
    return [low, high]


def type_info(items, offset, seen=()):
    if offset is None or offset not in items or offset in seen or len(seen) > 16:
        raise ValueError('unresolved/cyclic type')
    item = items[offset]
    attrs, tag = item['attrs'], item['tag']
    label = name(attrs.get('DW_AT_name', '<anonymous>'))
    if tag in ('DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type', 'DW_TAG_restrict_type'):
        inner = type_info(items, reference(attrs.get('DW_AT_type', '')), seen+(offset,))
        return dict(inner, spelling=label if label != '<anonymous>' else inner['spelling'])
    if tag in ('DW_TAG_base_type', 'DW_TAG_pointer_type', 'DW_TAG_union_type'):
        if 'DW_AT_byte_size' not in attrs:
            raise ValueError('type byte size missing')
        return {'kind': tag[len('DW_TAG_'):], 'size': scalar(attrs['DW_AT_byte_size']),
                'spelling': label, 'die': offset,
                'encoding': attrs.get('DW_AT_encoding')}
    raise ValueError(f'type unsupported: {tag}')


def type_extent(items, offset, seen=()):
    # An unsupported type may still occupy known bytes. This bound is used
    # only to suppress ambiguous positive matches, never to accept a variable.
    if offset not in items or offset in seen or len(seen)>16:
        return None
    attrs=items[offset]['attrs']
    if 'DW_AT_byte_size' in attrs:
        return scalar(attrs['DW_AT_byte_size'])
    if items[offset]['tag'] in ('DW_TAG_typedef','DW_TAG_const_type','DW_TAG_volatile_type','DW_TAG_restrict_type'):
        return type_extent(items,reference(attrs.get('DW_AT_type','')),seen+(offset,))
    return None


def parse_variables(info, function, symbol="fixture"):
    if info.count('Compilation Unit @ offset') != 1 or not re.search(r'Version:\s+5(?:\s|$)', info) or 'DW_UT_compile' not in info:
        raise ValueError('only one DWARF5 compilation unit is supported')
    if len(info) > 32 * 1024 * 1024 or any(x in info for x in ('DW_AT_dwo_name', 'DW_AT_GNU_dwo_name', 'DW_AT_GNU_dwo_id', 'DW_AT_import')):
        raise ValueError('external or excessive debug information unsupported')
    items = dies(info)
    producers = [x['attrs'].get('DW_AT_producer', '') for x in items.values() if x['tag'] == 'DW_TAG_compile_unit']
    options = [token for producer in producers for token in name(producer).split() if token.startswith('-O')]
    if len(producers) != 1 or not re.match(r'GNU C(?:\d+)?\s', name(producers[0])) or not options or set(options) != {'-O0'}:
        raise ValueError('optimized or unknown optimization level unsupported; require explicit -O0 only')
    functions = [d for d in items.values() if d['tag'] == 'DW_TAG_subprogram'
                 and name(d['attrs'].get('DW_AT_name', '')) == symbol]
    if len(functions) != 1:
        raise ValueError('require unique requested function DIE')
    subprogram = functions[0]
    if span(subprogram) != [function['function_start'], function['function_start']+function['function_size']]:
        raise ValueError('DWARF function range differs from symbol')
    frame = subprogram['attrs'].get('DW_AT_frame_base', '')
    if not re.search(r'\(DW_OP_call_frame_cfa\)$', frame) or frame.count('DW_OP_') != 1:
        raise ValueError('frame base is not simple CFA')
    result = []
    for item in items.values():
        if item['tag'] not in ('DW_TAG_variable', 'DW_TAG_formal_parameter'):
            continue
        chain = []
        ancestor = item['parent']
        while ancestor is not None:
            chain.append(items[ancestor])
            ancestor = items[ancestor]['parent']
        if subprogram not in chain:
            continue
        attrs = item['attrs']
        row = {'die': item['id'], 'name': name(attrs.get('DW_AT_name', '')),
               'kind': item['tag'][len('DW_TAG_'):], 'status': 'unsupported',
               'decl_file_index': scalar(attrs['DW_AT_decl_file']) if 'DW_AT_decl_file' in attrs else None,
               'decl_line': scalar(attrs['DW_AT_decl_line']) if 'DW_AT_decl_line' in attrs else None,
               'raw_location': attrs.get('DW_AT_location')}
        raw_location=attrs.get('DW_AT_location','')
        raw_fbreg=re.search(r'\(DW_OP_fbreg: (-?\d+)\)$',raw_location)
        if raw_fbreg and raw_location.count('DW_OP_')==1 and '(exprloc)' in raw_location:
            row['opaque_source_extent']=dict(fbreg=int(raw_fbreg[1]),size=type_extent(items,reference(attrs.get('DW_AT_type',''))))
        try:
            if any(parent['tag'] not in ('DW_TAG_compile_unit', 'DW_TAG_subprogram', 'DW_TAG_lexical_block') for parent in chain):
                raise ValueError('inline/other scope context unsupported')
            if any(parent['tag'] == 'DW_TAG_subprogram' and parent is not subprogram for parent in chain):
                raise ValueError('nested subprogram unsupported')
            if not row['name'] or 'DW_AT_start_scope' in attrs:
                raise ValueError('unnamed or start_scope unsupported')
            location = attrs.get('DW_AT_location', '')
            match = re.search(r'\(DW_OP_fbreg: (-?\d+)\)$', location)
            if not match or location.count('DW_OP_') != 1 or '(exprloc)' not in location:
                raise ValueError('not a single DW_OP_fbreg location (register/list/piece/optimized unsupported)')
            scope = span(subprogram)
            scope_ids = [subprogram['id']]
            for parent in reversed(chain):
                if parent['tag'] == 'DW_TAG_lexical_block':
                    block = span(parent)
                    scope = [max(scope[0], block[0]), min(scope[1], block[1])]
                    scope_ids.append(parent['id'])
            if scope[1] <= scope[0]:
                raise ValueError('scope intersection empty')
            row.update(type=type_info(items, reference(attrs.get('DW_AT_type', ''))),
                       fbreg=int(match[1]), scope_pc=scope, scope_dies=scope_ids,
                       status='pending_cfa_verification')
        except ValueError as error:
            row['reason'] = str(error)
        result.append(row)
        if len(result) > 4096:
            raise ValueError('excessive source object count')
    producer = [x['attrs']['DW_AT_producer'] for x in items.values()
                if x['tag'] == 'DW_TAG_compile_unit']
    return result, producer


def parse_cfa(text, function):
    found = []
    current = None
    for line in text.splitlines():
        match = re.search(r'FDE .*pc=([0-9a-f]+)\.\.([0-9a-f]+)', line)
        if match:
            current = {'span': [int(match[1], 16), int(match[2], 16)], 'rows': []}
            found.append(current)
            continue
        if ' CIE ' in line:
            current = None
        match = re.match(r'\s*([0-9a-f]{16})\s+(\S+)', line)
        if match and current is not None:
            cfa = re.fullmatch(r'(rsp|rbp)([+-]\d+)', match[2])
            if not cfa:
                raise ValueError(f'unsupported CFA expression: {match[2]}')
            current['rows'].append({'pc': int(match[1], 16), 'register': cfa[1], 'offset': int(cfa[2])})
    start, size = function['function_start'], function['function_size']
    matches = [x for x in found if x['span'] == [start, start+size]]
    if len(matches) != 1 or not matches[0]['rows'] or matches[0]['rows'][0]['pc'] != start:
        raise ValueError('require unique covering FDE with explicit entry row')
    return matches[0]


def signed_offset(value):
    return (value + (1 << 63)) % MOD - (1 << 63)


def overlap(a, n, b, m):
    return (a - b) % MOD < m or (b - a) % MOD < n


def verify_frame(cfa, text, variables):
    lines = text.splitlines()
    if not lines or lines[0] != 'FORMAT\tnirvana-stack-frame-v1':
        raise ValueError('unrecognized frame-helper protocol')
    points, accesses = {}, []
    for line in lines[1:]:
        fields = line.split('\t')
        if fields[0] == 'POINT' and len(fields) == 4:
            pc = int(fields[1])
            if pc in points or not cfa['span'][0] <= pc < cfa['span'][1]:
                raise ValueError('duplicate/out-of-range frame point')
            offsets = [None if f == '?' else int(f) for f in fields[2:]]
            if any(v is not None and not -(1 << 63) <= v < (1 << 63) for v in offsets):
                raise ValueError('frame offset outside i64')
            points[pc] = offsets
        elif fields[0] == 'ACCESS' and len(fields) == 6:
            pc, assignment, offset, width = map(int, fields[1:5])
            if assignment < 0 or not -(1 << 63) <= offset < (1 << 63) or width not in (1, 2, 4, 8) or fields[5] not in ('read', 'write'):
                raise ValueError('invalid frame access')
            accesses.append(dict(pc=pc, assignment=assignment, offset=offset, width=width, kind=fields[5]))
        else:
            raise ValueError('unrecognized frame-helper record')
        if len(points) + len(accesses) > 250_000:
            raise ValueError('excessive frame records')
    if not points or any(a['pc'] not in points for a in accesses):
        raise ValueError('missing frame instruction points')
    rows = cfa['rows']
    if rows[0] != dict(pc=cfa['span'][0], register='rsp', offset=8):
        raise ValueError('entry CFA must be rsp+8')
    if [r['pc'] for r in rows] != sorted({r['pc'] for r in rows}):
        raise ValueError('duplicate/unordered CFA rows')
    if any(r['pc'] not in points for r in rows):
        raise ValueError('CFA row lacks a reachable instruction-point proof')
    index, checked = 0, []
    for pc, (rsp, rbp) in sorted(points.items()):
        if rsp is None:
            raise ValueError('dynamic/realigned/unknown stack unsupported')
        while index + 1 < len(rows) and rows[index + 1]['pc'] <= pc:
            index += 1
        row = rows[index]
        delta = dict(rsp=rsp, rbp=rbp)[row['register']]
        if delta is None or (delta + row['offset']) % MOD != 8:
            raise ValueError(f'CFA is not entry RSP+8 at {pc:#x}')
        checked.append(dict(pc=pc, cfa_row_pc=row['pc'], cfa_entry_offset=8))
    for var in variables:
        if var['status'] != 'pending_cfa_verification':
            continue
        var['entry_rsp_offset'] = signed_offset(var['fbreg'] + 8)
        touches = [a for a in accesses if overlap(a['offset'], a['width'], var['entry_rsp_offset'], var['type']['size'])]
        var['known_stack_accesses'] = len(touches)
        var['out_of_scope_accesses'] = [a for a in touches if not var['scope_pc'][0] <= a['pc'] < var['scope_pc'][1]]
        var['partial_accesses'] = [a for a in touches if (a['offset'], a['width']) != (var['entry_rsp_offset'], var['type']['size'])]
        var['status'] = 'matched_cell'
    for var in variables:
        if var['status'] != 'matched_cell':
            continue
        aliases, unresolved = [], []
        for other in variables:
            if other is var:
                continue
            if other['status'] == 'matched_cell':
                start, size = other['entry_rsp_offset'], other['type']['size']
            elif other.get('opaque_source_extent', {}).get('size'):
                start = signed_offset(other['opaque_source_extent']['fbreg'] + 8)
                size = other['opaque_source_extent']['size']
            else:
                unresolved.append(other['die'])
                continue
            if overlap(var['entry_rsp_offset'], var['type']['size'], start, size):
                aliases.append(other['die'])
        var['overlapping_source_dies'] = aliases
        var['unresolved_source_die_bounds'] = unresolved
        var['integer_local_eligible'] = (var['kind'] == 'variable' and var['type']['kind'] == 'base_type'
            and var['type']['size'] in (1, 2, 4, 8) and not aliases and not unresolved and not var['out_of_scope_accesses'])
    cfa['verified_points'] = checked


def unescape(value):
    result, index = [], 0
    while index < len(value):
        if value[index] != '\\':
            result.append(value[index])
            index += 1
            continue
        index += 1
        if index >= len(value) or value[index] not in ('\\', 't', 'n'):
            raise ValueError('unsupported TSV escape')
        result.append({'\\': '\\', 't': '\t', 'n': '\n'}[value[index]])
        index += 1
    return ''.join(result)


def parse_metadata(text, metadata_root):
    if len(text) > MAX_FILE:
        raise ValueError('excessive metadata')
    reader = csv.DictReader(io.StringIO(text), delimiter='\t')
    if reader.fieldnames not in (COLUMNS, COLUMNS + ['basis']):
        raise ValueError('metadata requires the seven columns and optional final basis')
    result, seen = {}, set()
    for index, raw in enumerate(reader):
        if index > 250_000 or None in raw or any(v is None for v in raw.values()):
            raise ValueError('malformed/excessive TSV rows')
        path = Path(unescape(raw['object']))
        path = (Path(metadata_root) / path).resolve()
        register = int(raw['register'])
        if not 0 <= register < MOD or (str(path), register) in seen:
            raise ValueError('negative/duplicate metadata register')
        seen.add((str(path), register))
        row = dict(raw, object=str(path), register=register, local=unescape(raw['local']))
        if not row['local']:
            raise ValueError('empty C local name')
        for field in ('web', 'offset', 'width'):
            row[field] = None if raw[field] == '-' else int(raw[field])
        basis = raw.get('basis', 'store-web' if row['web'] is not None else '-')
        if basis not in ('store-web', 'load-cell', '-'):
            raise ValueError('unknown association basis')
        known = basis != '-'
        if known and (row['offset'] is None or row['width'] not in (1, 2, 4, 8)):
            raise ValueError('known association lacks an exact cell')
        if row['offset'] is not None and not -(1 << 63) <= row['offset'] < (1 << 63):
            raise ValueError('cell offset outside i64')
        if basis == 'store-web' and (row['web'] is None or not 0 <= row['web'] < MOD):
            raise ValueError('store-web requires a nonnegative web ID')
        if basis == 'load-cell' and row['web'] is not None:
            raise ValueError('load-cell cannot claim a store-web ID')
        if not known and any(row[k] is not None for k in ('web', 'offset', 'width')):
            raise ValueError('unknown association must have empty cell/web fields')
        row['basis'] = basis
        result.setdefault(str(path), []).append(row)
    return result


def classify(row, variables):
    if row['basis'] == '-':
        return 'missing_association', None
    matches = [v for v in variables if v['status'] == 'matched_cell'
        and (row['offset'], row['width']) == (v['entry_rsp_offset'], v['type']['size'])]
    if len(matches) != 1:
        return 'unmatched_or_ambiguous_cell', None
    var = matches[0]
    if var['overlapping_source_dies'] or var['unresolved_source_die_bounds']:
        return 'ambiguous_source_bytes', None
    if var['out_of_scope_accesses']:
        return 'unsupported_scope', None
    if var['kind'] == 'formal_parameter':
        return 'known_parameter', var['source_id']
    if not var['integer_local_eligible']:
        return 'known_noninteger_object', var['source_id']
    return 'known_integer_local', var['source_id']


def measure(rows, variables):
    groups, sources, counts = {}, {}, Counter()
    for row in rows:
        reason, identity = classify(row, variables)
        counts[reason] += 1
        groups.setdefault(row['local'], []).append(dict(row, classification=reason, source_id=identity))
        if reason == 'known_integer_local':
            sources.setdefault(identity, set()).add(row['local'])
    source_rows = []
    for var in variables:
        if var.get('integer_local_eligible'):
            locals_ = sorted(sources.get(var['source_id'], []))
            source_rows.append(dict(source_id=var['source_id'], die=var['die'], name=var['name'],
                locals=locals_, fragments=len(locals_), extra_fragments=max(0, len(locals_) - 1)))
    mixed = []
    for local, members in groups.items():
        identities = sorted({m['source_id'] for m in members if m['source_id'] is not None})
        if len(identities) > 1:
            mixed.append(dict(local=local, source_ids=identities))
    return dict(emitted_locals=len(groups), member_registers=len(rows), classifications=dict(counts),
        integer_associated_registers=counts['known_integer_local'],
        integer_source_objects=len(source_rows), observed_integer_source_objects=sum(bool(v['fragments']) for v in source_rows),
        known_fragments=sum(v['fragments'] for v in source_rows),
        known_extra_fragments=sum(v['extra_fragments'] for v in source_rows),
        mixed_locals=mixed, source_objects=source_rows, locals=groups,
        bases=dict(Counter(row['basis'] for row in rows)))


def association(row):
    if row['basis'] == '-':
        return None
    return row['basis'], row['web'], row['offset'], row['width']


def common_regressions(before, after):
    prior = {v['source_id']: v for v in before['source_objects']}
    increased = [dict(source_id=v['source_id'], name=v['name'],
                     before=prior[v['source_id']]['locals'], after=v['locals'])
                 for v in after['source_objects'] if v['fragments'] > prior[v['source_id']]['fragments']]
    def pairs(measurement):
        result = set()
        for group in measurement['mixed_locals']:
            ids = group['source_ids']
            result.update((a, b) for i, a in enumerate(ids) for b in ids[i+1:])
        return result
    return dict(increased_fragmentation=increased,
                new_known_mixing_pairs=sorted(pairs(after) - pairs(before)))


def compare_metadata(before, after, variables):
    old, new = [{r['register']: r for r in rows} for rows in (before, after)]
    common = sorted(r for r in old.keys() & new.keys()
        if association(old[r]) is not None and association(old[r]) == association(new[r]))
    newly_known = sorted(r for r in new if association(new[r]) is not None
        and (r not in old or association(old[r]) is None))
    changed = sorted(r for r in old.keys() & new.keys()
        if association(old[r]) is not None and association(new[r]) is not None
        and association(old[r]) != association(new[r]))
    removed = sorted(r for r in old if association(old[r]) is not None
        and (r not in new or association(new[r]) is None))
    common_before = measure([old[r] for r in common], variables)
    common_after = measure([new[r] for r in common], variables)
    return dict(full=dict(before=measure(before, variables), after=measure(after, variables)),
        common=dict(registers=common, before=common_before, after=common_after,
                    regressions=common_regressions(common_before, common_after)),
        expanded_coverage=dict(registers=newly_known, after=measure([new[r] for r in newly_known], variables)),
        changed_association_registers=changed, removed_association_registers=removed,
        member_ids_identical=old.keys() == new.keys())


def validate_flags(flags):
    if not isinstance(flags, list) or not flags or '-O0' not in flags or any(not isinstance(f, str) for f in flags):
        raise ValueError('flags must be a list containing explicit -O0')
    for flag in flags:
        if not flag.startswith('-') or flag.startswith('-g') or (flag.startswith('-O') and flag != '-O0'):
            raise ValueError('require nondebug O0 flags, with packed option arguments')
        if flag in ('-c', '-S', '-E', '-o', '-fsyntax-only', '-save-temps') or flag.startswith(('-o', '--output', '@', '-M', '-fdump', '-save-temps')):
            raise ValueError('flags must not select outputs or side files')
    return flags


def load_cases(path, source_root, objects):
    data = json.loads(Path(path).read_text())
    rows = data['cases'] if isinstance(data, dict) and 'cases' in data else data
    if not isinstance(rows, list) or not 0 < len(rows) <= 256:
        raise ValueError('cases must be a nonempty JSON list (at most256)')
    result, ids, paths = [], set(), set()
    for row in rows:
        label = row['id']
        if not isinstance(label, str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,100}', label) or label in ids:
            raise ValueError('invalid/duplicate case ID')
        source = (Path(source_root) / row['source']).resolve()
        obj = (Path(objects) / row.get('object', label + '.o')).resolve()
        if str(obj) in paths:
            raise ValueError('multiple cases cannot share an object path')
        ids.add(label)
        paths.add(str(obj))
        result.append(dict(id=label, source=source, object=obj, flags=validate_flags(row.get('flags', DEFAULT_FLAGS))))
    return result


def executable(value):
    return str(Path(value).resolve()) if os.sep in str(value) else str(value)


def evaluate_case(case, args, runner, out, metadata):
    folder = out / case['id']
    folder.mkdir()
    record = dict(id=case['id'], source=str(case['source']), object=str(case['object']),
                  flags=case['flags'], status='unsupported', variables=[])
    stage = 'input'
    try:
        source_bytes = case['source'].read_bytes()
        if len(source_bytes) > MAX_FILE:
            raise ValueError('excessive source file')
        record['source_sha256'] = sha256(source_bytes)
        variants = dict(existing=read_elf(case['object'], args.symbol, require_nondebug=True))
        stage = 'compile'
        for label, extra in [('plain', []), ('debug', ['-g'])]:
            path = folder / (label + '.o')
            runner.run([executable(args.cc), *case['flags'], *extra, '-c', case['source'], '-o', path])
            variants[label] = read_elf(path, args.symbol)
        stage = 'machine_input'
        compare_machine_bytes(variants)
        record['machine_bytes_identical'] = True
        record['objects'] = {k: {a: b for a, b in v.items() if a not in ('text_bytes', 'function_bytes')}
                             for k, v in variants.items()}
        stage = 'debug_information'
        raw = {}
        for kind in ('info', 'frames-interp'):
            raw[kind] = runner.run([executable(args.readelf), '--wide', '--debug-dump=' + kind,
                                   '--debug-dump=no-follow-links', folder / 'debug.o'])
            (folder / (kind + '.txt')).write_text(raw[kind])
        variables, producer = parse_variables(raw['info'], variants['existing'], args.symbol)
        for var in variables:
            var['source_id'] = record['source_sha256'] + ':' + format(var['die'], 'x')
        record['variables'], record['producer'] = variables, producer
        cfa = parse_cfa(raw['frames-interp'], variants['existing'])
        stage = 'frame_helper'
        frame = runner.run([str(args.frame_helper), '--symbol', args.symbol, case['object']])
        (folder / 'frame.tsv').write_text(frame)
        verify_frame(cfa, frame, variables)
        record['cfa'] = cfa
        stage = 'metadata'
        sets = []
        for mode in ('before', 'after'):
            helper = getattr(args, mode + '_helper')
            if helper:
                text = runner.run([str(helper), case['object']])
                (folder / (mode + '.tsv')).write_text(text)
                parsed = parse_metadata(text, args.metadata_root)
                if any(p != str(case['object']) for p in parsed):
                    raise ValueError('metadata helper returned another object')
                rows = parsed.get(str(case['object']), [])
            else:
                if str(case['object']) not in metadata[mode]:
                    raise ValueError(mode + ' TSV has no rows for object; use a helper for zero-local outputs')
                rows = metadata[mode][str(case['object'])]
            sets.append(rows)
        if sha256(case['object'].read_bytes()) != variants['existing']['object_sha256'] or case['source'].read_bytes() != source_bytes:
            raise InputMismatch('source or existing object changed during evaluation')
        record['comparison'] = compare_metadata(*sets, variables)
        record['status'] = 'evaluated'
    except InputMismatch:
        raise
    except (ValueError, OSError, struct.error, UnicodeError) as error:
        record['unsupported'] = dict(stage=stage, reason=str(error))
    return record


def summarize(cases):
    result = dict(cases=len(cases), evaluated=sum(c['status'] == 'evaluated' for c in cases),
        identical_inputs=sum(c.get('machine_bytes_identical', False) for c in cases),
        variables=dict(Counter(v['status'] for c in cases for v in c['variables'])),
        unsupported=[dict(id=c['id'], **c['unsupported']) for c in cases if 'unsupported' in c])
    for scope in ('full', 'common'):
        result[scope] = {}
        for mode in ('before', 'after'):
            ms = [c['comparison'][scope][mode] for c in cases if 'comparison' in c]
            fields = ('emitted_locals', 'member_registers', 'integer_associated_registers',
                      'integer_source_objects', 'observed_integer_source_objects', 'known_fragments', 'known_extra_fragments')
            totals = {k: sum(m[k] for m in ms) for k in fields}
            totals['known_mixed_locals'] = sum(len(m['mixed_locals']) for m in ms)
            totals['classifications'] = dict(sum((Counter(m['classifications']) for m in ms), Counter()))
            totals['bases'] = dict(sum((Counter(m['bases']) for m in ms), Counter()))
            result[scope][mode] = totals
    added = [c['comparison']['expanded_coverage']['after'] for c in cases if 'comparison' in c]
    result['expanded_coverage'] = dict(registers=sum(m['member_registers'] for m in added),
        integer_associated_registers=sum(m['integer_associated_registers'] for m in added),
        classifications=dict(sum((Counter(m['classifications']) for m in added), Counter())),
        bases=dict(sum((Counter(m['bases']) for m in added), Counter())))
    result['changed_associations'] = sum(len(c['comparison']['changed_association_registers']) for c in cases if 'comparison' in c)
    result['changed_member_id_cases'] = [c['id'] for c in cases if 'comparison' in c and not c['comparison']['member_ids_identical']]
    result['common_regressions'] = [dict(id=c['id'], **c['comparison']['common']['regressions']) for c in cases if 'comparison' in c and any(c['comparison']['common']['regressions'].values())]
    return result


def write_report(out, report):
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    summary = report.get('summary', {})
    lines = ['# Source recovery evaluation', '',
        f"Evaluated {summary.get('evaluated', 0)}/{summary.get('cases', 0)} cases. Unknown and unsupported associations are excluded from positive recovery counts.", '',
        '| Scope | Side | Known integer registers | Fragments | Extra fragments | Mixed known-source locals |',
        '| --- | --- | ---: | ---: | ---: | ---: |']
    for scope in ('common', 'full'):
        for mode, m in summary.get(scope, {}).items():
            lines.append(f"| {scope} | {mode} | {m['integer_associated_registers']} | {m['known_fragments']} | {m['known_extra_fragments']} | {m['known_mixed_locals']} |")
    expanded = summary.get('expanded_coverage', {})
    lines += ['', f"Expanded coverage: {expanded.get('registers', 0)} newly known location associations, including {expanded.get('integer_associated_registers', 0)} integer-source matches."]
    lines += ['', 'Common uses only identical known register/basis/web/cell tuples. Full coverage can grow and is reported separately; growth is not an apples-to-apples accuracy gain.', '',
        'Source identity is source SHA256 + DIE, never spelling. Lexical scopes do not prove lifetimes; reused/ambiguous cells are rejected. Scope checks cover only proven stack accesses. Compiler DWARF, the frame helper and metadata producers are trusted. Stable register IDs across compared display IRs are an input precondition.', '',
        'Exact inputs, tool versions, commands, unsupported reasons, source objects and all register associations are in report.json. This tool does not establish native semantic equivalence.', '']
    if 'fatal_error' in report:
        lines.append('FAILED: ' + report['fatal_error'])
    (out / 'report.md').write_text('\n'.join(lines))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--cases', type=Path, required=True, help='JSON list or {"cases":[...]}')
    parser.add_argument('--source-root', type=Path, default=Path.cwd())
    parser.add_argument('--objects', type=Path, required=True, help='existing nondebug object directory')
    parser.add_argument('--symbol', default='fixture')
    parser.add_argument('--frame-helper', type=Path, required=True, help='inspect_stack_frame executable')
    parser.add_argument('--metadata-root', type=Path, default=Path.cwd(), help='base for relative TSV object paths')
    for mode in ('before', 'after'):
        group = parser.add_mutually_exclusive_group(required=True)
        group.add_argument('--' + mode + '-metadata', type=Path)
        group.add_argument('--' + mode + '-helper', type=Path, help='measure_variables-compatible executable')
    parser.add_argument('--cc', default='cc')
    parser.add_argument('--readelf', default='readelf')
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--out', type=Path, required=True, help='new or empty artifact directory; never deletes files')
    args = parser.parse_args(argv)
    report = dict(schema='source-recovery-v1', cases=[], notes=[
        'Only explicit GNU C O0/DWARF5 simple frame-relative locations are supported.',
        'Source/debug copies are evaluation inputs only; helpers receive existing nondebug objects.',
        'Common comparisons require stable display-IR register identities supplied by the metadata producers.',
        'Source provenance is supplied by the caller; identical machine bytes do not prove a unique original source.',
        'Local labels must uniquely identify emitted storage groups within an object.'])
    try:
        if not math.isfinite(args.timeout) or args.timeout <= 0 or not re.fullmatch(r'[A-Za-z_]\w*', args.symbol):
            raise ValueError('invalid timeout or symbol')
        args.source_root, args.objects = args.source_root.resolve(), args.objects.resolve()
        args.metadata_root, args.frame_helper = args.metadata_root.resolve(), args.frame_helper.resolve()
        args.out = args.out.resolve()
        if args.out.exists() and any(args.out.iterdir()):
            raise ValueError('--out must be new or empty')
        cases = load_cases(args.cases, args.source_root, args.objects)
        metadata = {}
        for mode in ('before', 'after'):
            helper = getattr(args, mode + '_helper')
            if helper:
                setattr(args, mode + '_helper', helper.resolve())
            else:
                metadata[mode] = parse_metadata(getattr(args, mode + '_metadata').read_text(), args.metadata_root)
        args.out.mkdir(parents=True, exist_ok=True)
        runner = Runner(args.source_root, args.timeout)
        report['environment'] = dict(LC_ALL='C', DEBUGINFOD_URLS='')
        report['tools'] = {tool: runner.run([executable(getattr(args, tool)), '--version']) for tool in ('cc', 'readelf')}
        if not report['tools']['readelf'].startswith('GNU readelf'):
            raise ValueError('only GNU readelf output is supported')
        report['frame_helper_sha256'] = sha256(args.frame_helper.read_bytes())
        report['cases_sha256'] = sha256(args.cases.read_bytes())
        report['metadata_inputs'] = {}
        for mode in ('before', 'after'):
            input_path = getattr(args, mode + '_helper') or getattr(args, mode + '_metadata')
            report['metadata_inputs'][mode] = dict(path=str(input_path.resolve()),
                kind='helper' if getattr(args, mode + '_helper') else 'tsv',
                sha256=sha256(input_path.read_bytes()))
        for case in cases:
            report['cases'].append(evaluate_case(case, args, runner, args.out, metadata))
        report['commands'] = runner.commands
        report['summary'] = summarize(report['cases'])
        write_report(args.out, report)
        print(json.dumps(report['summary'], indent=2))
        return 0
    except (ValueError, OSError, KeyError, TypeError, csv.Error) as error:
        report['fatal_error'] = str(error)
        if 'runner' in locals():
            report['commands'] = runner.commands
        if 'args' in locals() and args.out.is_dir() and not any(args.out.iterdir()):
            write_report(args.out, report)
        elif 'runner' in locals():
            write_report(args.out, report)
        print('source recovery evaluation failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
