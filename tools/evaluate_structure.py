#!/usr/bin/env python3
"""Record a partial M0 baseline: source/control topology of generated C.

Uses compiler-preprocessed C only on the evaluation side. Nirvana receives
only the nondebug x86-64 object. Every requested profile remains in report.json,
including tool failures, unsupported dumps and bounded distance results.
Exit 0 means the report was produced, not semantic equivalence or M0 completion.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
import platform
import resource
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
import traceback

from evaluation import control_graph as cg
from evaluation import semantics
from evaluation import c_footprint as cf
from evaluation import state_memory as sm
from evaluation.state_values import protocol as sv

ROOT = Path(__file__).resolve().parents[1]
FLAGS = ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic', '-fno-lto']
IDENTIFIER = re.compile(r'[A-Za-z_][A-Za-z_0-9]*\Z')
TAG = re.compile(r'[A-Za-z0-9][A-Za-z0-9_-]{0,63}\Z')


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def capture(argv, timeout, input=None, **kwargs):
    """Bound the command and its compiler children, including on interruption."""
    with subprocess.Popen(argv, stdin=subprocess.PIPE if input is not None else None,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, start_new_session=True, **kwargs) as process:
        try:
            stdout, stderr = process.communicate(input=input, timeout=timeout)
        except BaseException as error:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = process.communicate()
            if isinstance(error, subprocess.TimeoutExpired):
                error.stdout, error.stderr = stdout, stderr
            raise
        return subprocess.CompletedProcess(argv, process.returncode, stdout, stderr)


def load_cases(path):
    value = json.loads(Path(path).read_text())
    if value.get('schema') != 'nirvana-structure-corpus-v1':
        raise ValueError('unknown corpus schema')
    cases = value['cases']
    if not 0 < len(cases) <= 64:
        raise ValueError('require 1..64 cases')
    ids, families = set(), {}
    for case in cases:
        if not TAG.fullmatch(case['id']) or case['id'] in ids:
            raise ValueError('require unique safe case IDs')
        ids.add(case['id'])
        if not IDENTIFIER.fullmatch(case['function']):
            raise ValueError('invalid function name')
        if case['cohort'] not in ['development', 'holdout']:
            raise ValueError('unknown cohort')
        family = case['family']
        if not isinstance(family, str) or not family:
            raise ValueError('require source family')
        if family in families and families[family] != case['cohort']:
            raise ValueError('source family split across cohorts')
        families[family] = case['cohort']
        source = (ROOT / case['source']).resolve()
        if not source.is_relative_to(ROOT) or not source.is_file():
            raise ValueError('source must name an existing repository file')
        if case.get('source_sha256') is not None and case['source_sha256'] != digest(source):
            raise ValueError('corpus source hash mismatch; version the changed corpus')
    return cases


def provenance(executable, timeout):
    path = shutil.which(str(executable))
    if not path:
        return {'requested': str(executable), 'status': 'unavailable'}
    try:
        result = capture([path, '--version'], timeout)
        return {'path': str(Path(path).resolve()), 'sha256': digest(path),
                'version': result.stdout.strip(), 'returncode': result.returncode,
                'stderr': result.stderr}
    except (OSError, subprocess.TimeoutExpired) as error:
        return {'path': path, 'status': 'unavailable', 'error': str(error)}


class CommandError(Exception):
    def __init__(self, kind, message):
        self.kind = kind
        super().__init__(message)


def invoke(argv, stage, directory, row, timeout, **kwargs):
    argv = list(map(str, argv))
    record = {'stage': stage, 'argv': argv, 'cwd': str(ROOT)}
    row['commands'].append(record)
    start = time.monotonic()
    try:
        actual = argv
        if row.get('measure_rss'):
            if not shutil.which(argv[0]):
                raise FileNotFoundError(f'executable unavailable: {argv[0]}')
            resources = directory / f'{stage}.resources.txt'
            actual = ['/usr/bin/time', '-q', '-f', '%M %U %S', '-o', str(resources), '--', *argv]
            record['measurement_argv'] = actual
        result = capture(actual, timeout, cwd=ROOT, env=dict(os.environ, LC_ALL='C'), **kwargs)
        record.update(returncode=result.returncode, wall_seconds=time.monotonic() - start)
        if row.get('measure_rss'):
            values = resources.read_text().split()
            if len(values) == 3:
                record['resources'] = {'max_rss_kib': int(values[0]),
                                       'user_seconds': float(values[1]), 'system_seconds': float(values[2]),
                                       'scope': 'largest process in this command and its waited children'}
        for name, content in [('stdout', result.stdout), ('stderr', result.stderr)]:
            path = directory / f'{stage}.{name}.txt'
            path.write_text(content)
            record[name] = path.name
        if result.returncode:
            diagnostic = result.stderr.lower()
            unsupported = (stage == 'decompile' and not any(s in diagnostic for s in ['panicked at', 'stack overflow'])
                           and any(s in diagnostic for s in ['unsupported', 'not implemented', 'unresolved relocation', 'unresolved import']))
            raise CommandError('unsupported' if unsupported else 'tool_error', result.stderr[-2000:])
        row['stages'][stage] = 'passed'
        return result
    except subprocess.TimeoutExpired as error:
        record.update(status='timeout', wall_seconds=time.monotonic() - start)
        for name in ['stdout', 'stderr']:
            content = getattr(error, name) or ''
            if isinstance(content, bytes):
                content = content.decode(errors='replace')
            path = directory / f'{stage}.{name}.txt'
            path.write_text(content)
            record[name] = path.name
        raise CommandError('timeout', f'{stage}: command exceeded {timeout}s') from error
    except OSError as error:
        record.update(status='unavailable', error=str(error), wall_seconds=time.monotonic() - start)
        raise CommandError('unavailable', str(error)) from error


def measure(case, tag, compiler, opt, args, out):
    row = {**case, 'id': f'{case["id"]}-{tag}-{opt}', 'compiler': tag, 'optimization': opt,
           'stages': {}, 'commands': [], 'semantics': {'status': 'not_run'},
           'measure_rss': args.measure_rss}
    directory = out / row['id']
    directory.mkdir()
    row['artifacts'] = directory.name
    source = ROOT / case['source']
    preprocessed = directory / 'source.i'
    obj = directory / 'input.o'
    generated = directory / 'readable.c'
    row['source_sha256'] = digest(source)
    start = time.monotonic()
    stage = 'preprocess'
    def failed(error, kind):
        row.update(status=kind, failure_stage=stage, error=str(error))
        row['stages'][stage] = kind
        row.setdefault('failures', []).append({'stage': stage, 'status': kind, 'error': str(error)})
    try:
        flags = [*FLAGS, f'-{opt}']
        # Suppress GNU line markers so the retained C11 input can be compiled
        # with the same strict warning flags by either compiler.
        invoke([compiler, *flags, '-E', '-P', source, '-o', preprocessed], stage, directory, row, args.timeout)
        row['preprocessed_sha256'] = digest(preprocessed)
        stage = 'input_compile'
        invoke([compiler, *flags, '-c', preprocessed, '-o', obj], stage, directory, row, args.timeout)
        row['object_sha256'] = digest(obj)
        stage = 'decompile'
        result = invoke([args.decompiler, obj, '--symbol', case['function'], '--emit', args.emit],
                        stage, directory, row, args.timeout)
        generated.write_text(result.stdout)
        row['readable_sha256'] = digest(generated)
        stage = 'recompile'
        invoke([args.c_compiler, *flags, '-c', generated, '-o', directory / 'readable.o'],
               stage, directory, row, args.timeout)
        graphs = []
        for stage, path, function in [('source_cfg', preprocessed, case['function']),
                                      ('generated_cfg', generated, 'nirvana_readable')]:
            result = invoke([args.clang, '--analyze', '-std=c11', '-Werror', '-Xclang',
                             '-analyzer-checker=debug.DumpCFG', path, '-o', os.devnull],
                            stage, directory, row, args.timeout)
            raw, stats = cg.parse_dump(result.stderr, function)
            graph, removed = cg.normalize(raw)
            graph_file = directory / f'{stage}.json'
            graph_file.write_text(json.dumps(
                {'graph': graph, 'stats': {**stats, **removed}}, indent=2) + '\n')
            row[stage] = {**stats, **removed, 'nodes': len(graph['nodes']), 'edges': len(graph['edges']),
                          'graph_sha256': digest(graph_file),
                          'dump_sha256': digest(directory / f'{stage}.stderr.txt')}
            graphs.append(graph)
        stage = 'distance'
        row['distance'] = cg.distance(*graphs, max_states=args.max_states, seconds=args.search_seconds)
        row['stages'][stage] = 'measured'
        row['status'] = 'measured'
    except (CommandError, cg.Unsupported) as error:
        failed(error, error.kind if isinstance(error, CommandError) else 'unsupported')
        row['semantics']['reason'] = f'{stage}: {error}'
    except Exception as error:
        failed(error, 'evaluator_error')
        (directory / 'evaluator.traceback.txt').write_text(traceback.format_exc())
    row['structure_status'] = row['status']
    row['c_footprint'] = {'status': 'not_run'}
    if args.c_footprint:
        sides = {}
        for side, path, function, prerequisite in [
                ('source', preprocessed, case['function'], 'preprocess'),
                ('generated', generated, 'nirvana_readable', 'recompile')]:
            stage = side + '_ast'
            if row['stages'].get(prerequisite) != 'passed':
                sides[side] = {'status': 'not_run', 'reason': prerequisite + ' not completed'}
                continue
            try:
                result = invoke([args.clang, '-std=c11', '-Werror', '-fsyntax-only', '-Xclang',
                                 '-ast-dump=json', '-Xclang', '-ast-dump-filter=' + function, path],
                                stage, directory, row, args.timeout)
                sides[side] = {**cf.measure(result.stdout, function),
                               'raw_ast_sha256': digest(directory / f'{stage}.stdout.txt')}
            except (CommandError, cf.Unsupported) as error:
                kind = error.kind if isinstance(error, CommandError) else 'unsupported'
                sides[side] = {'status': kind, 'reason': str(error)}
                failed(error, kind)
            except Exception as error:
                sides[side] = {'status': 'evaluator_error', 'reason': str(error)}
                failed(error, 'evaluator_error')
                (directory / f'{stage}.traceback.txt').write_text(traceback.format_exc())
        measured = all(value['status'] == 'measured' for value in sides.values())
        row['c_footprint'] = {'metric': cf.METRIC, 'status': 'measured' if measured else 'incomplete', **sides}
        if measured:
            row['c_footprint']['source_generated_delta'] = cf.delta(sides['source'], sides['generated'])
    # Graph-reader failures and bounded distance are independent of execution.
    if args.semantic_probe and row['stages'].get('recompile') == 'passed':
        stage = 'semantic_prepare'
        try:
            def observed(argv, name, **kwargs):
                nonlocal stage
                stage = name
                return invoke(argv, name, directory, row, args.timeout, **kwargs)
            semantics.run(args, row, directory, observed, FLAGS)
            stage = 'semantics'
            if row['semantics']['status'] != 'passed':
                failed('semantic observations differ or remain incomplete', row['semantics']['status'])
            else:
                row['stages']['semantics'] = 'passed'
        except (CommandError, semantics.ProtocolError, OSError) as error:
            kind = error.kind if isinstance(error, CommandError) else 'tool_error'
            failed(error, kind)
            row['semantics'].update(status=kind, reason=f'{stage}: {error}')
        except Exception as error:
            failed(error, 'evaluator_error')
            row['semantics'].update(status='evaluator_error', reason=f'{stage}: {error}')
            (directory / 'evaluator.traceback.txt').write_text(traceback.format_exc())
    row['state_memory_sites'] = {'status': 'not_run'}
    if args.state_memory_sites:
        stage = 'state_memory_sites'
        if (row['c_footprint']['status'] != 'measured'
                or 'parameter_registers' not in row.get('stage_checks', {}).get('selected_c', {})
                or 'prepare_stdout_sha256' not in row['semantics']):
            row['state_memory_sites'] = {'status': 'unavailable', 'reason': 'requires measured C AST and bound ABI metadata'}
        else:
            try:
                row['state_memory_sites'] = sm.measure((directory / 'source_ast.stdout.txt').read_text(),
                    (directory / 'generated_ast.stdout.txt').read_text(), case['function'],
                    row['stage_checks']['selected_c']['parameter_registers'])
            except cf.Unsupported as error:
                row['state_memory_sites'] = {'status': 'unsupported', 'reason': str(error)}
                failed(error, 'unsupported')
            except Exception as error:
                row['state_memory_sites'] = {'status': 'evaluator_error', 'reason': str(error)}
                failed(error, 'evaluator_error')
                (directory / f'{stage}.traceback.txt').write_text(traceback.format_exc())
        row['stages'][stage] = row['state_memory_sites']['status']
    sv.attach(args, row, directory)
    if args.state_values and row['state_values']['status'] in ['counterexample_under_model', 'evaluator_error']:
        stage = 'state_values'
        failed('state value model differs or evaluator failed', row['state_values']['status'])
    row['wall_seconds'] = time.monotonic() - start
    row['max_rss'] = None
    samples = [command['resources']['max_rss_kib'] for command in row['commands'] if 'resources' in command]
    row['command_max_rss_kib'] = max(samples) if samples else None
    (directory / 'row.json').write_text(json.dumps(row, indent=2) + '\n')
    return row


def run(args):
    for name, default in [('emit', 'readable-c'), ('measure_rss', False), ('semantic_probe', None),
                          ('semantic_seed', 0x6e697276616e6130), ('semantic_cases', 16),
                          ('semantic_steps', 4096), ('toolchain_manifest', None), ('semantic_inputs', None),
                          ('c_footprint', False), ('state_memory_sites', False), ('state_values', False),
                          ('value_solver', os.environ.get('NIRVANA_Z3', 'z3')), ('value_seconds', 2.0)]:
        if not hasattr(args, name):
            setattr(args, name, default)
    if args.state_memory_sites and (not args.c_footprint or not args.semantic_probe):
        raise ValueError('state memory sites require --c-footprint and --semantic-probe')
    if args.state_values and not args.state_memory_sites:
        raise ValueError('state values require --state-memory-sites')
    if type(args.value_seconds) not in [int, float] or not 0 < args.value_seconds <= 30:
        raise ValueError('state value solver budget must be positive and at most 30 seconds')
    cases = load_cases(args.cases)
    compilers = []
    for setting in args.compiler or ['gcc=cc']:
        tag, separator, executable = setting.partition('=')
        if not separator or not TAG.fullmatch(tag) or not executable or tag in [t for t, _ in compilers]:
            raise ValueError('compiler must be a unique TAG=EXECUTABLE')
        compilers.append((tag, executable))
    if len(compilers) > 8:
        raise ValueError('compiler profile limit')
    opts = args.optimization or ['O2', 'O3']
    if len(set(opts)) != len(opts):
        raise ValueError('duplicate optimization')
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if any(out.iterdir()):
        raise ValueError('output directory must be empty; preserve earlier baselines')
    args.decompiler = args.decompiler.resolve()
    report = {'schema': 'nirvana-structure-report-v1', 'metric': cg.METRIC,
              'evaluation': {'runner_sha256': digest(__file__), 'metric_sha256': digest(cg.__file__),
                             'semantics_sha256': digest(semantics.__file__),
                             'stages_sha256': digest(Path(semantics.__file__).with_name('stages.py'))},
              'requested_profiles': len(cases) * len(compilers) * len(opts),
              'scope': 'Control topology only; arithmetic, effect contents and semantic equivalence are separate evaluations.',
              'corpus': {'path': str(args.cases.resolve()), 'sha256': digest(args.cases)},
              'workspace_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'workspace_dirty': bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True)),
              'decompiler': {'path': str(args.decompiler), 'sha256': digest(args.decompiler)},
              'clang': provenance(args.clang, args.timeout),
              'c_compiler': provenance(args.c_compiler, args.timeout),
              'compilers': {tag: provenance(compiler, args.timeout) for tag, compiler in compilers},
              'budgets': {'command_seconds': args.timeout, 'search_seconds': args.search_seconds, 'search_states': args.max_states},
              'semantics': {'status': 'not_run'}, 'max_rss': None, 'rows': []}
    report['emission'] = args.emit
    if args.semantic_probe:
        report['evaluation']['probe_metadata'] = 'hashed-probe-json-v1'
    report['c_footprint'] = {'metric': cf.METRIC, 'enabled': args.c_footprint,
                            'scope': 'C syntax counts and local-binding fingerprints; not a semantic distance.'}
    if args.c_footprint:
        report['evaluation']['c_footprint_sha256'] = digest(cf.__file__)
    report['state_memory_sites'] = {'metric': sm.METRIC, 'enabled': args.state_memory_sites,
                                  'scope': 'Static state[4] byte-range sites; unknown roots and indices retained.'}
    if args.state_memory_sites:
        report['evaluation']['state_memory_sha256'] = digest(sm.__file__)
    report['semantic_probe'] = provenance(args.semantic_probe, args.timeout) if args.semantic_probe else None
    report['state_values'] = {'model': sv.MODEL, 'enabled': args.state_values,
                              'scope': 'C model return/state bytes for valid state[4]; checked helper contracts.'}
    if args.state_values:
        report['evaluation']['state_values_modules'] = sv.implementation()
        report['state_values']['solver'] = provenance(args.value_solver, args.timeout)
        report['budgets']['value_solver_seconds'] = args.value_seconds
    if args.semantic_inputs:
        if not args.semantic_probe:
            raise ValueError('semantic input rows require --semantic-probe')
        text = args.semantic_inputs.read_text()
        rows = [line.split() for line in text.splitlines()]
        if (len(rows) != args.semantic_cases or any(len(row) != 4 or any(not word.isascii() or not word.isdecimal() or not 0 <= int(word) < 2**64 for word in row) for row in rows)):
            raise ValueError('semantic input file must match the declared four-word vector count')
        report['semantic_inputs'] = {'path': str(args.semantic_inputs.resolve()), 'sha256': digest(args.semantic_inputs)}
    report['budgets'].update(semantic_seed=args.semantic_seed, semantic_vectors=args.semantic_cases,
                             low_step_limit=args.semantic_steps)
    report['resources'] = {'enabled': args.measure_rss, 'unit': 'KiB',
                           'scope': 'per-command largest process, not concurrent aggregate RSS'}
    report['host'] = {'machine': platform.machine(), 'platform': platform.platform(),
                      'cpu_affinity': sorted(os.sched_getaffinity(0))}
    cpu = Path('/proc/cpuinfo')
    if cpu.is_file():
        for line in cpu.read_text().splitlines():
            key, separator, value = line.partition(':')
            if separator and key.strip() in ['model name', 'flags']:
                report['host'].setdefault(key.strip().replace(' ', '_'), value.strip())
    report['time_tool'] = provenance('/usr/bin/time', args.timeout) if args.measure_rss else None
    if args.toolchain_manifest:
        report['toolchain_manifest'] = {'path': str(args.toolchain_manifest.resolve()),
                                        'sha256': digest(args.toolchain_manifest),
                                        'manifest': json.loads(args.toolchain_manifest.read_text())}
    for case in cases:
        for tag, compiler in compilers:
            for opt in opts:
                row = measure(case, tag, compiler, opt, args, out)
                report['rows'].append(row)
                # Retain completed rows even if the caller interrupts a later profile.
                (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    report['summary'] = {'requested': len(report['rows']),
                         'status': dict(Counter(r['status'] for r in report['rows'])),
                         'failures_by_stage': dict(Counter(f['stage'] for r in report['rows'] for f in r.get('failures', []))),
                         'distances': dict(Counter(r['distance']['status'] for r in report['rows'] if 'distance' in r)),
                         'cohorts': dict(Counter(r['cohort'] for r in report['rows']))}
    report['semantics'] = {'status': 'reported' if args.semantic_probe else 'not_run',
                           'contract': semantics.CONTRACT if args.semantic_probe else None,
                           'counts': dict(Counter(r['semantics']['status'] for r in report['rows']))}
    report['summary']['architecture'] = dict(Counter(r.get('stage_checks', {}).get('status', 'not_run') for r in report['rows']))
    report['summary']['c_footprint'] = dict(Counter(r['c_footprint']['status'] for r in report['rows']))
    report['summary']['state_memory_sites'] = dict(Counter(r['state_memory_sites']['status'] for r in report['rows']))
    report['summary']['state_values'] = dict(Counter(r['state_values']['status'] for r in report['rows']))
    report['resources']['runner_peak_rss_kib'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases', type=Path, default=ROOT / 'tools/corpora/structure-smoke.json')
    parser.add_argument('--decompiler', type=Path, default=ROOT / 'target/debug/nirvana')
    parser.add_argument('--compiler', action='append', help='TAG=EXECUTABLE; repeat for each binary-producing compiler')
    parser.add_argument('--c-compiler', default='cc', help='fixed compiler for all generated C profiles')
    parser.add_argument('--emit', choices=['readable-c', 'middle-c'], default='readable-c')
    parser.add_argument('--semantic-probe', type=Path, help='built examples/evaluation_probe executable')
    parser.add_argument('--c-footprint', action='store_true', help='observe C operators, literals and condition syntax using Clang AST JSON')
    parser.add_argument('--state-memory-sites', action='store_true', help='align static memory sites through the fixed state[4] ABI; requires C AST and semantic probe')
    parser.add_argument('--state-values', action='store_true', help='compare supported C state values with SMT; requires --state-memory-sites')
    parser.add_argument('--value-solver', default=os.environ.get('NIRVANA_Z3', 'z3'))
    parser.add_argument('--value-seconds', type=float, default=2, help='state value solver seconds per invocation')
    parser.add_argument('--semantic-inputs', type=Path, help='fixed four-word input rows; use matching --semantic-cases')
    parser.add_argument('--semantic-seed', type=int, default=0x6e697276616e6130)
    parser.add_argument('--semantic-cases', type=int, default=16)
    parser.add_argument('--semantic-steps', type=int, default=4096)
    parser.add_argument('--measure-rss', action='store_true', help='measure command process RSS via /usr/bin/time')
    parser.add_argument('--toolchain-manifest', type=Path)
    parser.add_argument('--clang', default=os.environ.get('NIRVANA_CLANG', 'clang'), help='evaluation CFG reader')
    parser.add_argument('--optimization', action='append', choices=['O0', 'O1', 'O2', 'O3', 'Os'])
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=15)
    parser.add_argument('--search-seconds', type=float, default=1)
    parser.add_argument('--max-states', type=int, default=100000)
    args = parser.parse_args()
    if not 0 < args.timeout < float('inf') or not 0 < args.search_seconds < float('inf') or args.max_states < 1:
        parser.error('require positive finite budgets')
    if not (0 <= args.semantic_seed < 2**64 and 8 <= args.semantic_cases <= 256 and 1 <= args.semantic_steps <= 1_000_000):
        parser.error('invalid semantic profile budgets')
    try:
        report = run(args)
    except (OSError, ValueError, KeyError) as error:
        parser.error(str(error))
    print(json.dumps(report['summary'], indent=2))


if __name__ == '__main__':
    main()
