#!/usr/bin/env python3
"""Replay saved loop-cut obligations and optionally regenerate them in Rust."""
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def artifact(checkpoint, name, seen=frozenset()):
    key = (checkpoint.resolve(), name)
    if key in seen:
        raise ValueError('cyclic artifact reference')
    record = json.loads(checkpoint.read_text())['review_artifacts'][name]
    if 'text' in record:
        value = record['text']
    else:
        referenced = (checkpoint.parent / record['checkpoint']).resolve()
        if not referenced.is_relative_to(checkpoint.parent.resolve()):
            raise ValueError('artifact reference leaves the checkpoint directory')
        value = artifact(referenced, record.get('artifact', name), seen | {key})
    if digest(value.encode()) != record['sha256']:
        raise ValueError(f'artifact hash mismatch: {name}')
    return value


def solve(solver, text, seconds):
    if seconds <= 0:
        return 'unknown-budget'
    script = (f'(set-option :timeout {max(1, int(seconds * 1000))})\n'
              '(set-option :produce-models true)\n'
              '(set-option :pp.bv-literals true)\n'
              + text + '\n(check-sat)\n')
    try:
        result = subprocess.run(
            [str(solver), '-in', '-smt2'], input=script, capture_output=True,
            text=True, timeout=seconds + 0.3)
    except subprocess.TimeoutExpired:
        return 'unknown-timeout'
    status = result.stdout.strip()
    if result.returncode or result.stderr or status not in {'sat', 'unsat', 'unknown'}:
        return 'solver-failure'
    return status


def rust_regeneration(args, checkpoint, texts, solver):
    for path, expected in checkpoint['source_sha256'].items():
        source = (ROOT / path).resolve()
        if not source.is_relative_to(ROOT) or digest(source.read_bytes()) != expected:
            raise ValueError(f'Rust regeneration needs the checkpoint source: {path}')
    output = args.out / 'rust'
    env = os.environ | {
        'NIRVANA_REGION_OBJECT': str((args.out / 'input.o').resolve()),
        'NIRVANA_REGION_OUTPUT': str(output.resolve()),
        'NIRVANA_Z3': str(solver),
        'NIRVANA_REQUIRE_ROLL_PROOF': '1',
    }
    command = [
        'python3', 'tools/dev.py', 'cargo', 'test', '--test', 'verification',
        'actual_compiler_loop_', '--', '--ignored', '--nocapture', '--test-threads=1',
    ]
    result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)
    log = result.stdout + result.stderr
    (args.out / 'rust.log').write_text(log)
    record = {'rust_returncode': result.returncode}
    if result.returncode == 0:
        same = all((output / name).exists()
                   and digest((output / name).read_bytes()) == digest(value.encode())
                   for name, value in texts.items())
        record['rust_artifacts_match'] = same
        if not same:
            raise ValueError('regenerated artifacts differ from the checkpoint')
    if args.report:
        args.report.with_suffix('.rust.log').write_text(log)
    return record


def replay_obligations(checkpoint, texts, solver):
    layout = checkpoint.get('proof_artifacts', {})
    if not isinstance(layout, dict):
        raise ValueError('checkpoint proof layout must be an object')
    completion_name = layout.get('completion', 'automatic-complete.smt2')
    comparison_name = layout.get('comparison', 'automatic-compare.smt2')
    entry = layout.get('entry_invariants')
    if checkpoint['schema'] == 'nirvana-inductive-loop-m2-v1':
        if set(layout) != {'completion', 'comparison', 'entry_invariants'} or not isinstance(entry, dict) or set(entry) != {'base', 'feedback'}:
            raise ValueError('inductive checkpoint must retain both entry obligations')
    elif checkpoint['schema'] not in ['nirvana-compositional-roll-m2-v1', 'nirvana-contextual-loop-m2-v1'] or layout:
        raise ValueError('unsupported checkpoint proof layout')
    names = [completion_name, comparison_name] + (list(entry.values()) if entry else [])
    obligations = checkpoint['cut_obligations']
    if not 1 <= len(obligations) <= 48:
        raise ValueError('checkpoint cut obligation budget')
    names += [obligation['artifact'] for obligation in obligations]
    if any(not isinstance(name, str) or name not in texts for name in names) or len(set(names)) != len(names):
        raise ValueError('checkpoint proof artifacts must be distinct and present')
    if digest(texts[comparison_name].encode()) != checkpoint['comparison_partitions']['property_sha256']:
        raise ValueError('flat comparison must use the retained property')
    start = time.monotonic()
    entry_results = []
    if entry is not None:
        deadline = time.monotonic() + 3
        for phase in ['base', 'feedback']:
            status = solve(solver, texts[entry[phase]], deadline - time.monotonic())
            entry_results.append({'phase': phase, 'status': status})
            if status != 'unsat':
                break
    entry_verified = entry is None or len(entry_results) == 2 and all(row['status'] == 'unsat' for row in entry_results)
    extension_deadline = time.monotonic() + 5
    completion = solve(solver, texts[completion_name], 5) if entry_verified else 'not-run'

    results = []
    if completion == 'unsat':
        deadline = extension_deadline if entry is not None else time.monotonic() + 15
        for obligation in checkpoint['cut_obligations']:
            status = solve(solver, texts[obligation['artifact']],
                           deadline - time.monotonic())
            results.append({'cut': obligation['cut'], 'kind': obligation['kind'],
                            'status': status})
            if status != 'unsat':
                break
    verified = (entry_verified and completion == 'unsat'
                and len(results) == len(checkpoint['cut_obligations'])
                and all(row['status'] == 'unsat' for row in results))
    return {
        'completion': completion,
        'entry_invariants': entry_results,
        'entry_invariants_all_unsat': entry_verified if entry is not None else None,
        'obligations': results,
        'total_obligations': len(checkpoint['cut_obligations']),
        'all_checkpoint_obligations_unsat': verified,
        'seconds': time.monotonic() - start,
        'scope': ('Saved source-bound decomposition under the original region contract. '
                  'Rust regeneration also checks the constructor, proof seals and C behavior. '
                  'SAT requires Rust replay and supplies no accepted certificate.'),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--checkpoint', type=Path,
                        default=ROOT / 'tools/corpora/compositional-roll-v1.m2.json')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--rust', action='store_true',
                        help='require the pinned sources, proof seal and generated-C tests')
    parser.add_argument('--flat', action='store_true',
                        help='also record the separate 15-second flat comparison')
    args = parser.parse_args()
    checkpoint = json.loads(args.checkpoint.read_text())
    if not checkpoint.get('cut_obligations'):
        parser.error('checkpoint must contain source-bound cut obligations')
    args.out.mkdir()
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
    texts = {name: artifact(args.checkpoint, name)
             for name in checkpoint['review_artifacts']}
    for name, value in texts.items():
        if Path(name).name != name:
            raise ValueError('artifact name must be a file name')
        (args.out / name).write_text(value)
    obj = base64.b64decode(checkpoint['input_object']['base64'], validate=True)
    if digest(obj) != checkpoint['input_object']['sha256']:
        raise ValueError('input object hash mismatch')
    (args.out / 'input.o').write_bytes(obj)
    solver_name = os.environ.get('NIRVANA_Z3', 'z3')
    solver = Path(shutil.which(solver_name) or solver_name).resolve()
    version = subprocess.check_output([str(solver), '-version'], text=True).strip()
    record = replay_obligations(checkpoint, texts, solver)
    record.update(solver_version=version, solver_file_sha256=digest(solver.read_bytes()))
    comparison_name = checkpoint.get('proof_artifacts', {}).get('comparison', 'automatic-compare.smt2')
    if args.flat:
        deadline = time.monotonic() + 15
        statuses = []
        for suffix in checkpoint['comparison_partitions']['suffixes']:
            status = solve(solver, texts[comparison_name] + suffix,
                           deadline - time.monotonic())
            statuses.append(status)
            if status != 'unsat':
                break
        record['flat_partitions'] = statuses
        record['flat_total'] = len(checkpoint['comparison_partitions']['suffixes'])
    if args.rust:
        record.update(rust_regeneration(args, checkpoint, texts, solver))
    if args.report:
        args.report.write_text(json.dumps(record, indent=2) + '\n')
    (args.out / 'replay.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))
    return 0 if record['all_checkpoint_obligations_unsat'] and record.get('rust_returncode', 0) == 0 else 2


if __name__ == '__main__':
    raise SystemExit(main())
