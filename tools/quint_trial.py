#!/usr/bin/env python3
"""Run the finite structured-controller trial in a managed temporary directory."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tarfile
import urllib.request
import shutil
import re
import socket
import time
import platform

ROOT = Path(__file__).resolve().parents[1]

QUINT_VERSION = '0.34.0'
QUINT_SHA256 = '5091d7d1ea944e794d9106c7e62e3b844d70f77ddbbcbb4feb5ee5a6025b5ac7'
APALACHE_VERSION = '0.62.4'
APALACHE_SHA256 = 'b781b53bba32fac14ac2e02b0332e1dc2edc64cb7b850c0608d8142cc7aa2ef4'
JAVA_VERSION = '21.0.13.1+2-1~24.04.1'
JAVA_SHA256 = '18d6aabaf7232290322d53afff075e412d93832253dd9fc2c769d5579362e9ba'


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def fetch(url, path, expected):
    with urllib.request.urlopen(url, timeout=60) as source, path.open('wb') as dest:
        while chunk := source.read(1024 * 1024):
            dest.write(chunk)
    if sha(path) != expected:
        raise ValueError(f'checksum mismatch: {path.name}')
    return {'url': url, 'sha256': expected, 'bytes': path.stat().st_size}


def bootstrap(out):
    """Pinned Linux x86-64 tools; all downloads/configuration stay inside out."""
    if platform.system() != 'Linux' or platform.machine() not in ('x86_64', 'amd64') or not shutil.which('dpkg-deb'):
        raise RuntimeError('bootstrap requires Linux x86-64 and dpkg-deb; otherwise supply --quint')
    out.mkdir(parents=True, exist_ok=True)
    tools = out / 'toolchain'
    tools.mkdir()
    quint = tools / 'quint'
    records = {'quint': fetch(
        f'https://github.com/quint-co/quint/releases/download/v{QUINT_VERSION}/quint-linux-amd64',
        quint, QUINT_SHA256)}
    quint.chmod(0o755)
    deb = tools / 'java.deb'
    records['java'] = fetch(
        'https://archive.ubuntu.com/ubuntu/pool/main/o/openjdk-21/'
        f'openjdk-21-jre-headless_{JAVA_VERSION}_amd64.deb', deb, JAVA_SHA256)
    java_root = tools / 'java-root'
    subprocess.run(['dpkg-deb', '-x', str(deb), str(java_root)], check=True, timeout=60)
    java = java_root / 'usr/lib/jvm/java-21-openjdk-amd64'
    for link in java.rglob('*'):
        if link.is_symlink() and str(link.readlink()).startswith('/etc/'):
            target = java_root / str(link.readlink()).lstrip('/')
            if target.exists():
                link.unlink()
                link.symlink_to(target)
    home = out / 'quint-home'
    dist = home / f'apalache-dist-{APALACHE_VERSION}'
    dist.mkdir(parents=True)
    prefix = f'https://github.com/apalache-mc/apalache/releases/download/v{APALACHE_VERSION}'
    archive = tools / 'apalache.tgz'
    records['apalache'] = fetch(f'{prefix}/apalache-{APALACHE_VERSION}.tgz', archive, APALACHE_SHA256)
    with tarfile.open(archive) as packed:
        packed.extractall(dist, filter='data')
    for download in [deb, archive]:
        download.unlink()
    temporary = out / 'tmp'
    temporary.mkdir()
    env = {**os.environ, 'QUINT_HOME': str(home), 'JAVA_HOME': str(java),
           'PATH': str(java / 'bin') + os.pathsep + os.environ['PATH'],
           'TMPDIR': str(temporary), 'JAVA_TOOL_OPTIONS': '-Xmx512m -Xss8m'}
    records['versions'] = {
        'quint': subprocess.check_output([str(quint), '--version'], text=True, env=env).strip(),
        'apalache': APALACHE_VERSION,
        'java': subprocess.run([str(java / 'bin/java'), '-version'], text=True,
                               capture_output=True, env=env, check=True).stderr.strip(),
    }
    (out / 'toolchain.json').write_text(json.dumps(records, indent=2) + '\n')
    return quint, env, records


def quint_value(value):
    if isinstance(value, dict):
        return '{' + ','.join(k + ':' + quint_value(v) for k, v in value.items()) + '}'
    if isinstance(value, list):
        return '[' + ','.join(map(quint_value, value)) + ']'
    return json.dumps(value)


def export(out, exporter, selected=(0, 1, 2, 9, 10, 11, 12, 13)):
    result = subprocess.run([str(exporter)], check=True, capture_output=True, text=True, timeout=20)
    data = json.loads(result.stdout)
    verdicts = [case['verdict'] for case in data['cases']]
    if verdicts != ['accepted'] * 3 + ['rejected'] * 5 + ['accepted'] * 6:
        raise ValueError(f'unexpected Rust acceptance gate: {verdicts}')
    (out / 'fixtures.json').write_text(result.stdout)
    (out / 'fixtures.qnt').write_text(
        'module fixtures { pure val selected = Set(' + ','.join(map(str, selected)) + ')\n'
        'pure val cases = ' + quint_value(data['cases']) + ' }\n')
    shutil.copy2(ROOT / 'models/structured_events.qnt', out / 'structured_events.qnt')
    config = out / 'tlc.json'
    config.write_text(json.dumps({'maxHeap': '-Xmx512m', 'stackSize': '-Xss8m', 'workers': 1}))
    return data


def trial(out, quint, env, toolchain):
    out.mkdir(parents=True, exist_ok=True)
    # Each trial owns its translation server rather than reusing a local one.
    with socket.socket() as listener:
        listener.bind(('127.0.0.1', 0))
        port = listener.getsockname()[1]
    checks = []

    def call(name, command, *, cwd=out, timeout=180):
        started = time.monotonic()
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                capture_output=True, timeout=timeout)
        text = result.stdout + result.stderr
        (out / (name + '.log')).write_text(text)
        entry = {'name': name, 'command': list(map(str, command)),
                 'returncode': result.returncode, 'seconds': time.monotonic() - started,
                 'log_sha256': hashlib.sha256(text.encode()).hexdigest()}
        checks.append(entry)
        print(f'{name}: exit {result.returncode}', flush=True)
        return result, text, entry

    build, text, _ = call('build-exporter',
        ['python3', 'tools/dev.py', 'cargo', 'build', '--locked', '--example', 'structure_model'], cwd=ROOT)
    if build.returncode:
        raise RuntimeError(text)
    replay, text, _ = call('rust-replay', ['python3', 'tools/dev.py', 'cargo', 'test', '--lib',
        'control_flow::structure::model_trial_tests::exported_trial_candidates_replay_through_real_validator_and_executor',
        '--', '--exact', '--nocapture'], cwd=ROOT)
    if replay.returncode or '1 passed; 0 failed' not in text:
        raise RuntimeError('Rust replay did not pass exactly one test: ' + text)
    exporter = ROOT / 'target/debug/examples/structure_model'
    data = export(out, exporter)
    query = ['verify', str(out / 'structured_events.qnt'), '--backend=tlc',
             f'--apalache-version={APALACHE_VERSION}', f'--server-endpoint=localhost:{port}',
             '--tlc-config=' + str(out / 'tlc.json'), '--verbosity=4']
    good, text, positive = call('positive-tlc', [str(quint), *query])
    if good.returncode or 'Model checking completed. No error has been found.' not in text:
        raise RuntimeError('finite TLC search did not complete: ' + text)
    counts = re.search(r'(\d+) states generated, (\d+) distinct states found, (\d+) states left on queue', text)
    if not counts or int(counts[3]) != 0:
        raise RuntimeError('TLC did not exhaust its state queue')
    positive['generated_states'], positive['distinct_states'], _ = map(int, counts.groups())

    sim, text, observations = call('terminal-observations', [str(quint), 'run',
        str(out / 'structured_events.qnt'), '--backend=typescript', '--max-samples=1000',
        '--max-steps=60', '--seed=0x4e495256414e41', '--verbosity=2'])
    counts = dict(re.findall(r'(returned|faulted|suspended) was observed in (\d+) trace', text))
    if sim.returncode or set(counts) != {'returned', 'faulted', 'suspended'} or not all(int(n) for n in counts.values()):
        raise RuntimeError('nonempty terminal observations missing: ' + text)
    observations['observations'] = {k: int(v) for k, v in counts.items()}

    expected = ['step-pc', 'step-pc', 'condition-evaluation', 'step-pc',
                'ordered-body', 'budget-before-control']
    for index, reason in zip(range(3, 9), expected):
        directory = out / f'negative-{index}'
        directory.mkdir()
        export(directory, exporter, (index,))
        query[1] = str(directory / 'structured_events.qnt')
        result, text, entry = call(data['cases'][index]['name'], [str(quint), *query])
        found = re.findall(r'reason \|-> "([^"]+)"', text)
        if (not result.returncode or '[violation]' not in text
                or 'Error: Invariant ' not in text or not found or found[-1] != reason):
            raise RuntimeError('expected semantic counterexample, got: ' + text)
        entry.update(case=index, rust_verdict=data['cases'][index]['verdict'], reason=reason)
        start = text.index('Error: Invariant ')
        end = text.index('\nFinished in ', start)
        entry['counterexample'] = text[start:end]

    inputs = ['models/structured_events.qnt', 'examples/structure_model.rs',
              'tests/support/formal_structure.rs', 'src/control_flow/structure/model_trial_tests.rs',
              'tools/quint_trial.py', 'src/control_flow/structure.rs', 'src/control_flow/structure_verify.rs',
              'src/model/ir.rs']
    return {'schema': 'nirvana-structured-events-trial-v1', 'milestone': 'M2 structure correspondence',
            'status': 'passed', 'toolchain': toolchain, 'checks': checks,
            'workspace_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
            'workspace_dirty': bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip()),
            'source_sha256': {p: sha(ROOT / p) for p in inputs},
            'exporter_sha256': sha(exporter), 'fixtures_sha256': sha(out / 'fixtures.json'),
            'bounds': {'positive_pairs': 8, 'budgets': [0, 6], 'max_loop_depth': 2, 'stack_guard': 8},
            'rust_replay': {'normal_pair_reports': 448, 'rejected_ast_mutations': 5,
                            'executor_mutation': 'model-only early-budget fault injection; real executor passes'},
            'limits': ['Finite exported family, not an unbounded proof of the recovery algorithm.',
                       'Event tokens assume shared deterministic primitive semantics; only the designated condition Load may fault.',
                       'Symbolic branch outcomes overapproximate concrete data; Rust replay finds concrete witnesses per AST mutation, not automated TLC-trace concretization.',
                       'MemorySSA, module CALL, native ISA lifting and arithmetic are separate contracts.']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--quint', type=Path, help='Use an installed Quint0.34.0 and existing Java/Apalache environment')
    args = parser.parse_args()
    out = args.out.resolve()
    if args.quint:
        quint, env = args.quint.resolve(), dict(os.environ)
        toolchain = {'quint_version': subprocess.check_output([str(quint), '--version'], text=True).strip(),
                     'quint_sha256': sha(quint), 'apalache_version': APALACHE_VERSION}
        if toolchain['quint_version'] != QUINT_VERSION:
            raise ValueError('trial requires Quint' + QUINT_VERSION)
        home = Path(env.get('QUINT_HOME', Path.home() / '.quint'))
        jar = home / f'apalache-dist-{APALACHE_VERSION}/apalache/lib/apalache.jar'
        if jar.exists():
            toolchain['apalache_jar_sha256'] = sha(jar)
    else:
        quint, env, toolchain = bootstrap(out)
    report = trial(out, quint, env, toolchain)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Passed; report: {args.report}', flush=True)


if __name__ == '__main__':
    main()
