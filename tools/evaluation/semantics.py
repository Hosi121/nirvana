"""Fixed ABI observations, kept separate from source/control-graph distance."""
import hashlib
import json
from pathlib import Path

CONTRACT = 'nirvana-fixture-state4-checked-v1'
FILES = ['generated-probe.c', 'generated-inputs.txt', 'generated-expected.txt',
         'native-probe.c', 'native-inputs.txt', 'native-expected.txt']


class ProtocolError(ValueError):
    pass


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def compare(expected, actual, inputs, width):
    """Compare complete words, including every RAM byte; hashes are provenance."""
    def parse(text):
        rows = []
        for line in text.splitlines():
            try:
                words = [int(word) for word in line.split()]
            except ValueError as error:
                raise ProtocolError('observer emitted a noninteger word') from error
            if len(words) != width or any(not 0 <= w < 2**64 for w in words):
                raise ProtocolError('observer width or integer range mismatch')
            rows.append(words)
        return rows
    wanted, got = parse(expected), parse(actual)
    source = inputs.splitlines()
    if len(wanted) != len(got) or len(wanted) != len(source):
        raise ProtocolError('observer/input row count mismatch')
    for index, (a, b) in enumerate(zip(wanted, got)):
        if a != b:
            return {'status': 'counterexample', 'case_index': index, 'input': source[index],
                    'expected': a, 'actual': b, 'cases': len(wanted)}
    return {'status': 'passed', 'cases': len(wanted)}


def run(args, row, directory, invoke, flags):
    """invoke records real commands, timeouts, stdout/stderr and optional RSS."""
    destination = directory / 'semantics'
    argv = [args.semantic_probe, directory / 'input.o', directory / 'readable.c',
                     destination, row['function'], args.emit, args.semantic_seed,
                     args.semantic_cases, args.semantic_steps]
    input_file = getattr(args, 'semantic_inputs', None)
    if input_file:
        argv.append(input_file)
    if getattr(args, 'loop_solver', None):
        argv.extend(['--recover-loops', args.loop_solver])
    result = invoke(argv, 'semantic_prepare')
    try:
        profile = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise ProtocolError('invalid semantic probe JSON') from error
    if (not isinstance(profile, dict) or profile.get('schema') != 'nirvana-evaluation-probe-v1'
            or profile.get('generator') != ('fixture-state4-input-file-v1' if input_file else 'fixture-state4-seeds-v1')
            or profile.get('vectors') != args.semantic_cases
            or profile.get('seed') != args.semantic_seed
            or profile.get('step_limit') != args.semantic_steps
            or profile.get('requested_cases') != args.semantic_cases * 3
            or profile.get('memory_base') != 4096 or profile.get('memory_size') != 512
            or profile.get('state_pointer') != 4224 or profile.get('stack_pointer') != 4600
            or profile.get('row_words') != 69):
        raise ProtocolError('semantic probe profile mismatch')
    counts = [profile.get(k) for k in ['returned', 'read_faults', 'write_faults', 'suspended']]
    native_cases = profile.get('native_cases')
    if (any(not isinstance(n, int) or isinstance(n, bool) or n < 0 for n in counts)
            or sum(counts) != profile['requested_cases']
            or sum(counts[:3]) != profile.get('checked_cases')
            or not isinstance(native_cases, int) or isinstance(native_cases, bool)
            or not 0 <= native_cases <= args.semantic_cases):
        raise ProtocolError('semantic probe coverage mismatch')
    from . import stages
    stages.attach(profile.pop('stage_checks', None), row, destination, args.semantic_steps,
                  profile['requested_cases'], profile.get('register_count'))
    from . import loop_recovery
    loop_recovery.attach(profile.pop('loop_recovery', None), row, destination,
                         profile['requested_cases'], args.semantic_steps,
                         required=bool(getattr(args, 'loop_solver', None)))
    row['semantics'] = {'status': 'running', 'contract': CONTRACT, 'profile': profile,
                        'prepare_stdout_sha256': hashlib.sha256(result.stdout.encode()).hexdigest(),
                        'native_observations': 'return and state[4], valid pointer',
                        'generated_observations': 'return, all RAM words, first fault address/access/width',
                        'inputs': {name: sha(destination / name) for name in FILES}, 'checks': {}}
    native_inputs = (destination / 'native-inputs.txt').read_text()
    native_expected = (destination / 'native-expected.txt').read_text()
    c_inputs = (destination / 'generated-inputs.txt').read_text()
    c_expected = (destination / 'generated-expected.txt').read_text()
    if (len(native_expected.splitlines()) != profile['native_cases']
            or len(c_expected.splitlines()) != profile['checked_cases']):
        raise ProtocolError('semantic probe expected-row coverage mismatch')
    commands = [
        ('native', [args.c_compiler, *flags, '-O2', destination / 'native-probe.c',
                    directory / 'input.o', '-o', destination / 'native-probe'],
         native_inputs, native_expected, 5),
    ]
    for opt in ['O0', 'O2']:
        commands.append((f'generated_{opt}',
                         [args.c_compiler, *flags, f'-{opt}', '-fsanitize=undefined',
                          '-fno-sanitize-recover=undefined', destination / 'generated-probe.c',
                          '-o', destination / f'generated-{opt}'], c_inputs, c_expected, 69))
    for label, argv, inputs, expected, width in commands:
        invoke(argv, f'{label}_compile')
        observed = invoke([argv[-1]], f'{label}_run', input=inputs)
        check = compare(expected, observed.stdout, inputs, width)
        row['semantics']['checks'][label] = check
    row['semantics']['status'] = ('counterexample' if any(c['status'] == 'counterexample' for c in row['semantics']['checks'].values())
                                  else 'passed' if profile['suspended'] == 0
                                  and profile['native_cases'] == args.semantic_cases else 'inconclusive')
