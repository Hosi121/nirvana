"""Replay concrete selected-Semantic-IR state pairs, with explicit input scope."""
import itertools
import re

from .semantics import ProtocolError
from .state_record_codec import Decoder, EXTRA_FIELDS

MODEL = 'selected-semantic-state-pairs-v1'
FILENAME = 'selected-semantic-states.jsonl'
MAX_BYTES = 128 * 1024 * 1024
MAX_LINE_BYTES = 4 * 1024 * 1024
MAX_U64 = 2**64 - 1


def require(condition, message):
    if not condition:
        raise ProtocolError(message)


def u64(value):
    return type(value) is int and 0 <= value <= MAX_U64


def snapshot(value, registers, budget):
    fields = {'status', 'registers', 'memory_base', 'memory', 'instruction', 'trace'}
    require(isinstance(value, dict) and set(value) == fields, 'semantic state snapshot fields')
    words = value['registers']
    require(isinstance(words, list) and len(words) == registers and all(map(u64, words)),
            'semantic state register projection')
    require(u64(value['memory_base']) and value['memory_base'] == 4096
            and isinstance(value['memory'], list) and len(value['memory']) == 512
            and all(type(n) is int and 0 <= n <= 255 for n in value['memory']), 'semantic state RAM')
    status = value['status']
    require(isinstance(status, list) and len(status) == 4 and all(map(u64, status)), 'semantic state status')
    kind, _, access, width = status
    require(kind == 0 and access == width == 0
            or kind == 1 and access in [1, 2] and width in [1, 2, 4, 8]
            or status == [2, 0, 0, 0], 'semantic state status variant')
    require(value['instruction'] is None or u64(value['instruction']), 'semantic state PC')
    require(isinstance(value['trace'], list) and len(value['trace']) <= budget
            and all(map(u64, value['trace'])), 'semantic state instruction trace')


def memory(words, pointer):
    ram = [(i * 29 + 7) & 255 for i in range(512)]
    for index, word in enumerate(words):
        address = pointer + index * 8
        if address <= MAX_U64 and 4096 <= address <= 4096 + 512 - 8:
            ram[address - 4096:address - 4096 + 8] = word.to_bytes(8, 'little')
    return ram


def unique_object(pairs):
    result = dict(pairs)
    require(len(result) == len(pairs), 'duplicate semantic record key')
    return result


def validate(metadata, entry, evidence, budgets, requested, directory, machine_registers, *, retained=False):
    require(isinstance(metadata, dict) and set(metadata) <= {
                'model', 'file', 'sha256', 'rows', 'mismatches', 'input_binding'} | EXTRA_FIELDS
            and metadata.get('model') == MODEL and metadata.get('file') == FILENAME,
            'semantic state-pair model or filename')
    require(machine_registers == 32 and type(requested) is int and 0 < requested <= 768
            and requested % 3 == 0, 'semantic state-pair ABI profile')
    path = directory / FILENAME
    require(path.stat().st_size <= MAX_BYTES, 'semantic state-pair file budget')
    with (directory / evidence['input_ir']).open() as stream:
        header = re.fullmatch(r'entry=(\d+) registers=(\d+)\n', stream.readline(1024))
    require(header is not None and u64(int(header[1]))
            and int(header[2]) == evidence['source_registers'], 'semantic input IR header')
    codec = Decoder(metadata, int(header[2]), retained=retained, max_bytes=MAX_BYTES,
                    max_line_bytes=MAX_LINE_BYTES, object_pairs_hook=unique_object)
    native = directory / 'native-inputs.txt'
    require(native.stat().st_size <= 32768, 'semantic native input budget')
    try:
        vectors = [[int(n) for n in line.split()] for line in native.read_text().splitlines()]
    except ValueError as error:
        raise ProtocolError('semantic native input words') from error
    require(all(len(words) == 4 and all(map(u64, words)) for words in vectors), 'semantic native input shape')
    bound = len(vectors) * 3 == requested
    order = iter(itertools.product(range(requested), budgets, [0, MAX_U64]))
    rows = mismatches = 0
    with path.open('rb') as stream:
        while True:
            raw = stream.readline(MAX_LINE_BYTES + 1)
            if not raw:
                break
            require(len(raw) <= MAX_LINE_BYTES and raw.endswith(b'\n'), 'semantic state-pair row budget')
            row = codec.decode(raw)
            require(isinstance(row, dict) and set(row) == {'case', 'budget', 'fresh', 'input', 'expected', 'actual'},
                    'semantic state-pair fields')
            key = tuple(row[k] for k in ['case', 'budget', 'fresh'])
            require(all(type(n) is int for n in key) and key == next(order, None), 'semantic state-pair coverage order')
            case, budget, fresh = key
            pointer = [4224, 4592, MAX_U64][case % 3]
            initial = [0] * 32
            initial[4], initial[7] = 4600, pointer
            require(isinstance(row['input'], list) and all(map(u64, row['input']))
                    and row['input'] == initial, 'semantic state-pair machine input')
            for side in ['expected', 'actual']:
                snapshot(row[side], evidence['source_registers'], budget)
            if budget == 0:
                state = row['expected']
                require(state['registers'] == initial + [fresh] * (evidence['source_registers'] - 32)
                        and state['status'] == [2, 0, 0, 0] and not state['trace']
                        and state['instruction'] == int(header[1]), 'semantic initial input state')
                if bound:
                    require(state['memory'] == memory(vectors[case // 3], pointer), 'semantic initial RAM binding')
            mismatches += row['expected'] != row['actual']
            rows += 1
            require(mismatches == 0 or entry['status'] == 'counterexample' and mismatches == 1,
                    'semantic state-pair mismatch contradicts stage status')
            if mismatches:
                require(not stream.read(1), 'semantic state-pair continues after counterexample')
    require(rows == entry['observations']
            and (entry['status'] != 'passed' or rows == requested * len(budgets) * 2)
            and (entry['status'] != 'counterexample' or mismatches == 1), 'semantic state-pair count or status')
    observed = {'model': MODEL, 'file': FILENAME, **codec.summary(), 'rows': rows,
                'mismatches': mismatches, 'input_binding': 'native-vectors' if bound else 'stage-profile'}
    require(all(metadata[k] == v and type(metadata[k]) is type(v)
                for k, v in observed.items() if k in metadata), 'semantic state-pair retained summary')
    return observed
