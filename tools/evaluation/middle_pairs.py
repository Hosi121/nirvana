"""Replay MIR memory/saved-value transitions at the original machine state."""
import hashlib
import itertools
import json
import re

from . import semantic_pairs as pairs
from .semantics import ProtocolError

MODEL = 'middle-state-pairs-v1'


def validate(metadata, entry, evidence, budgets, requested, directory, registers):
    require = pairs.require
    filename = entry['name'] + '.states.jsonl'
    require(isinstance(metadata, dict) and set(metadata) <= {
                'model', 'file', 'sha256', 'rows', 'mismatches', 'input_binding'}
            and metadata.get('model') == MODEL and metadata.get('file') == filename,
            'MIR state-pair metadata')
    require(registers == 32 and type(requested) is int and 0 < requested <= 768 and requested % 3 == 0,
            'MIR state-pair input profile')
    path = directory / filename
    require(path.stat().st_size <= pairs.MAX_BYTES, 'MIR state-pair file budget')
    with (directory / evidence['input_ir']).open() as stream:
        header = re.fullmatch(r'entry=(\d+) registers=(\d+)\n', stream.readline(1024))
    require(header is not None and pairs.u64(int(header[1])) and int(header[2]) == registers,
            'MIR input IR header')
    native = directory / 'native-inputs.txt'
    require(native.stat().st_size <= 32768, 'MIR native input budget')
    try:
        vectors = [[int(n) for n in line.split()] for line in native.read_text().splitlines()]
    except ValueError as error:
        raise ProtocolError('MIR native input words') from error
    require(all(len(words) == 4 and all(map(pairs.u64, words)) for words in vectors), 'MIR native input shape')
    bound = len(vectors) * 3 == requested
    order = iter(itertools.product(range(requested), budgets, entry['comparisons']))
    digest = hashlib.sha256()
    rows = mismatches = 0
    with path.open('rb') as stream:
        while raw := stream.readline(pairs.MAX_LINE_BYTES + 1):
            require(len(raw) <= pairs.MAX_LINE_BYTES and raw.endswith(b'\n'), 'MIR state-pair row budget')
            digest.update(raw)
            try:
                row = json.loads(raw, object_pairs_hook=pairs.unique_object)
            except (ValueError, RecursionError) as error:
                raise ProtocolError('MIR state-pair JSON') from error
            require(isinstance(row, dict) and set(row) == {'case', 'budget', 'variant', 'input', 'expected', 'actual'},
                    'MIR state-pair fields')
            key = tuple(row[k] for k in ['case', 'budget', 'variant'])
            require(type(key[0]) is int and type(key[1]) is int and type(key[2]) is str
                    and key == next(order, None), 'MIR state-pair coverage order')
            case, budget, _ = key
            pointer = [4224, 4592, pairs.MAX_U64][case % 3]
            initial = [0] * 32
            initial[4], initial[7] = 4600, pointer
            require(isinstance(row['input'], list) and all(map(pairs.u64, row['input']))
                    and row['input'] == initial, 'MIR machine input')
            for side in ['expected', 'actual']:
                pairs.snapshot(row[side], registers, budget)
            if budget == 0:
                state = row['expected']
                require(state['registers'] == initial and state['status'] == [2, 0, 0, 0]
                        and not state['trace'] and state['instruction'] == int(header[1]), 'MIR initial machine state')
                if bound:
                    require(state['memory'] == pairs.memory(vectors[case // 3], pointer), 'MIR initial RAM binding')
            mismatches += row['expected'] != row['actual']
            rows += 1
            require(mismatches == 0 or entry['status'] == 'counterexample' and mismatches == 1,
                    'MIR state-pair mismatch contradicts status')
            if mismatches:
                require(not stream.read(1), 'MIR state-pair continues after counterexample')
    require(rows == entry['observations']
            and (entry['status'] != 'passed' or rows == requested * len(budgets) * len(entry['comparisons']))
            and (entry['status'] != 'counterexample' or mismatches == 1), 'MIR state-pair count or status')
    observed = {'model': MODEL, 'file': filename, 'sha256': digest.hexdigest(), 'rows': rows,
                'mismatches': mismatches, 'input_binding': 'native-vectors' if bound else 'stage-profile'}
    require(all(metadata[k] == v and type(metadata[k]) is type(v)
                for k, v in observed.items() if k in metadata), 'MIR retained state-pair summary')
    return observed
