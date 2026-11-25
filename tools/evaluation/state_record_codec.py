"""Lossless register tokens for existing full-state JSON Lines observations.

Only the two snapshot register values can be encoded. The decoded digest uses
the original row bytes with those tokens restored to Rust Vec Debug spelling;
other fields, whitespace and strings are never serialized again.
"""
import hashlib
import json
import re

from .semantics import ProtocolError

ENCODING = 'register-rle-u64-v1'
EXTRA_FIELDS = {'encoding', 'decoded_bytes', 'decoded_sha256'}
MAX_U64 = 2**64 - 1


def require(condition, message):
    if not condition:
        raise ProtocolError(message)


def unique_object(pairs):
    result = dict(pairs)
    require(len(result) == len(pairs), 'duplicate state-record key')
    return result


def u64(value):
    return type(value) is int and 0 <= value <= MAX_U64


class Decoder:
    def __init__(self, metadata, registers, *, retained=False,
                 max_bytes=128 * 1024 * 1024, max_line_bytes=4 * 1024 * 1024,
                 object_pairs_hook=unique_object):
        require(isinstance(metadata, dict), 'state-record metadata')
        require(type(registers) is int and 0 <= registers <= 1_000_000,
                'state-record source register quota')
        self.encoding = metadata.get('encoding') if 'encoding' in metadata else None
        self.registers = registers
        self.max_bytes, self.max_line_bytes = max_bytes, max_line_bytes
        self.hook = object_pairs_hook
        self.physical = hashlib.sha256()
        self.logical = hashlib.sha256()
        self.physical_bytes = self.decoded_bytes = 0
        if 'encoding' not in metadata:
            require(not EXTRA_FIELDS.intersection(metadata), 'state-record encoding declaration')
        else:
            require(self.encoding == ENCODING, 'state-record encoding')
            require(type(metadata.get('decoded_bytes')) is int
                    and 0 <= metadata['decoded_bytes'] <= max_bytes,
                    'state-record decoded-byte metadata')
            if retained:
                require({'sha256', 'decoded_sha256', 'decoded_bytes'} <= metadata.keys(),
                        'retained state-record digests required')
            for key in ['sha256', 'decoded_sha256']:
                if key in metadata:
                    require(type(metadata[key]) is str
                            and re.fullmatch('[0-9a-f]{64}', metadata[key]) is not None,
                            'state-record digest metadata')

    def decode(self, raw):
        require(len(raw) <= self.max_line_bytes and raw.endswith(b'\n'), 'state-record physical row budget')
        require(self.physical_bytes + len(raw) <= self.max_bytes, 'state-record physical file budget')
        try:
            row = json.loads(raw, object_pairs_hook=self.hook)
        except (ValueError, RecursionError) as error:
            raise ProtocolError('state-record JSON') from error
        if self.encoding is None:
            # Preserve old dense-only behavior and metadata shape. Snapshot
            # validation by the caller rejects any undeclared RLE object.
            restored = raw
        else:
            restored = self._restore(raw, row)
        require(self.decoded_bytes + len(restored) <= self.max_bytes,
                'state-record decoded file budget')
        self.physical.update(raw)
        self.logical.update(restored)
        self.physical_bytes += len(raw)
        self.decoded_bytes += len(restored)
        return row

    def summary(self):
        result = {'sha256': self.physical.hexdigest()}
        if self.encoding is not None:
            result.update(encoding=ENCODING, decoded_bytes=self.decoded_bytes,
                          decoded_sha256=self.logical.hexdigest())
        return result

    def _restore(self, raw, row):
        require(isinstance(row, dict) and all(isinstance(row.get(side), dict)
                and 'registers' in row[side] for side in ['expected', 'actual']),
                'state-record snapshot objects')
        try:
            text = raw.decode('utf-8')
            decoder = json.JSONDecoder(object_pairs_hook=self.hook)
            top = dict(_members(text, 0, decoder))
            plans = []
            for side in ['expected', 'actual']:
                start, _ = top[side]
                start, end = dict(_members(text, start, decoder))['registers']
                payload, stop = decoder.raw_decode(text, start)
                require(stop == end and payload == row[side]['registers'],
                        'state-record register token correspondence')
                runs, size = _plan(payload, self.registers)
                token = text[start:end]
                if isinstance(payload, dict):
                    require(token == json.dumps(payload, separators=(',', ':')),
                            'state-record canonical RLE token')
                    require(len(token) < size, 'state-record RLE token is not smaller')
                # A register token consists entirely of ASCII JSON integers
                # and punctuation once the plan above has been checked.
                plans.append((side, start, end, runs, size))
            restored_size = len(raw) + sum(size - (end - start) for _, start, end, _, size in plans)
            require(restored_size <= self.max_line_bytes, 'state-record decoded row budget')
            require(self.decoded_bytes + restored_size <= self.max_bytes,
                    'state-record decoded file budget')
            # Both dimensions and the TOTAL logical row/file budget precede
            # every run expansion, including when both individual sides fit.
            replacements = []
            for side, start, end, runs, size in plans:
                values = [value for count, value in runs for _ in range(count)]
                token = '[' + ', '.join(map(str, values)) + ']'
                require(len(token) == size, 'state-record decoded token size')
                if isinstance(row[side]['registers'], list):
                    require(text[start:end] == token, 'state-record canonical dense token')
                row[side]['registers'] = values
                byte_start = len(text[:start].encode('utf-8'))
                replacements.append((byte_start, byte_start + end - start, token.encode('ascii')))
            result, cursor = [], 0
            for start, end, token in sorted(replacements):
                require(cursor <= start <= end <= len(raw), 'state-record token spans')
                result.extend([raw[cursor:start], token])
                cursor = end
            result.append(raw[cursor:])
            restored = b''.join(result)
            require(len(restored) == restored_size, 'state-record restored byte count')
            return restored
        except ProtocolError:
            raise
        except (ValueError, RecursionError, KeyError, UnicodeError) as error:
            raise ProtocolError('state-record token JSON') from error


def _plan(payload, registers):
    if isinstance(payload, list):
        require(len(payload) == registers and all(map(u64, payload)), 'state-record dense register quota')
        runs = [(1, value) for value in payload]
    else:
        require(isinstance(payload, dict) and set(payload) == {'rle'}
                and isinstance(payload['rle'], list), 'state-record RLE fields')
        runs, total, previous = [], 0, None
        for run in payload['rle']:
            require(isinstance(run, list) and len(run) == 2 and type(run[0]) is int
                    and 0 < run[0] <= registers and u64(run[1]), 'state-record RLE run')
            count, value = run
            total += count
            require(total <= registers and value != previous, 'state-record RLE quota or nonmaximal runs')
            runs.append((count, value))
            previous = value
        require(total == registers, 'state-record RLE source register quota')
    size = 2 + sum(count * len(str(value)) for count, value in runs)
    if registers:
        size += 2 * (registers - 1)
    return runs, size


def _members(text, start, decoder):
    """Locate object value spans by bounded JSON token decoding, never regex."""
    def whitespace(index):
        while index < len(text) and text[index] in ' \t\r\n':
            index += 1
        return index
    cursor = whitespace(start)
    require(cursor < len(text) and text[cursor] == '{', 'state-record object token')
    cursor = whitespace(cursor + 1)
    if cursor < len(text) and text[cursor] == '}':
        return
    while cursor < len(text):
        key, cursor = decoder.raw_decode(text, cursor)
        require(type(key) is str, 'state-record key token')
        cursor = whitespace(cursor)
        require(cursor < len(text) and text[cursor] == ':', 'state-record colon token')
        start = whitespace(cursor + 1)
        _, end = decoder.raw_decode(text, start)
        yield key, (start, end)
        cursor = whitespace(end)
        require(cursor < len(text) and text[cursor] in ',}', 'state-record object delimiter')
        if text[cursor] == '}':
            return
        cursor = whitespace(cursor + 1)
    raise ProtocolError('state-record incomplete object')
