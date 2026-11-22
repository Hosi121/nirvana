"""Parse a binary's reported build identity; unknown is explicit.

This is build provenance, not an attestation of source-to-binary compilation.
The report separately retains the executable SHA256.
"""
import re

VERSION = re.compile(r'nirvana ([0-9A-Za-z.+-]+) git=([0-9a-f]{40}|[0-9a-f]{64}|unknown) source_dirty=(true|false|unknown)\Z')


def parse(tool):
    if (not isinstance(tool, dict) or type(tool.get('returncode')) is not int or tool['returncode'] != 0
            or not isinstance(tool.get('version'),str)): return None
    match = VERSION.fullmatch(tool.get('version', ''))
    if not match: return None
    package, revision, dirty = match.groups()
    return {'model': 'nirvana-rust-target-build-v1', 'package_version': package,
            'source_revision': None if revision == 'unknown' else revision,
            'source_dirty': {'true': True, 'false': False, 'unknown': None}[dirty]}
