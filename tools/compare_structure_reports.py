#!/usr/bin/env python3
"""Replay retained artifacts and compare M0 reports with matching inputs/contracts."""
import argparse
import json
from pathlib import Path
from evaluation.reports import compare


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('before', type=Path)
    parser.add_argument('after', type=Path)
    args = parser.parse_args()
    try:
        result = compare(args.before, args.after)
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.error(str(error))
    print(json.dumps(result, indent=2))
    if (result['semantic_regressions'] or result['structure_regressions']
            or result['architecture_regressions'] or result['c_footprint_regressions']
            or result['structure'].get('regressed')):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
