#!/usr/bin/env python3
"""Refine graph distances using retained artifacts, keeping the original report."""
import argparse
import hashlib
import json
from pathlib import Path
from evaluation.reports import reanalyze


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('report', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--max-states', type=int)
    parser.add_argument('--search-seconds', type=float)
    args = parser.parse_args()
    if args.out.resolve().parent != args.report.resolve().parent or args.out.exists():
        parser.error('choose a new output filename beside the original report')
    try:
        result = reanalyze(args.report, max_states=args.max_states, seconds=args.search_seconds)
        result['reanalysis']['runner_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        with args.out.open('x') as output:
            output.write(json.dumps(result, indent=2) + '\n')
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.error(str(error))
    print(json.dumps(result['summary'], indent=2))


if __name__ == '__main__':
    main()
