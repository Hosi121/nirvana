#!/usr/bin/env python3
"""Compare retained linked-leaf profiles without executing their binaries."""
import argparse
import json
from pathlib import Path
from evaluation.module_profile import compare


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('before',type=Path);parser.add_argument('after',type=Path);args=parser.parse_args()
    try: result=compare(args.before,args.after)
    except (OSError,ValueError,TypeError,KeyError) as error: parser.error(str(error))
    print(json.dumps(result,indent=2))
    if result['regressions'] or result['candidate_errors']: raise SystemExit(1)


if __name__=='__main__': main()
