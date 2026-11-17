#!/usr/bin/env python3
"""UBSan-check retained original/readable C, comparing return + four words.

This does not feed instrumented objects to the decompiler. Full guest-memory
comparison against IR is performed by the Rust recovery tests before retention.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def invoke(command, *, data=None):
    result = subprocess.run(command, input=data, text=True, capture_output=True, timeout=10)
    if result.returncode or result.stderr:
        raise RuntimeError(f"{command!r}\n{result.stdout}\n{result.stderr}")
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path, default=Path("target/memory-recovery/generated"))
    parser.add_argument("--out", type=Path, default=Path("target/memory-recovery/ubsan"))
    parser.add_argument("--cc", default="cc")
    parser.add_argument("--inputs", type=Path, help="optional whitespace-separated rows of four unsigned words")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    args.out.mkdir(parents=True, exist_ok=True)
    inputs = []
    input_file = args.inputs or root / "tests/fixtures/inputs.tsv"
    for number, row in enumerate(input_file.read_text().splitlines(), 1):
        row = row.strip()
        if row and not row.startswith("#"):
            fields = row.split() if args.inputs else row.split("\t")[1:]
            if len(fields) != 4:
                raise ValueError(f"{input_file}:{number}: expected four unsigned words")
            words = [int(word) for word in fields]
            if any(word < 0 or word > (1 << 64) - 1 for word in words):
                raise ValueError(f"{input_file}:{number}: word outside u64")
            inputs.append(" ".join(map(str, words)))
    if not inputs:
        raise ValueError("no input rows")
    data = "\n".join(inputs) + "\n"
    flags = ["-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic", "-fno-lto",
             "-fsanitize=undefined", "-fno-sanitize-recover=undefined", "-DFIXTURE_ENTRY=fixture"]
    sources = sorted(source for opt in ("O0", "O1", "O2", "O3", "Os")
                     for source in args.artifacts.glob(f"*-{opt}.c"))
    if not sources:
        raise RuntimeError("retain artifacts with NIRVANA_RECOVERY_ARTIFACTS before running")
    report = {"compiler": invoke([args.cc, "--version"]).splitlines()[0], "flags": flags,
              "observations": "return and four state words; UBSan diagnostics fail",
              "input_file": str(input_file.resolve()),
              "input_sha256": hashlib.sha256(data.encode()).hexdigest(), "cases": []}
    for source in sources:
        opt = source.stem.rsplit("-", 1)[1]
        readable = source.with_name(source.stem + "-readable.c")
        native_binary = args.out / (source.stem + "-native")
        readable_binary = args.out / (source.stem + "-readable")
        invoke([args.cc, *flags, f"-{opt}", str(source), str(root / "tests/fixtures/harness.c"), "-o", str(native_binary)])
        invoke([args.cc, *flags, f"-{opt}", str(readable), "-o", str(readable_binary)])
        reference = invoke([str(native_binary.resolve())], data=data)
        reconstructed = invoke([str(readable_binary.resolve())], data=data)
        before = [list(map(int, row.split())) for row in reference.splitlines()]
        after = [list(map(int, row.split())) for row in reconstructed.splitlines()]
        if len(before) != len(inputs) or len(after) != len(inputs):
            raise AssertionError(f"row count mismatch: {source}")
        if any(len(row) != 5 for row in before) or any(len(row) != 6 for row in after):
            raise AssertionError(f"field count mismatch: {source}")
        if before != [row[:5] for row in after]:
            raise AssertionError(f"sanitized return/state mismatch: {source}")
        report["cases"].append({"source": str(source), "readable": str(readable), "optimization": opt,
                                "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                                "readable_sha256": hashlib.sha256(readable.read_bytes()).hexdigest(),
                                "inputs": len(inputs), "status": "matched-no-ubsan-diagnostics"})
    report["comparisons"] = len(sources) * len(inputs)
    (args.out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{len(sources)} configurations, {report['comparisons']} sanitized native/readable comparisons match")


if __name__ == "__main__":
    main()
