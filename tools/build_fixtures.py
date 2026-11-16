#!/usr/bin/env python3
"""Build native C reference fixtures and retain objects, oracles, and provenance.

Python standard library only. This does not invoke the decompiler or translate C
into the handwritten IR. Native artifacts use the selected compiler's host target.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess


REPO = Path(__file__).resolve().parents[1]
FIXTURES = REPO / "tests" / "fixtures"
UINT64_MAX = (1 << 64) - 1
BASE_FLAGS = ["-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic", "-fno-lto"]


def rows(path, width):
    result = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != width:
            raise ValueError(f"{path}:{number}: expected {width} tab-separated columns")
        result.append(fields)
    return result


def integers(words):
    values = tuple(int(word) for word in words)
    if any(value < 0 or value > UINT64_MAX for value in values):
        raise ValueError("fixture values must be unsigned 64-bit integers")
    return values


def catalog():
    cases = {}
    for name, ir, features in rows(FIXTURES / "cases.tsv", 3):
        if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", name) or name in cases:
            raise ValueError(f"invalid or duplicate fixture id: {name}")
        cases[name] = {"id": name, "handwritten_ir": None if ir == "-" else ir,
                       "features": features.split(",")}
    source_ids = {path.stem for path in (FIXTURES / "cases").glob("*.c")}
    if source_ids != set(cases):
        raise ValueError("cases.tsv and C source files do not agree")
    inputs = {}
    for name, *values in rows(FIXTURES / "inputs.tsv", 5):
        if not name or name in inputs:
            raise ValueError(f"duplicate input id: {name}")
        inputs[name] = integers(values)
    if not inputs:
        raise ValueError("at least one fixture input is required")
    goldens = {}
    for case, name, *values in rows(FIXTURES / "golden.tsv", 7):
        if case not in cases or name not in inputs or (case, name) in goldens:
            raise ValueError(f"invalid or duplicate golden case: {case}/{name}")
        goldens[case, name] = integers(values)
    if {case for case, _ in goldens} != set(cases):
        raise ValueError("every C fixture must have a hand-checked golden case")
    return cases, inputs, goldens


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(arguments, *, input_text=None, timeout=30):
    completed = subprocess.run([str(argument) for argument in arguments],
                               input=input_text, text=True, capture_output=True,
                               timeout=timeout, check=False)
    if completed.returncode:
        raise RuntimeError(f"command failed: {arguments}\n{completed.stderr}")
    return completed.stdout


def save_manifest(path, manifest):
    temporary = path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(manifest, indent=2) + "\n")
    temporary.replace(path)


def build(args):
    cases, inputs, goldens = catalog()
    if args.list:
        for case in cases.values():
            print(f"{case['id']}\t{','.join(case['features'])}")
        return
    if args.case:
        missing = set(args.case) - set(cases)
        if missing:
            raise ValueError(f"unknown fixture ids: {sorted(missing)}")
        cases = {name: case for name, case in cases.items() if name in args.case}
    compilers = args.cc or ["cc"]
    optimizations = list(dict.fromkeys(args.opt or ["O0", "O2"]))
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    metadata = {
        "schema_version": 1,
        "complete": False,
        "kind": "original-c-native-reference",
        "decompiler_tested": False,
        "inputs": {"path": "tests/fixtures/inputs.tsv", "sha256": sha256(FIXTURES / "inputs.tsv"), "count": len(inputs)},
        "goldens": {"path": "tests/fixtures/golden.tsv", "sha256": sha256(FIXTURES / "golden.tsv"), "count": len(goldens)},
        "support_sha256": {name: sha256(FIXTURES / name) for name in ["fixture.h", "harness.c", "helpers.c", "cases.tsv"]},
        "compilers": [], "artifacts": [],
    }
    manifest_path = output / "manifest.json"
    save_manifest(manifest_path, metadata)
    input_text = "".join(" ".join(map(str, values)) + "\n" for values in inputs.values())
    reference = {}
    native_cases = 0
    for compiler_index, selected in enumerate(compilers):
        compiler = shutil.which(selected)
        if compiler is None:
            raise ValueError(f"C compiler not found: {selected}")
        compiler = str(Path(compiler).resolve())
        compiler_id = f"cc-{compiler_index}"
        metadata["compilers"].append({"id": compiler_id, "executable": compiler,
                                      "version": command([compiler, "--version"]).strip(),
                                      "target": command([compiler, "-dumpmachine"]).strip()})
        for optimization in optimizations:
            variant = optimization + ("-ubsan" if args.sanitize else "")
            directory = output / compiler_id / variant
            directory.mkdir(parents=True, exist_ok=True)
            flags = [*BASE_FLAGS, f"-{optimization}"]
            if args.sanitize:
                flags += ["-fsanitize=undefined", "-fno-sanitize-recover=undefined"]
            support_objects = []
            for support in ["harness", "helpers"]:
                obj = directory / f"{support}.o"
                command([compiler, *flags, "-c", FIXTURES / f"{support}.c", "-o", obj])
                support_objects.append(obj)
            for name, case in cases.items():
                source = FIXTURES / "cases" / f"{name}.c"
                obj = directory / f"{name}.o"
                binary = directory / f"{name}.bin"
                oracle = directory / f"{name}.oracle.tsv"
                compile_command = [compiler, *flags, "-c", str(source), "-o", str(obj)]
                command(compile_command)
                command([compiler, *flags, obj, *support_objects, "-o", binary])
                stdout = command([binary], input_text=input_text, timeout=5)
                results = [integers(line.split()) for line in stdout.splitlines()]
                if len(results) != len(inputs) or any(len(result) != 5 for result in results):
                    raise ValueError(f"{name}: expected one return and four state values per input")
                if name in reference and results != reference[name]:
                    raise ValueError(f"{name}: native results differ across compiler/optimization settings")
                reference.setdefault(name, results)
                for input_id, result in zip(inputs, results):
                    expected = goldens.get((name, input_id))
                    if expected is not None and result != expected:
                        raise ValueError(f"{name}/{input_id}: got {result}, expected {expected}")
                oracle.write_text("# input id\treturn\tstate[0..3]\n" + "".join(
                    input_id + "\t" + "\t".join(map(str, result)) + "\n"
                    for input_id, result in zip(inputs, results)))
                metadata["artifacts"].append({
                    **case, "compiler": compiler_id, "optimization": optimization,
                    "sanitizer": "undefined" if args.sanitize else None,
                    "flags": flags, "compile_command": compile_command,
                    "source": str(source.relative_to(REPO)), "source_sha256": sha256(source),
                    "object": str(obj.relative_to(output)), "object_sha256": sha256(obj),
                    "binary": str(binary.relative_to(output)), "binary_sha256": sha256(binary),
                    "oracle": str(oracle.relative_to(output)), "oracle_sha256": sha256(oracle),
                })
                native_cases += len(results)
            print(f"{compiler_id} {variant}: {len(cases)} fixtures, {len(inputs)} inputs each", flush=True)
    metadata["complete"] = True
    metadata["native_executions"] = native_cases
    save_manifest(manifest_path, metadata)
    print(f"Verified {native_cases} native cases; artifacts and provenance: {manifest_path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="list fixture IDs without compiling")
    parser.add_argument("--cc", action="append", help="compiler executable, repeatable; default: cc")
    parser.add_argument("--opt", action="append", choices=["O0", "O1", "O2", "O3", "Os"], help="repeatable; default: O0 and O2")
    parser.add_argument("--case", action="append", help="fixture ID to build, repeatable; default: all")
    parser.add_argument("--out", type=Path, default=REPO / "target" / "c-fixtures")
    parser.add_argument("--sanitize", action="store_true", help="enable UndefinedBehaviorSanitizer")
    args = parser.parse_args()
    try:
        build(args)
    except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
