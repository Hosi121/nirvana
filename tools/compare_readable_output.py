#!/usr/bin/env python3
"""Compare readable function text on identical C11/O0/O2 machine-code inputs.

Size/goto/mask counts describe output, not equivalence or source similarity.
Native equivalence is checked separately by the Rust fixture tests.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
FLAGS = ["-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic", "-fno-lto"]


def run(args):
    return subprocess.run(list(map(str, args)), text=True, capture_output=True,
                          timeout=30, cwd=ROOT)


def checked(args):
    result = run(args)
    if result.returncode:
        raise RuntimeError(f"{args}: {result.stderr}")
    return result.stdout


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def function_text(code):
    start = code.index("uint64_t nirvana_readable(")
    brace = code.index("{", start)
    depth = 1
    end = brace + 1
    while depth:
        if code[end] == "{":
            depth += 1
        elif code[end] == "}":
            depth -= 1
        end += 1
    return code[start:end] + "\n"


def metrics(code):
    body = function_text(code)
    # Exclude comments and whitespace from the token measure. Full translation
    # unit bytes are retained too: shorter calls add a shared helper prelude.
    plain = re.sub(r"/\*.*?\*/|//[^\n]*", "", body, flags=re.S)
    declarations = re.findall(
        r"^\s*(?:uint(?:8|16|32|64)_t|nirvana_u(?:8|16|32|64)_address)\s+(\w+)\s*([;=])", plain, re.M)
    locals_ = {name for name, _ in declarations if not name.startswith("nirvana_")}
    initialized_locals = {name for name, delimiter in declarations
                          if name in locals_ and delimiter == "="}
    copies = sum(a in locals_ and b in locals_ for a, b in
                 re.findall(r"\b(\w+)\s*=\s*(\w+)\s*(?=[,;)])", plain))
    named_roles = sum(re.fullmatch(r"(?:counter|accumulator|limit|address|quotient)\d*", name) is not None
                      for name in locals_)
    return {"unit_bytes": len(code.encode()), "function_bytes": len(body.encode()),
            "tokens": len(re.findall(r"[A-Za-z_][A-Za-z_0-9]*|0x[0-9a-f]+|[0-9]+|[^\s]", plain)),
            "gotos": len(re.findall(r"\bgoto\b", plain)),
            "labels": len(re.findall(r"^bb[0-9]+:", plain, re.M)),
            "masks": plain.count(" & "),
            "casts": len(re.findall(r"\(uint(?:8|16|32|64)_t\)", plain)),
            "locals": len(locals_), "initialized_locals": len(initialized_locals),
            "copies": copies, "named_roles": named_roles,
            "for_headers": len(re.findall(r"\bfor \(;(?: |\n)", plain)),
            "if_statements": len(re.findall(r"\bif\s*\(", plain)),
            "return_statements": len(re.findall(r"\breturn\b", plain)),
            "break_statements": len(re.findall(r"\bbreak\b", plain)),
            "posttest_loops": len(re.findall(r"}\s*while\s*\(", plain)),
            "compound_updates": sum(name in locals_ for name in re.findall(r"\b(\w+)\s*[+\-*%&|^]=", plain)),
            "max_indent": max(len(line) - len(line.lstrip()) for line in plain.splitlines())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, default=ROOT / "target/debug/nirvana")
    parser.add_argument("--out", type=Path, default=ROOT / "target/output-polish")
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    binaries = {"before": args.before.resolve(), "after": args.after.resolve()}
    sources = sorted((ROOT / "tests/fixtures/cases").glob("*.c"))
    sources += sorted((ROOT / "tests/fixtures/recovery").glob("*.c"))
    rows = []
    for source in sources:
        for opt in ["O0", "O2"]:
            name = f"{source.stem}-{opt}"
            obj = out / f"{name}.o"
            checked(["cc", *FLAGS, f"-{opt}", "-c", source, "-o", obj])
            row = {"id": name, "source": str(source.relative_to(ROOT)),
                   "source_sha256": digest(source), "object_sha256": digest(obj),
                   "flags": FLAGS + [f"-{opt}"]}
            rejected = []
            for variant, binary in binaries.items():
                result = run([binary, obj, "--emit", "readable-c"])
                rejected.append(result.returncode != 0)
                if result.returncode:
                    row[variant] = {"error": result.stderr.strip()}
                    continue
                full = out / f"{name}-{variant}.c"
                full.write_text(result.stdout)
                checked(["cc", *FLAGS, f"-{opt}", "-c", full, "-o", full.with_suffix(".o")])
                (out / f"{name}-{variant}-function.c").write_text(function_text(result.stdout))
                row[variant] = metrics(result.stdout)
            if rejected[0] != rejected[1]:
                raise RuntimeError(f"{name}: support changed; cannot compare the same corpus")
            rows.append(row)
    accepted = [r for r in rows if "error" not in r["after"]]
    totals = {v: {k: sum(r[v][k] for r in accepted)
                  for k in ["unit_bytes", "function_bytes", "tokens", "gotos", "labels", "masks", "casts", "locals", "initialized_locals", "copies", "named_roles", "for_headers", "if_statements", "return_statements", "break_statements", "posttest_loops", "compound_updates"]}
              for v in binaries}
    report = {"compiler": checked(["cc", "--version"]).strip(),
              "binaries": {v: {"path": str(p), "sha256": digest(p)} for v, p in binaries.items()},
              "configurations": len(rows), "accepted": len(accepted), "totals": totals, "rows": rows}
    (out / "comparison.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"accepted": len(accepted), "configurations": len(rows), "totals": totals}, indent=2))


if __name__ == "__main__":
    main()
