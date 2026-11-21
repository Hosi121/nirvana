#!/usr/bin/env python3
"""Compare pinned summarize ELF and checked C backends on fixed stdin cases.

Fetch the corpus with audit_ctf.py first. Native execution is restricted to the
SHA-256-pinned summarize binary; author-provided inputs are regression oracles.
"""
import argparse
import hashlib
import json
import os
import pathlib
import resource
import shutil
import subprocess

REPO = pathlib.Path(__file__).resolve().parent.parent


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def limits():
    resource.setrlimit(resource.RLIMIT_CPU, (3, 3))
    resource.setrlimit(resource.RLIMIT_AS, (256 << 20, 256 << 20))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def run(binary, text):
    process = subprocess.run([str(binary.resolve())], input=text.encode(),
                             capture_output=True, timeout=5, preexec_fn=limits,
                             env={**os.environ, "LC_ALL": "C"})
    return dict(exit_code=process.returncode, stdout_hex=process.stdout.hex(),
                stderr_hex=process.stderr.hex())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", type=pathlib.Path, required=True)
    parser.add_argument("--output", type=pathlib.Path, required=True)
    parser.add_argument("--nirvana", type=pathlib.Path,
                        default=REPO / "target/debug/nirvana")
    options = parser.parse_args()
    manifest_path = REPO / "tools/corpora/ctf-x86-64.json"
    manifest = json.loads(manifest_path.read_text())
    case = next(c for c in manifest["cases"] if c["id"] == "uiuctf2024-summarize")
    item = next(f for f in case["files"] if f["path"] == case["binary"])
    binary = options.inputs / case["id"] / case["binary"]
    data = binary.read_bytes()
    if sha256(data) != item["sha256"]:
        raise ValueError("original binary SHA-256 mismatch")
    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    original = output / "original"
    executables = []
    report = dict(schema="nirvana-ctf-stdio-v1", challenge=case["id"],
                  manifest_sha256=sha256(manifest_path.read_bytes()),
                  binary_sha256=sha256(data),
                  nirvana_sha256=sha256(options.nirvana.read_bytes()),
                  input_source="author-provided solution, zeros and mutants from pinned model runs",
                  observation="process exit code, stdout bytes and stderr bytes; C locale",
                  compiler=subprocess.check_output(["cc", "--version"], text=True).splitlines()[0],
                  cases=[], backends=[], diagnostic_inputs=[])
    try:
        shutil.copyfile(binary, original)
        original.chmod(0o700)
        executables.append(original)
        for index, model in enumerate(case["model_runs"]):
            text = " ".join(map(str, model["arguments"])) + "\n"
            expected = run(original, text)
            assert expected["exit_code"] == 0 and expected["stderr_hex"] == ""
            message = bytes.fromhex(expected["stdout_hex"])
            if "expected_rax" in model:
                assert (b"Correct.\n" in message) == (model["expected_rax"] == 1)
            report["cases"].append(dict(index=index, input=text,
                                        purpose=model["purpose"], original=expected))
        for mode in ["module-c", "module-readable-c", "module-locals-c"]:
            source = output / f"{mode}.c"
            generation = subprocess.run([str(options.nirvana.resolve()), str(binary.resolve()),
                                         "--entry", case["entry"], "--emit", mode],
                                        capture_output=True, timeout=30, check=True)
            source.write_bytes(generation.stdout)
            for optimization in ["-O0", "-O2"]:
                executable = output / f"{mode}{optimization}"
                command = ["cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic",
                           optimization, "-fsanitize=undefined", "-fno-sanitize-recover=all",
                           str(source), "-o", str(executable)]
                subprocess.run(command, capture_output=True, timeout=60, check=True)
                executables.append(executable)
                backend = dict(mode=mode, optimization=optimization,
                               c_sha256=sha256(generation.stdout),
                               executable_sha256=sha256(executable.read_bytes()),
                               compile_command=command, runs=[])
                for item in report["cases"]:
                    actual = run(executable, item["input"])
                    backend["runs"].append(dict(case=item["index"], actual=actual,
                                                matched=actual == item["original"]))
                report["backends"].append(backend)
                print(mode, optimization, sum(r["matched"] for r in backend["runs"]),
                      "/", len(backend["runs"]), flush=True)
        # The original ignores scanf failure and then reads uninitialized C
        # locals. Keep these observations separate from defined-input parity.
        for text in ["", "bad\n", "705965527 780663452\n"]:
            report["diagnostic_inputs"].append(dict(input=text, original=run(original, text),
                generated=run(executables[-1], text),
                caveat="original source leaves locals indeterminate after failed scanf"))
        matched = sum(r["matched"] for b in report["backends"] for r in b["runs"])
        report["summary"] = dict(defined_inputs=len(report["cases"]),
                                 generated_executables=len(report["backends"]),
                                 comparisons=sum(len(b["runs"]) for b in report["backends"]),
                                 matched=matched)
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        assert report["summary"]["comparisons"] == matched
    finally:
        for executable in executables:
            executable.unlink(missing_ok=True)


if __name__ == "__main__":
    main()
