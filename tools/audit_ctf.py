#!/usr/bin/env python3
"""Measure original CTF binaries using a pinned corpus and local Nirvana builds."""

import argparse
import collections
import hashlib
import json
import pathlib
import re
import struct
import subprocess
import urllib.request


REPO = pathlib.Path(__file__).resolve().parent.parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def command(args, stem, text=None):
    args = [str(a) for a in args]
    try:
        p = subprocess.run(args, input=text, capture_output=True, text=True, timeout=30)
        code, out, err = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired as e:
        code, out, err = None, e.stdout or b"", e.stderr or b""
        out = out.decode(errors="replace") if isinstance(out, bytes) else out
        err = err.decode(errors="replace") if isinstance(err, bytes) else err
    stem.parent.mkdir(parents=True, exist_ok=True)
    stdout = stem.with_suffix(stem.suffix + ".stdout")
    stdout.write_text(out)
    stem.with_suffix(stem.suffix + ".stderr").write_text(err)
    return {"command": args, "exit_code": code, "stderr": err,
            "stdout": str(stdout), "stdout_sha256": digest(out.encode())}


def elf_loads(data):
    if data[:7] != b"\x7fELF\x02\x01\x01" or struct.unpack_from("<H", data, 18)[0] != 62:
        raise ValueError("corpus requires ELF64 little-endian x86-64")
    offset = struct.unpack_from("<Q", data, 32)[0]
    stride, count = struct.unpack_from("<HH", data, 54)
    if stride < 56 or offset + stride * count > len(data):
        raise ValueError("invalid program header bounds")
    loads = []
    for i in range(count):
        kind, flags, file_offset, address, _, filesz, memsz, _ = struct.unpack_from(
            "<IIQQQQQQ", data, offset + i * stride)
        if kind == 1:
            if file_offset + filesz > len(data) or filesz > memsz:
                raise ValueError("invalid PT_LOAD bounds")
            loads.append({"address": address, "file_offset": file_offset,
                          "filesz": filesz, "memsz": memsz, "flags": flags})
    return loads


def code_bytes(data, loads, start, size):
    matches = [p for p in loads if p["flags"] & 1 and p["address"] <= start
               and start + size <= p["address"] + p["filesz"]]
    if len(matches) != 1:
        raise ValueError("function needs one file-backed executable mapping")
    offset = matches[0]["file_offset"] + start - matches[0]["address"]
    return data[offset:offset + size]


def symbols(text):
    result = {}
    for line in text.splitlines():
        f = line.split()
        if len(f) >= 8 and f[3] == "FUNC" and f[6] not in ("UND", "ABS") and int(f[2]) > 0:
            result[f[7]] = (int(f[1], 16), int(f[2]))
    return result


def instruction_rows(text, regions):
    rows = []
    for line in text.splitlines():
        match = re.match(r"\s*([0-9a-f]+):\s+((?:[0-9a-f]{2}\s+)+)\s*(.*)", line)
        if match:
            address = int(match[1], 16)
            owners = [name for name, (start, size) in regions.items()
                      if start <= address < start + size]
            if owners:
                rows.append({"address": address, "hex": "".join(match[2].split()),
                             "assembly": match[3], "regions": owners})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=pathlib.Path,
                        default=REPO / "tools/corpora/ctf-x86-64.json")
    parser.add_argument("--output", type=pathlib.Path, required=True)
    parser.add_argument("--nirvana", type=pathlib.Path, default=REPO / "target/debug/nirvana")
    parser.add_argument("--probe", type=pathlib.Path, default=REPO / "target/debug/examples/inspect_ctf")
    parser.add_argument("--offline", action="store_true", help="verify and reuse downloaded inputs")
    options = parser.parse_args()
    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    manifest = json.loads(options.manifest.read_text())
    nirvana, probe = options.nirvana.resolve(), options.probe.resolve()
    report = {"schema": "nirvana-ctf-audit-v1", "nirvana_sha256": digest(nirvana.read_bytes()),
              "probe_sha256": digest(probe.read_bytes()),
              "manifest_sha256": digest(options.manifest.read_bytes()),
              "scope": "static original binaries, selected function probes and bounded modeled runs",
              "cases": []}
    for case in manifest["cases"]:
        directory = output / "observations" / case["id"]
        directory.mkdir(parents=True, exist_ok=True)
        inputs = output / "inputs" / case["id"]
        for item in case["files"]:
            path = inputs / item["path"]
            if not path.exists():
                if options.offline:
                    raise FileNotFoundError(path)
                with urllib.request.urlopen(item["url"], timeout=30) as response:
                    data = response.read(item["bytes"] + 1)
                if len(data) != item["bytes"] or digest(data) != item["sha256"]:
                    raise ValueError(f"download mismatch: {item['url']}")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
            if digest(path.read_bytes()) != item["sha256"]:
                raise ValueError(f"cached input mismatch: {path}")
        binary = inputs / case["binary"]
        data = binary.read_bytes()
        loads = elf_loads(data)
        observed = {"id": case["id"], "source_url": case["challenge_url"],
                    "binary_sha256": digest(data), "loads": loads,
                    "mapped_bytes": sum(p["memsz"] for p in loads),
                    "image_span": max(p["address"] + p["memsz"] for p in loads)
                                  - min(p["address"] for p in loads)}
        metadata = {}
        for label, args in [
            ("symbols", ["readelf", "--wide", "--syms", binary]),
            ("frames", ["readelf", "--wide", "--debug-dump=frames", binary]),
            ("relocations", ["readelf", "--wide", "--relocs", binary]),
            ("disassembly", ["objdump", "-d", "-M", "intel", "--insn-width=16", binary]),
        ]:
            run = command(args, directory / label)
            if run["exit_code"] != 0:
                raise RuntimeError(run)
            metadata[label] = pathlib.Path(run["stdout"]).read_text()
        observed["imports"] = sorted({f[7].split("@")[0]
            for line in metadata["symbols"].splitlines() if len(f := line.split()) >= 8
            and f[3] == "FUNC" and f[6] == "UND"})
        observed["copy_relocations"] = [line.strip() for line in metadata["relocations"].splitlines()
                                         if "R_X86_64_COPY" in line]
        observed["root"] = command([nirvana, binary, "--entry", case["entry"], "--emit", "module-locals-c"], directory / "root")
        if observed["root"]["exit_code"] == 0:
            obj = directory / "root.o"
            observed["root_compile"] = command(
                ["cc", "-x", "c", "-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic",
                 "-c", observed["root"]["stdout"], "-o", obj], directory / "root-compile")
            obj.unlink(missing_ok=True)
        found = symbols(metadata["symbols"])
        wanted = {"main": int(case["entry"], 0), **{p["name"]: int(p["entry"], 0)
                                                    for p in case["module_probes"]}}
        regions = {name: found[name] for name in case["raw_symbols"]}
        for name, entry in wanted.items():
            if name in found:
                regions[name] = found[name]
            else:
                bounds = {(int(a, 16), int(b, 16)) for a, b in re.findall(
                    r"pc=([0-9a-f]+)\.\.([0-9a-f]+)", metadata["frames"])}
                matches = [(a, b - a) for a, b in bounds if a == entry]
                if len(matches) != 1:
                    raise ValueError(f"ambiguous/missing FDE: {case['id']} {entry:#x}")
                regions[name] = matches[0]
        rows = instruction_rows(metadata["disassembly"], regions)
        for row in rows:
            instruction = bytes.fromhex(row["hex"])
            if code_bytes(data, loads, row["address"], len(instruction)) != instruction:
                raise ValueError("disassembly bytes disagree with original ELF")
        for name, (start, size) in regions.items():
            cursor = start
            for row in rows:
                if name in row["regions"]:
                    if row["address"] != cursor:
                        raise ValueError(f"instruction coverage gap: {name}")
                    cursor += len(bytes.fromhex(row["hex"]))
            if cursor != start + size:
                raise ValueError(f"incomplete function byte coverage: {name}")
        text = "".join(f"{i}\t{row['address']:#x}\t{row['hex']}\n" for i, row in enumerate(rows))
        run = command([probe, "decode"], directory / "decode", text)
        if run["exit_code"] != 0:
            raise RuntimeError(run)
        lines = pathlib.Path(run["stdout"]).read_text().splitlines()
        if len(lines) != len(rows):
            raise ValueError("incomplete instruction probe")
        for expected_index, (row, line) in enumerate(zip(rows, lines)):
            index, row["decode"], row["detail"] = line.split("\t", 2)
            if int(index) != expected_index:
                raise ValueError("instruction probe order mismatch")
        observed["regions"] = regions
        observed["instruction_decode_counts"] = dict(collections.Counter(r["decode"] for r in rows))
        observed["unsupported_instructions"] = [r for r in rows if r["decode"] == "unsupported"]
        observed["raw_functions"] = []
        for name in case["raw_symbols"]:
            address, size = regions[name]
            raw = directory / (name + ".bin")
            raw.write_bytes(code_bytes(data, loads, address, size))
            run = command([nirvana, raw, "--raw", "--base", hex(address), "--entry", hex(address),
                           "--emit", "readable-c"], directory / ("raw-" + name))
            result = {"name": name, "address": address, "size": size, "readable": run}
            if run["exit_code"] == 0:
                obj = directory / (name + ".o")
                result["compile"] = command(["cc", "-x", "c", "-std=c11", "-Wall", "-Wextra", "-Werror",
                                              "-pedantic", "-c", run["stdout"], "-o", obj], directory / ("compile-" + name))
                obj.unlink(missing_ok=True)
                result["types"] = command([nirvana, raw, "--raw", "--base", hex(address), "--entry", hex(address),
                                            "--emit", "types"], directory / ("types-" + name))
            observed["raw_functions"].append(result)
        observed["module_probes"] = []
        for item in case["module_probes"]:
            result = {"name": item["name"], "entry": item["entry"], "outputs": {}}
            for mode in ["module-jumps", "module-values", "module-locals-c"]:
                result["outputs"][mode] = command([nirvana, binary, "--entry", item["entry"], "--emit", mode],
                                                    directory / (item["name"] + "-" + mode))
            c = result["outputs"]["module-locals-c"]
            if c["exit_code"] == 0:
                obj = directory / (item["name"] + "-module.o")
                result["compile"] = command(["cc", "-x", "c", "-std=c11", "-Wall", "-Wextra", "-Werror",
                                              "-pedantic", "-c", c["stdout"], "-o", obj], directory / (item["name"] + "-compile"))
                obj.unlink(missing_ok=True)
            observed["module_probes"].append(result)
        observed["model_runs"] = []
        for index, item in enumerate(case["model_runs"]):
            result = {**item, "result": command([probe, "run", binary, item["entry"],
                       ",".join(map(str, item["arguments"]))], directory / f"run-{index}")}
            result["state"] = pathlib.Path(result["result"]["stdout"]).read_text()
            observed["model_runs"].append(result)
        report["cases"].append(observed)
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(case["id"], "root:", observed["root"]["exit_code"],
              "decode:", observed["instruction_decode_counts"], flush=True)
    print("Report:", output / "report.json")


if __name__ == "__main__":
    main()
