#!/usr/bin/env python3
"""Build a modular HTTP fixture, verify native sockets, and probe selected ELF functions.

Function emission, C compilation, and native server behavior are separate results.
Successful selected-function probes do not demonstrate whole-server decompilation.
"""

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import struct
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests/fixtures/http-server"
FLAGS = ["-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic", "-fno-lto",
         "-fno-stack-protector"]
FUNCTIONS = ["http_header_name_byte", "http_header_value_byte", "http_status_is_error",
             "http_reason_phrase", "http_path_equal", "http_parse_request",
             "http_dispatch", "http_render_response", "http_server_banner",
             "http_read_request", "http_serve_once"]
EMISSIONS = ["decoded", "readable-c", "effects-ir", "effects-readable-c"]


def native_cases():
    def case(name, request, status, body, **options):
        return {"name": name, "chunks": [request], "status": status, "body": body, **options}

    return [
        case("health", b"GET /health HTTP/1.1\r\nHost: localhost\r\n\r\n", 200, b"ok\n"),
        case("metrics", b"GET /metrics HTTP/1.1\r\nHost: localhost\r\n\r\n", 200,
             b"requests_total 1\n", content_type="text/plain; version=0.0.4"),
        case("not-found", b"GET /missing HTTP/1.1\r\n\r\n", 404, b"not found\n"),
        case("method", b"POST /health HTTP/1.1\r\n\r\n", 405, b"method not allowed\n"),
        case("http-1.0", b"GET /health HTTP/1.0\r\n\r\n", 200, b"ok\n"),
        {"name": "fragmented", "chunks": [b"GET /hea", b"lth HTTP/1.1\r\nHost: local",
                                           b"host\r\n\r\n"],
         "status": 200, "body": b"ok\n"},
        case("malformed-line", b"GET /health BAD/1.1\r\n\r\n", 400, b"bad request\n"),
        case("malformed-header", b"GET /health HTTP/1.1\r\nNo-Colon\r\n\r\n", 400,
             b"bad request\n"),
        case("control-byte", b"GET /health HTTP/1.1\r\nX-Test: \x01\r\n\r\n", 400,
             b"bad request\n"),
        case("long-path", b"GET /" + b"x" * 128 + b" HTTP/1.1\r\n\r\n", 400,
             b"bad request\n"),
        case("oversized", b"GET /health HTTP/1.1\r\nX-Pad: " + b"x" * 1024 + b"\r\n\r\n",
             400, b"bad request\n", allow_reset=True),
        case("incomplete", b"GET /health HTTP/1.1\r\nHost: localhost", 400,
             b"bad request\n"),
        case("empty", b"", 400, b"bad request\n"),
    ]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def as_text(value):
    return value.decode("utf-8", "replace") if isinstance(value, bytes) else value or ""


def command(argv, timeout=20):
    argv = list(map(str, argv))
    started = time.monotonic()
    try:
        result = subprocess.run(argv, capture_output=True, text=True, timeout=timeout, cwd=ROOT)
        return {"argv": argv, "returncode": result.returncode, "stdout": result.stdout,
                "stderr": result.stderr, "duration_seconds": time.monotonic() - started}
    except subprocess.TimeoutExpired as error:
        return {"argv": argv, "returncode": None, "stdout": as_text(error.stdout),
                "stderr": as_text(error.stderr), "timeout": True,
                "duration_seconds": time.monotonic() - started}
    except OSError as error:
        return {"argv": argv, "returncode": None, "stdout": "", "stderr": str(error),
                "launch_error": True, "duration_seconds": time.monotonic() - started}


def classify_probe(result):
    """Only known capability rejections count as unsupported; retain other failures."""
    diagnostic = result["stderr"].lower()
    if result.get("timeout"):
        return "timeout"
    if result.get("launch_error") or result["returncode"] is None or result["returncode"] < 0:
        return "tool-error"
    if result["returncode"] == 0:
        return "accepted"
    if "panicked at" in diagnostic or "stack overflow" in diagnostic:
        return "tool-error"
    if any(text in diagnostic for text in ["unknown emission format", "unknown option",
                                           "unrecognized option", "unexpected argument"]):
        return "cli-incompatible"
    if any(text in diagnostic for text in ["unsupported", "not implemented", "not proven",
                                           "unresolved relocation", "unresolved import",
                                           "must target the external puts", "must target puts",
                                           "indirect effects require", "requires internal-call or plt analysis",
                                           "requires an external effect model", "requires value-flow evidence",
                                           "lacks dynamic import evidence"]):
        return "unsupported"
    return "tool-error"


def read_port(process, timeout):
    deadline = time.monotonic() + timeout
    data = bytearray()
    with selectors.DefaultSelector() as selector:
        selector.register(process.stdout, selectors.EVENT_READ)
        while b"\n" not in data:
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not selector.select(remaining):
                raise TimeoutError("server did not announce its loopback port")
            chunk = os.read(process.stdout.fileno(), 64)
            if not chunk:
                raise RuntimeError("server exited before announcing its loopback port")
            data.extend(chunk)
            if len(data) > 16:
                raise RuntimeError("server port announcement exceeded its bound")
    if not re.fullmatch(rb"[0-9]+\n", data):
        raise RuntimeError(f"invalid server port announcement: {bytes(data)!r}")
    port = int(data)
    if not 0 < port < 65536:
        raise RuntimeError(f"invalid loopback port: {port}")
    return port


def check_response(response, case):
    head, separator, body = response.partition(b"\r\n\r\n")
    if not separator:
        raise AssertionError(f"incomplete HTTP response: {response!r}")
    lines = head.decode("ascii").split("\r\n")
    status = int(lines[0].split(" ")[1])
    if not lines[0].startswith("HTTP/1.1 ") or status != case["status"]:
        raise AssertionError(f"unexpected status line: {lines[0]!r}")
    headers = dict(line.split(": ", 1) for line in lines[1:])
    if headers.get("Connection") != "close":
        raise AssertionError("response does not close the one-request connection")
    if int(headers.get("Content-Length", "-1")) != len(body) or body != case["body"]:
        raise AssertionError(f"unexpected content length/body: {headers!r}, {body!r}")
    if headers.get("Content-Type") != case.get("content_type", "text/plain"):
        raise AssertionError(f"unexpected content type: {headers!r}")
    return {"status_code": status, "headers": headers, "body": body.decode("ascii"),
            "response_bytes": len(response)}


def run_native_case(binary, case, timeout=5):
    import socket

    started = time.monotonic()
    row = {"case": case["name"], "status": "failed"}
    process = None
    try:
        process = subprocess.Popen([str(binary)], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   cwd=ROOT)
        port = read_port(process, timeout)
        response = bytearray()
        connection_reset = False
        with socket.create_connection(("127.0.0.1", port), timeout=timeout) as client:
            client.settimeout(timeout)
            for i, chunk in enumerate(case["chunks"]):
                client.sendall(chunk)
                if i + 1 < len(case["chunks"]):
                    time.sleep(0.01)
            client.shutdown(socket.SHUT_WR)
            while True:
                try:
                    chunk = client.recv(4096)
                except ConnectionResetError:
                    connection_reset = True
                    if not case.get("allow_reset"):
                        raise
                    break
                if not chunk:
                    break
                response.extend(chunk)
                if len(response) > 4096:
                    raise AssertionError("response exceeded the fixture bound")
        stdout, stderr = process.communicate(timeout=timeout)
        row.update(check_response(bytes(response), case))
        row.update(returncode=process.returncode, stderr=stderr.decode("utf-8", "replace"),
                   connection_reset=connection_reset)
        if process.returncode != 0 or stdout or stderr:
            raise AssertionError(f"unexpected server exit/output: {process.returncode}, "
                                 f"{stdout!r}, {stderr!r}")
        row["status"] = "passed"
    except Exception as error:
        row["error"] = f"{type(error).__name__}: {error}"
    finally:
        if process is not None:
            if process.poll() is None:
                process.kill()
            _, stderr = process.communicate()
            row["returncode"] = process.returncode
            row.setdefault("stderr", stderr.decode("utf-8", "replace"))
            process.stdout.close()
            process.stderr.close()
        row["duration_seconds"] = time.monotonic() - started
    return row


def build_variant(out, optimization, elf_kind, cc="cc"):
    directory = out / f"{elf_kind}-{optimization}"
    directory.mkdir(parents=True, exist_ok=True)
    row = {"id": directory.name, "optimization": optimization, "elf_kind": elf_kind,
           "commands": [], "status": "failed"}
    compile_flags = FLAGS + [f"-{optimization}", "-fPIE" if elf_kind == "pie" else "-fno-pie"]
    objects = []
    for source in sorted(FIXTURE.glob("*.c")):
        obj = directory / f"{source.stem}.o"
        result = command([cc, *compile_flags, "-c", source, "-o", obj])
        row["commands"].append(result)
        if result["returncode"] != 0:
            return row
        objects.append(obj)
    binary = directory / "http-server"
    result = command([cc, f"-{optimization}", "-fno-lto",
                      "-pie" if elf_kind == "pie" else "-no-pie", *objects, "-o", binary])
    row["commands"].append(result)
    if result["returncode"] != 0:
        return row
    header = binary.read_bytes()[:20]
    expected_type = 3 if elf_kind == "pie" else 2
    if (header[:6] != b"\x7fELF\x02\x01" or
            struct.unpack_from("<HH", header, 16) != (expected_type, 62)):
        row["error"] = "compiler did not produce the requested ELF64 x86-64 executable kind"
        return row
    relocations = command(["readelf", "-rW", binary])
    row["commands"].append(relocations)
    if relocations["returncode"] != 0:
        return row
    (directory / "relocations.txt").write_text(relocations["stdout"])
    row["copy_relocations"] = relocations["stdout"].count("R_X86_64_COPY")
    if row["copy_relocations"]:
        row["error"] = "fixture unexpectedly requires COPY/data relocation support"
        return row
    row.update(status="passed", binary=str(binary), binary_sha256=sha256(binary),
               compile_flags=compile_flags, elf_type=expected_type)
    return row


def probe_function(nirvana, binary, symbol, emission, out, cc="cc", timeout=10):
    prefix = out / f"{symbol}-{emission}"
    result = command([nirvana, binary, "--symbol", symbol, "--emit", emission], timeout)
    row = {key: value for key, value in result.items() if key != "stdout"}
    row.update(symbol=symbol, emission=emission, status=classify_probe(result))
    extension = ".c" if emission.endswith("-c") else ".txt"
    emitted = prefix.with_suffix(extension)
    emitted.write_text(result["stdout"])
    prefix.with_suffix(".stderr.txt").write_text(result["stderr"])
    row["output"] = str(emitted)
    row["output_bytes"] = len(result["stdout"].encode())
    if row["status"] == "accepted" and emission.endswith("-c"):
        row["generated_c"] = []
        for optimization in ("O0", "O2"):
            compilation = command([cc, *FLAGS, f"-{optimization}", "-c", emitted,
                                   "-o", prefix.with_suffix(f".{optimization}.o")], timeout)
            row["generated_c"].append({**compilation,
                                       "status": "passed" if compilation["returncode"] == 0
                                       else "failed"})
        if any(item["status"] != "passed" for item in row["generated_c"]):
            row["status"] = "generated-c-error"
    return row


def probe_banner(nirvana, binary, timeout=10):
    result = command([nirvana, binary, "--symbol", "http_server_banner", "--run-effects", "0"],
                     timeout)
    row = {**result, "symbol": "http_server_banner", "emission": "run-effects",
           "status": classify_probe(result), "modeled_puts_return": 0}
    if row["status"] == "accepted":
        if (result["stdout"] != "nirvana modular HTTP fixture\n" or
                re.search(r"\breturned(?: rax=| )0\b", result["stderr"]) is None or
                "1 outcomes consumed" not in result["stderr"]):
            row["status"] = "modeled-output-error"
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="artifact/report directory")
    parser.add_argument("--nirvana", type=Path, help="optional selected-function CLI to evaluate")
    parser.add_argument("--cc", default="cc")
    parser.add_argument("--timeout", type=float, default=5.0, help="native operation timeout, seconds")
    parser.add_argument("--probe-timeout", type=float, default=10.0)
    parser.add_argument("--function", action="append", dest="functions",
                        help="probe only this symbol; repeat for multiple symbols")
    args = parser.parse_args()
    if args.timeout <= 0 or args.probe_timeout <= 0:
        parser.error("timeouts must be positive")
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    nirvana = args.nirvana.resolve() if args.nirvana else None
    report = {
        "schema": "nirvana-http-server-benchmark-v1",
        "claim": "Native modular server plus selected-function support; no whole-server decompilation claim.",
        "limits": {"requests_per_process": 1, "request_bytes": 1024, "path_bytes_including_nul": 128,
                   "response_bytes": 2048, "bind_address": "127.0.0.1", "port": "ephemeral",
                   "server_io_timeout_seconds": 3, "native_timeout_seconds": args.timeout,
                   "probe_timeout_seconds": args.probe_timeout, "lto": False},
        "compiler": command([args.cc, "--version"]),
        "sources": [{"path": str(path.relative_to(ROOT)), "sha256": sha256(path)}
                    for path in sorted(FIXTURE.iterdir()) if path.suffix in (".c", ".h")],
        "configurations": [],
    }
    if nirvana:
        report["nirvana"] = {"path": str(nirvana),
                              "sha256": sha256(nirvana) if nirvana.is_file() else None}
    for elf_kind in ("exec", "pie"):
        for optimization in ("O0", "O2"):
            row = build_variant(out, optimization, elf_kind, args.cc)
            report["configurations"].append(row)
            if row["status"] != "passed":
                continue
            binary = Path(row["binary"])
            row["native"] = [run_native_case(binary, case, args.timeout) for case in native_cases()]
            if nirvana:
                probe_out = binary.parent / "probes"
                probe_out.mkdir(exist_ok=True)
                row["probes"] = [probe_function(nirvana, binary, symbol, emission, probe_out,
                                                args.cc, args.probe_timeout)
                                 for symbol in args.functions or FUNCTIONS for emission in EMISSIONS]
                row["probes"].append(probe_banner(nirvana, binary, args.probe_timeout))
            # Persist after each configuration so interrupted evaluations leave evidence.
            (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    native = [case for row in report["configurations"] for case in row.get("native", [])]
    probes = [probe for row in report["configurations"] for probe in row.get("probes", [])]
    summary = {"configurations": len(report["configurations"]),
               "builds_passed": sum(row["status"] == "passed" for row in report["configurations"]),
               "native_cases": len(native), "native_passed": sum(case["status"] == "passed" for case in native),
               "probe_statuses": dict(Counter(probe["status"] for probe in probes))}
    report["summary"] = summary
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({**summary, "report": str(out / "report.json")}, indent=2))
    hard_errors = {"tool-error", "timeout", "generated-c-error", "modeled-output-error"}
    return 0 if (summary["builds_passed"] == 4 and len(native) == 4 * len(native_cases()) and
                 summary["native_passed"] == len(native) and
                 not any(probe["status"] in hard_errors for probe in probes)) else 1


if __name__ == "__main__":
    raise SystemExit(main())
