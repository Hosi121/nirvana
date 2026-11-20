# Modular HTTP linked-ELF benchmark

This fixture measures selected-function and whole-module recovery from a real
linked program. Whole-module mode regenerates executable C from `main`, then
compares HTTP behavior with the native server through actual loopback sockets.

The six separately compiled C modules contain request parsing (`parser.c`), route
lookup and indirect dispatch (`routes.c`), a cross-module table of handler pointers
(`routes_table.c`), response handlers/formatting (`response.c`), bounded loopback
transport (`transport.c`), and the executable entry (`main.c`). No LTO is used.
Keeping the table in a separate translation unit preserves table loads and indirect
handler calls at O2. `http_header_name_byte`, `http_header_value_byte`, and
`http_status_is_error` are simple pure leaves selectable from the final executable.
`http_server_banner` is a separately selectable puts-only leaf; the server announces
its port using `write`, avoiding stdout/stderr COPY relocations.

Run from the repository root:

```sh
python3 tools/http_server_benchmark.py --out target/http-server-native
python3 tools/http_server_benchmark.py --out target/http-server-probes --nirvana target/debug/nirvana
python3 tools/http_server_benchmark.py --out target/http-server-module --nirvana target/debug/nirvana --whole-module
python3 tools/http_server_benchmark.py --out target/http-server-structured --nirvana target/debug/nirvana --whole-module --module-emission module-readable-c
python3 -m unittest tools/tests/test_http_server_benchmark.py
```

The harness builds O0/O2 × ET_EXEC/PIE, checks the ELF kind and absence of COPY
relocations, and runs 13 actual socket cases per build. Each process binds only
`127.0.0.1` on an ephemeral port, prints that port, handles one request, closes, and
exits. Cases cover `/health`, `/metrics`, 404, unsupported method, HTTP/1.0, split
sends, malformed headers/lines, control bytes, long paths, oversized requests,
incomplete headers, and empty input. Content length, type, exact body, close, and
exit status are checked. Subprocesses are killed and reaped in `finally`, including
timeout/failure paths. Accept/receive/send also have three-second server bounds.

The optional CLI matrix probes each named function with `decoded`, `readable-c`,
`effects-ir`, and `effects-readable-c`, then compiles accepted C at O0 and O2.
`--function NAME` narrows function probes; the puts banner is always checked using
`--run-effects 0` with one modeled return outcome. The JSON report records commands,
compiler/source/binary identities, native results, emitted artifacts and diagnostics.
Statuses distinguish accepted output, explicit unsupported features, incompatible
CLI modes, timeouts, tool errors, generated-C errors, and wrong modeled output.
Explicit support rejections do not fail the harness; build/native failures and
unexpected tool/C/output errors do. C compilation checks syntax, not equivalence.

`--whole-module` additionally emits `module-c` for each binary, compiles it at
O0/O2, and repeats all socket cases: 104 generated-server runs across eight
combinations. A rejected module or a changed HTTP response fails this mode.
The report retains emitted C, binary hashes, commands, and each socket result.
`--compile-timeout` sets the whole-module compiler budget (default 60 seconds).
The original six C modules and native test cases are shared by both paths.

`--module-emission module-readable-c` runs the same comparison with named C
functions and structured bodies. The CLI reports structured/goto function counts
and direct/dynamic/import transfers. Each function retains resume labels for
altered return slots, deep recursion and entry at an existing guest PC.

The server implements one bounded GET request per connection and fixed in-memory
responses. Header names accept alphanumerics/hyphens; request/path/output limits
are 1024/127/2048 bytes. Generated module C preserves a checked guest RAM,
register file, stack, and PC dispatcher. Its Linux x86-64 adapter covers this
fixture's socket/errno ABI; the [execution model](../../../docs/equivalence.md)
defines the observation and supported environment.
