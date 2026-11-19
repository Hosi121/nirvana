# Modular HTTP linked-ELF benchmark

This fixture measures selected-function recovery from a real linked program.
The report distinguishes native socket behavior, C emission/compilation, and
modeled execution. Whole-server equivalence requires interprocedural execution
and socket effect models.

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

The server implements one bounded GET request per connection and fixed in-memory
responses. Header names accept alphanumerics/hyphens; request/path/output limits
are 1024/127/2048 bytes. Socket/errno effects, cross-function execution, and general
indirect-call recovery are the next evaluation targets.
