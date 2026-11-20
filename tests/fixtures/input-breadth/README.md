# Jump-table input fixtures

Three C11 functions exercise compiler-generated switch dispatch: a dense
unsigned key, a signed 32-bit key with a negative lower bound, and nested
switches. They share `uint64_t fixture(uint64_t state[4])` with the main corpus.

```sh
cargo test --test input_breadth -- --nocapture
```

The test builds O0/O2 × ET_EXEC/PIE for each source, with ordinary optimization
and CET settings. It uses C11, strict warnings, `-fno-lto`, and
`-fno-stack-protector`, following the standalone fixture convention. Each exact
linked binary is used for native execution and module lifting.

Each profile has 121 boundary and fixed-seed inputs. Native results are checked
against independent Rust oracles and module execution. Three module C outputs
are recompiled at O0/O2, then compared with all 80 registers, PC, instruction
budgets, first fault, and a digest of every guest RAM byte. Additional cases
exercise instruction cutoffs, resumption at table entries, and table mutation.
The initial matrix passes 1,452 native/oracle/module cases and 10,128 generated-C
state comparisons, including eight table mutations.

The linked module frontend discovers absolute and signed-relative table
entries. `--emit module-jumps` reports the initial-image candidates, local
extent hints, and an open residual. Execution reads the current guest table;
rewritten entries can select other decoded code or produce `UnknownTarget`.
These candidates provide instruction discovery. Closed-CFG and C `switch`
reconstruction are subsequent analysis steps.
