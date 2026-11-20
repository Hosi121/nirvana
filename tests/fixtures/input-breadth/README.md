# Jump-table input fixtures

Three C11 functions exercise compiler-generated switch dispatch: a dense
unsigned key, a signed 32-bit key with a negative lower bound, and nested
switches. An x86-64 assembly fixture, `shared-dispatch.S`, adds two table bases
merging into one indirect jump, a taken-side unsigned bound, and 28 scheduled
NOPs separating the base from its use. All share
`uint64_t fixture(uint64_t state[4])` with the main corpus.

```sh
cargo test --test input_breadth -- --nocapture
```

The test builds O0/O2 × ET_EXEC/PIE for each source, with ordinary optimization
and CET settings. It uses C11, strict warnings, `-fno-lto`, and
`-fno-stack-protector`, following the standalone fixture convention. Each exact
linked binary is used for native execution and module lifting.
The assembly fixture adds ET_EXEC/PIE at O2, for 14 profiles in total.

Each profile has 121 boundary and fixed-seed inputs. Native results are checked
against independent Rust oracles and module execution. Three module C outputs
are recompiled at O0/O2, then compared with all 80 registers, PC, instruction
budgets, first fault, and a digest of every guest RAM byte. Additional cases
exercise instruction cutoffs, resumption at table entries, and table mutation.
The matrix passes 1,694 native/oracle/module cases and 11,772 generated-C
state comparisons, including 16 table mutations. The original three-C-source
subset contributes 1,452 and 10,128 comparisons respectively.

The linked module frontend discovers absolute and signed-relative table
entries. `--emit module-jumps` reports the initial-image candidates, local
extent hints, and an open residual. Execution reads the current guest table;
rewritten entries can select other decoded code or produce `UnknownTarget`.
Predecessor contexts follow decoded direct CFG edges, keep alternative bases
separate, and merge entry extents for the same table. Cycles and search caps
are reported as `context_limited_branches`.
These candidates provide instruction discovery. Closed-CFG and C `switch`
reconstruction are subsequent analysis steps.
