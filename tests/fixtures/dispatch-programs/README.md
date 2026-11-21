# Dispatch programs

C11 programs add separate source families to the switch corpus:

- `mapped-switch.c`: a byte classification table feeds switch dispatch.
- `state-machine.c`: eight phases update state over one to eight iterations.
- `reused-selector.c`: volatile local slots hold successive selector values.
- `permuted-machine.c`: byte swaps precede dispatch in a state-machine loop.

```sh
cargo test --test end_to_end dispatch_programs:: -- --nocapture
NIRVANA_CLANG=clang-18 cargo test --test end_to_end dispatch_programs:: -- --include-ignored --nocapture
```

Each compiler builds O0/O2 × ET_EXEC/PIE with the same flags as
[input-breadth](../input-breadth/README.md). The exact binary runs natively
and supplies the lifted module. Independent Rust oracles cover 144 boundary,
state/iteration and fixed-seed inputs per profile. Budget cutoffs, case-entry
resumption, table rewrites and unknown targets add execution-boundary cases.

Three generated C backends compile at O0/O2 with UBSan. The shared
[module fixture harness](../../support/module_fixture.rs) compares all80
registers, PC, budgets, first fault and a digest of every guest RAM byte.
GCC13.3 and Clang18.1.3 each pass2,304 native/oracle/IR cases and15,720
generated comparisons across16 profiles. The first three families passed the
baseline implementation before inference changes. The permuted machine adds
two O2 PIE profiles whose hoisted table bases were previously forgotten at a
BSWAP. Inference now reuses scalar IR write sets: opaque results invalidate
their destination GPRs, flag writes invalidate comparison facts, and memory
writes invalidate saved values. Calls retain the opaque boundary.
Loop contexts retain explicit unexplored residuals.
