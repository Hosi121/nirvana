# Stripped modules

`pipeline.c` selects direct calls and a writable function-pointer table over
three stages. `stages.c` and `table.c` are separate translation units, linked
with the shared four-word fixture harness and `-fno-lto`.

```sh
cargo test --test stripped_elf -- --nocapture
NIRVANA_CLANG=clang-18 cargo test --test stripped_elf -- --include-ignored --nocapture
```

The test needs GNU binutils `strip` and `nm`. It obtains the fixture address
from the original file for evaluation, then gives the decompiler only the
`strip --strip-all` output and that numeric link-time entry. The loader uses
mapped `.eh_frame` regions; sized function symbols serve as an independent
bound check before stripping. Native execution uses both exact files.

The pipeline and four [dispatch programs](../dispatch-programs/README.md)
each build at O0/O2 × ET_EXEC/PIE per compiler. Independent Rust oracles cover
144 inputs/profile. Three C backends at O0/O2 run with UBSan and compare all80
registers, PC, budgets, first fault and the whole guest RAM digest. Additional
cases cover region entries, jump-table cases and writable call targets.
Clang O0's pipeline emits DIV for `% 3`, exercising the module's checked
divide-error instruction in both ELF profiles. The optimized profiles use
the compiler's multiplication and shift lowering.

The FDE layout follows [LSB Core 4.1 §10.6](https://refspecs.linuxfoundation.org/LSB_4.1.0/LSB-Core-generic/LSB-Core-generic.html)
and [AMD64 ABI §4.2.4](https://refspecs.linuxfoundation.org/elf/x86_64-abi-0.99.pdf).
An FDE is evidence for a contiguous code region, potentially a function fragment.
