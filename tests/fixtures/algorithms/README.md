# Algorithms and data structures

Five C11 fixtures use `uint64_t fixture(uint64_t state[4])`. Their source names
identify the evaluation corpus. The decompiler receives the object bytes and
entry symbol; recovered field and array layouts are candidates inferred from
memory accesses.

| Fixture | Input state | Output state |
| --- | --- | --- |
| BFS | adjacency bits, graph configuration, XOR seed, unused | visited mask, count, discovery order, distance sum |
| DFS | adjacency bits, graph configuration, XOR seed, unused | visited mask, count, discovery order, maximum depth |
| Ring queue | operation bits, operation count, initial value, checksum seed | queue count, rejected operations, checksum, next value |
| Linked list | successor nibbles, node configuration, value bytes, traversal limit | value sum, steps, visited mask, traversal hash |
| BST lookup | minimum key, key spacing, lookup key, path seed | found flag, found key, comparisons, path hash |

Graphs have 1–8 vertices. Bit `8*u+v` is edge `u -> v`; configuration selects
`n = (state[1] & 7) + 1` and `start = min((state[1] >> 3) & 7, n - 1)`.
The queue has eight slots, list traversal takes at most 16 steps, and the BST
has seven nodes. Queue entries, DFS frames, list nodes and tree nodes use C
structs. Source comments and the [independent Rust oracles](../../end_to_end/algorithm_fixtures.rs)
define the remaining encodings and return values. All four-word inputs are valid.

```sh
cargo test --test end_to_end algorithm_fixtures:: -- --nocapture
```

Each source is compiled at O0/O2 with C11, strict warnings, `-fno-lto` and
`-fno-stack-protector`. The same object is linked for native execution and passed
to the decompiler. The explicit stack setting selects the standalone function
ABI; the host compiler's default canary profile requires TLS and
`__stack_chk_fail` support. Vectorization follows the compiler's ordinary choices.

The corpus includes boundary cases and deterministic random inputs: BFS/DFS
84 each, queue 88, list 86, and BST 83. Native execution is compared with Rust
oracles. Core and readable C are each recompiled at O0/O2 and compared with
binary IR, including an FNV-1a digest of all 8192 guest RAM bytes.

On GCC 13.3.0, nine of ten ordinary frontend profiles pass: 850 native/oracle
cases, 767 IR cases and 3068 generated-C cases. BST O2 struct initialization
uses `movq` into XMM (`0f 6e`), which the ordinary frontend reports explicitly.
The test applies the positive checks automatically when that profile is accepted.

The linked module backend handles those vector instructions. A separate BST O2
test checks all 83 inputs against native/model results and 166 generated-C runs,
including all 80 registers, PC, budgets, instruction counts and the full guest
RAM digest. The ordinary frontend profile and module profile retain their
separate results.
