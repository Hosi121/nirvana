u64-expression-simplification verification

Snapshot: /tmp/nirvana-simplify-io4f1zo_/project
Write scope: src/simplify.rs, tests/simplify.rs
src/lib.rs has a snapshot-only temporary module declaration; it is not in the patch.

Commands and recorded terminal results:

cargo test --test simplify -- --nocapture
  6 passed, 0 failed, finished in 0.09s
  lazy_select_preserves_condition_faults_and_skips_unselected_faults ... ok
  restores_cmp_formulas_and_inverts_boolean_comparisons ... ok
  identities_and_coefficient_combining_do_not_assume_no_overflow ... ok
  faulting_operands_are_never_discarded_duplicated_or_reordered ... ok
  all_binary_operators_fold_constants_with_u64_semantics ... ok
  seeded_expression_trees_match_the_original_ir_interpreter ... ok
  1024 seeded expression trees: 31370 -> 12583 nodes
  Seed: 0x792c48a91234cdef, depth 4
  23 boundary register vectors, three memory layouts, two instruction limits
  141312 generated-tree execution comparisons plus 6877 constant-fold comparisons
  Execution equality includes return, registers, original trace, memory, or exact error.
  Faulting-load regression cases also compare static load order and occurrence count.
  Tests assert non-increasing node count and idempotence for checked trees.

cargo clippy --all-targets -- -D warnings
  passed, exit 0

cargo fmt --check
  passed, exit 0

Parent requested no additional broad snapshot test run; integrated suite is parent-owned.
No implementation changes were made after sharing the provisional simplify.rs.
Current parent provisional simplify.rs matches snapshot byte-for-byte: True

SHA-256:
54a2b75fd9546e0e47002d741d2293461197b08efe13ff1406a383eb1b01905d  src/simplify.rs
d3db39041c3c86e0424a32ee3f31bfad363cc92dc54d0ea5d4deeb80bcef35c9  tests/simplify.rs

git apply --check (empty destination for two new files): passed, exit 0

Parent integration:
- Reviewed all rewrite rules for wrapping arithmetic and Load evaluation.
- Both source hashes match the isolated agent result.
- Reduction regressions: five tests passed, including 256 seeded arbitrary CFGs,
  original instruction traces, memory, step limits, and block-exit value swaps.
- Integrated suite: 106 tests passed; cargo clippy --all-targets -- -D warnings
  and cargo fmt --check passed.
- The same 33 machine configurations and 63 inputs each preserve reduced-IR
  return, complete memory, and trace. Recompiled readable C also matches.
- Aggregate reachable-machine assignment count: 5023 -> 668.
