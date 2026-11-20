//! Separate source families freeze compiler output before changing discovery.
#[path = "support/module_fixture.rs"]
mod module_fixture;
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use module_fixture::{Case, build, check_generated, expected, state_address};
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Status};

#[path = "support/dispatch_oracle.rs"]
mod dispatch_oracle;
use dispatch_oracle::{inputs, oracle};

#[test]
fn gcc_dispatch_programs_match_native_and_sanitized_backends() {
    matrix("cc", "GCC");
}

#[test]
#[ignore = "requires Clang; set NIRVANA_CLANG and run with --include-ignored"]
fn clang_dispatch_programs_match_native_and_sanitized_backends() {
    let compiler = std::env::var("NIRVANA_CLANG").unwrap_or_else(|_| "clang".into());
    matrix(&compiler, "Clang");
}

fn matrix(compiler: &str, label: &str) {
    let scratch = native::Scratch::new();
    let inputs = inputs();
    let native_text: String = inputs
        .iter()
        .map(|r| format!("{} {} {} {}\n", r[0], r[1], r[2], r[3]))
        .collect();
    let mut native_count = 0;
    let mut generated_count = 0;
    for name in [
        "mapped-switch",
        "state-machine",
        "reused-selector",
        "permuted-machine",
    ] {
        let oracle_rows: Vec<_> = inputs.iter().map(|r| oracle(name, *r)).collect();
        for opt in ["-O0", "-O2"] {
            for pie in [false, true] {
                let directory = scratch.0.join(format!("{name}{opt}-{pie}"));
                std::fs::create_dir(&directory).unwrap();
                let original = directory.join("original");
                build(
                    compiler,
                    &native::fixture_root().join(format!("dispatch-programs/{name}.c")),
                    &original,
                    opt,
                    pie,
                );
                assert_eq!(
                    native::run(&original, &native_text),
                    oracle_rows,
                    "{label} {name} {opt} {pie}: native oracle"
                );
                let module = module_ir::lift_elf(
                    &std::fs::read(&original).unwrap(),
                    "fixture",
                    LinkedOptions {
                        load_bias: if pie { 0x20000 } else { 0 },
                        stack_size: 4096,
                    },
                )
                .unwrap();
                assert!(
                    module.jump_table_diagnostics.is_empty(),
                    "{label} {name} {opt} {pie}: {:?}",
                    module.jump_table_diagnostics
                );
                assert_eq!(
                    module.jump_tables.len(),
                    if name == "reused-selector" { 2 } else { 1 }
                );
                let mut cases: Vec<_> = inputs
                    .iter()
                    .map(|input| Case {
                        input: *input,
                        pc: module.program.entry(),
                        budget: 10_000,
                        patch: None,
                    })
                    .collect();
                let mut rows = Vec::new();
                for (case, oracle) in cases.iter().zip(&oracle_rows) {
                    let (row, status) = expected(&module, case);
                    assert!(
                        matches!(status, Status::Returned(_)),
                        "{label} {name} {opt} {pie}: {status:?}"
                    );
                    assert_eq!(&row[..5], oracle, "{label} {name} {opt} {pie}: native/IR");
                    rows.push(row);
                    native_count += 1;
                }
                for budget in [0, 1, 2, 4, 8, 16, 32, 64, 128] {
                    cases.push(Case {
                        input: [4, 17, 23, 7],
                        pc: module.program.entry(),
                        budget,
                        patch: None,
                    });
                }
                for table in &module.jump_tables {
                    for pc in table.targets() {
                        cases.push(Case {
                            input: [0, 17, 23, 3],
                            pc,
                            budget: 4,
                            patch: None,
                        });
                    }
                }
                let table = &module.jump_tables[0];
                let input = [if name == "mapped-switch" { 1 } else { 0 }, 17, 23, 0];
                let patched = Case {
                    input,
                    pc: module.program.entry(),
                    budget: 10_000,
                    patch: Some((
                        table.entries[0].address,
                        table.entries[1].target.wrapping_sub(table.bias),
                        table.width.bytes(),
                    )),
                };
                assert!(matches!(expected(&module, &patched).1, Status::Returned(_)));
                cases.push(patched.clone());
                let unknown = Case {
                    patch: Some((
                        table.entries[0].address,
                        state_address(&module).wrapping_sub(table.bias),
                        table.width.bytes(),
                    )),
                    ..patched
                };
                assert!(
                    matches!(expected(&module,&unknown).1,Status::UnknownTarget(pc) if pc==state_address(&module))
                );
                cases.push(unknown);
                for case in &cases[inputs.len()..] {
                    rows.push(expected(&module, case).0);
                }
                generated_count += check_generated(&module, &cases, &rows, &directory, true);
                println!(
                    "{label} {name} {opt} PIE={pie}: {} native cases, {} generated inputs/back end, {} context-limited branches",
                    inputs.len(),
                    cases.len(),
                    module.jump_table_context_limits.len()
                );
            }
        }
    }
    println!(
        "dispatch programs {label}:16 profiles, {native_count} native/oracle/IR cases, {generated_count} generated state comparisons with UBSan"
    );
}
