use crate::support::dispatch_oracle;
use crate::support::module_fixture;
use crate::support::native;
use module_fixture::{Case, build, check_generated, compile, expected, state_address};
use nirvana::linked_elf::{self, FunctionOrigin, LinkedOptions};
use nirvana::module_ir::{self, Status};
use std::path::Path;
use std::process::Command;

fn build_modular(compiler: &str, output: &Path, opt: &str, pie: bool) {
    let fixture = native::fixture_root().join("stripped-modules");
    compile(
        Command::new(compiler)
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                "-fno-lto",
                "-fno-stack-protector",
                opt,
            ])
            .args(if pie {
                ["-fPIE", "-pie"]
            } else {
                ["-fno-pie", "-no-pie"]
            })
            .arg(fixture.join("pipeline.c"))
            .arg(fixture.join("stages.c"))
            .arg(fixture.join("table.c"))
            .arg(native::fixture_root().join("harness.c"))
            .arg("-o")
            .arg(output),
    );
}

#[test]
fn gcc_stripped_regions_match_native_and_sanitized_backends() {
    matrix("cc", "GCC");
}

#[test]
#[ignore = "requires Clang; set NIRVANA_CLANG and run with --include-ignored"]
fn clang_stripped_regions_match_native_and_sanitized_backends() {
    matrix(
        &std::env::var("NIRVANA_CLANG").unwrap_or_else(|_| "clang".into()),
        "Clang",
    );
}

fn symbol(binary: &Path, name: &str) -> u64 {
    let output = Command::new("nm")
        .arg("-S")
        .arg("--defined-only")
        .arg(binary)
        .output()
        .unwrap();
    assert!(output.status.success());
    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .find_map(|line| {
            let fields: Vec<_> = line.split_whitespace().collect();
            (fields.last() == Some(&name)).then(|| u64::from_str_radix(fields[0], 16).unwrap())
        })
        .unwrap()
}

fn matrix(compiler: &str, label: &str) {
    let scratch = native::Scratch::new();
    let inputs = dispatch_oracle::inputs();
    let input_text: String = inputs
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
        "modular-pipeline",
    ] {
        let oracle: Vec<_> = inputs
            .iter()
            .map(|r| dispatch_oracle::oracle(name, *r))
            .collect();
        for opt in ["-O0", "-O2"] {
            for pie in [false, true] {
                let directory = scratch.0.join(format!("{name}{opt}-{pie}"));
                std::fs::create_dir(&directory).unwrap();
                let original = directory.join("original");
                if name == "modular-pipeline" {
                    build_modular(compiler, &original, opt, pie);
                } else {
                    build(
                        compiler,
                        &native::fixture_root().join(format!("dispatch-programs/{name}.c")),
                        &original,
                        opt,
                        pie,
                    );
                }
                assert_eq!(native::run(&original, &input_text), oracle);
                let options = LinkedOptions {
                    load_bias: if pie { 0x320000 } else { 0 },
                    stack_size: 4096,
                };
                let bytes = std::fs::read(&original).unwrap();
                let named = linked_elf::load(&bytes, "fixture", options).unwrap();
                let entry = named.image.function.address - options.load_bias;
                let stripped = directory.join("stripped");
                compile(
                    Command::new("strip")
                        .args(["--strip-all", "-o"])
                        .arg(&stripped)
                        .arg(&original),
                );
                assert_eq!(
                    native::run(&stripped, &input_text),
                    oracle,
                    "{label} {name} {opt} PIE={pie}: stripped native"
                );
                let bytes = std::fs::read(&stripped).unwrap();
                assert!(matches!(
                    linked_elf::load(&bytes, "fixture", options),
                    Err(linked_elf::BinaryError::MissingFunction(_))
                ));
                let image = linked_elf::load_at(&bytes, entry, options).unwrap();
                let root = image
                    .functions
                    .iter()
                    .find(|f| f.address == entry + options.load_bias)
                    .unwrap();
                assert!(matches!(root.origin, FunctionOrigin::Unwind { .. }));
                assert_eq!(image.image.function.bytes, named.image.function.bytes);
                let result = module_ir::lift_elf_at(&bytes, entry, options);
                let module =
                    result.unwrap_or_else(|e| panic!("{label} {name} {opt} PIE={pie}: {e}"));
                assert!(
                    module.jump_table_diagnostics.is_empty(),
                    "{:?}",
                    module.jump_table_diagnostics
                );
                if name == "modular-pipeline" {
                    for helper in ["stage_add", "stage_fold", "stage_mix"] {
                        let address = symbol(&original, helper) + options.load_bias;
                        assert!(
                            module
                                .program
                                .functions()
                                .iter()
                                .any(|f| f.address == address)
                        );
                    }
                }
                let mut cases: Vec<_> = inputs
                    .iter()
                    .map(|r| Case {
                        input: *r,
                        pc: module.program.entry(),
                        budget: 10_000,
                        patch: None,
                    })
                    .collect();
                let mut rows = Vec::new();
                for (case, oracle) in cases.iter().zip(&oracle) {
                    let (row, status) = expected(&module, case);
                    assert!(
                        matches!(status, Status::Returned(_)),
                        "{label} {name} {opt} PIE={pie}: {status:?}"
                    );
                    assert_eq!(
                        &row[..5],
                        oracle,
                        "{label} {name} {opt} PIE={pie}: native/IR"
                    );
                    rows.push(row);
                    native_count += 1;
                }
                for budget in [0, 1, 2, 4, 8, 16, 32, 64, 128] {
                    cases.push(Case {
                        input: [3, 0, 0, 3],
                        pc: module.program.entry(),
                        budget,
                        patch: None,
                    });
                }
                for function in module.program.functions() {
                    cases.push(Case {
                        input: [3, 17, 23, 3],
                        pc: function.address,
                        budget: 4,
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
                    for target in [table.entries[0].target, state_address(&module)] {
                        cases.push(Case {
                            input: [if name == "mapped-switch" { 1 } else { 0 }, 17, 23, 0],
                            pc: module.program.entry(),
                            budget: 10_000,
                            patch: Some((
                                table.entries[0].address,
                                target.wrapping_sub(table.bias),
                                table.width.bytes(),
                            )),
                        });
                    }
                }
                if name == "modular-pipeline" {
                    for target in [
                        symbol(&original, "stage_mix") + options.load_bias,
                        state_address(&module),
                        module.image.memory_base,
                    ] {
                        let case = Case {
                            input: [3, 0, 0, 0],
                            pc: module.program.entry(),
                            budget: 10_000,
                            patch: Some((
                                symbol(&original, "stage_table") + options.load_bias,
                                target,
                                8,
                            )),
                        };
                        if target == state_address(&module) {
                            assert!(
                                matches!(expected(&module, &case).1, Status::UnknownTarget(pc) if pc == target)
                            );
                        }
                        cases.push(case);
                    }
                }
                for case in &cases[inputs.len()..] {
                    rows.push(expected(&module, case).0);
                }
                generated_count += check_generated(&module, &cases, &rows, &directory, true);
                println!(
                    "{label} stripped {name} {opt} PIE={pie}: {} native cases, {} C inputs/backend",
                    inputs.len(),
                    cases.len()
                );
            }
        }
    }
    println!(
        "stripped {label}:20 profiles, {native_count} native/oracle/IR cases, {generated_count} generated state comparisons with UBSan"
    );
}
