//! Ordinary C binaries, native/oracle results, and computed-target execution.
#[path = "support/module_fixture.rs"]
mod module_fixture;
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use module_fixture::{Case, build, check_generated, expected, state_address};
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Status};
use std::process::Command;

fn inputs() -> Vec<[u64; 4]> {
    let mut result = Vec::new();
    for key in (0..15).chain([
        u64::MAX,
        u64::MAX - 1,
        u64::MAX - 2,
        u64::MAX - 3,
        u64::MAX - 4,
        u64::MAX - 5,
        0x7fff_ffff,
        0x8000_0000,
        1 << 32,
        0xffff_ffff_0000_0004,
    ]) {
        result.push([
            key,
            u64::MAX - 17,
            0x1234_5678_9abc_def0,
            0x1111_3333_5555_7777,
        ]);
    }
    for outer in 0..8 {
        for inner in 0..8 {
            result.push([outer, 17, 23, inner]);
        }
    }
    let mut seed = 0x128a_5376_9172_ef01u64;
    for _ in 0..32 {
        result.push(std::array::from_fn(|_| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        }));
    }
    result
}
fn reference(name: &str, mut r: [u64; 4]) -> Vec<u64> {
    let (a, b, d) = (r[1], r[2], r[3]);
    r[1] = match name {
        "dense-switch" => match r[0] {
            0 => a.wrapping_add(b),
            1 => a.wrapping_mul(3),
            2 => a ^ d,
            3 => a.rotate_left(7),
            4 => a.wrapping_sub(b),
            5 => a.wrapping_add(d.wrapping_mul(5)),
            6 => a.wrapping_add(b ^ d),
            7 => (a >> 3) | (d << 61),
            8 => a ^ (b & d),
            9 => a.wrapping_add(b & 255),
            10 => b.wrapping_add(17),
            11 => (a ^ d).wrapping_mul(7),
            _ => a ^ r[0],
        },
        "biased-switch" => match r[0] as u32 as i32 {
            -4 => a.wrapping_add(b),
            -3 => a ^ d,
            -2 => a.rotate_left(9),
            -1 => a.wrapping_mul(7),
            0 => a.wrapping_sub(b),
            1 => a.wrapping_add(d.wrapping_mul(3)),
            2 => a ^ (b & d),
            3 => b.wrapping_add(11),
            4 => (a >> 5) | (d << 59),
            _ => a ^ r[0],
        },
        "shared-dispatch" => match (r[0] & 3, d & 1) {
            (0, 0) => a.wrapping_add(b),
            (1, 0) => a.wrapping_mul(3),
            (0, 1) => a ^ d,
            (1, 1) => a.wrapping_sub(b),
            _ => a ^ r[0],
        },
        "nested-switch" => match r[0] & 7 {
            0 => a.wrapping_add(b),
            1 => a ^ d,
            2 => a.wrapping_mul(5),
            3 => a.rotate_left(11),
            4 => match d & 7 {
                0 => a.wrapping_sub(b),
                1 => a.wrapping_add(b.wrapping_mul(9)),
                2 => a ^ (b << 3),
                3 => a.rotate_right(7),
                4 => a.wrapping_mul(b),
                5 => a | b,
                _ => a & b,
            },
            5 => a.wrapping_sub(d),
            _ => a.wrapping_add(d & 255),
        },
        _ => panic!("unknown fixture {name}"),
    };
    let value = match name {
        "dense-switch" => r[1] ^ r[0] ^ r[2],
        "biased-switch" => r[1].wrapping_add(r[2]),
        _ => r[1] ^ r[2],
    };
    let mut result = vec![value];
    result.extend(r);
    result
}

#[test]
fn ordinary_switch_binaries_match_native_oracles_and_three_module_backends() {
    switch_matrix("cc", "GCC", true);
}

#[test]
#[ignore = "requires Clang; set NIRVANA_CLANG and run with --include-ignored"]
fn clang_switch_binaries_match_native_oracles_and_three_module_backends() {
    let compiler = std::env::var("NIRVANA_CLANG").unwrap_or_else(|_| "clang".into());
    switch_matrix(&compiler, "Clang", false);
}

fn switch_matrix(compiler: &str, label: &str, include_assembly: bool) {
    let scratch = native::Scratch::new();
    let inputs = inputs();
    let native_text: String = inputs
        .iter()
        .map(|r| format!("{} {} {} {}\n", r[0], r[1], r[2], r[3]))
        .collect();
    let mut generated_cases = 0;
    let mut native_cases = 0;
    let mut mutation_cases = 0;
    let mut profiles = 0;
    for (name, extension, opts) in [
        ("dense-switch", "c", &["-O0", "-O2"][..]),
        ("biased-switch", "c", &["-O0", "-O2"][..]),
        ("nested-switch", "c", &["-O0", "-O2"][..]),
        ("shared-dispatch", "S", &["-O2"][..]),
    ] {
        if extension == "S" && !include_assembly {
            continue;
        }
        let oracle: Vec<_> = inputs.iter().map(|r| reference(name, *r)).collect();
        for &opt in opts {
            for pie in [false, true] {
                let directory = scratch.0.join(format!("{name}{opt}-{pie}"));
                std::fs::create_dir(&directory).unwrap();
                let original = directory.join("original");
                build(
                    compiler,
                    &native::fixture_root().join(format!("input-breadth/{name}.{extension}")),
                    &original,
                    opt,
                    pie,
                );
                let actual = native::run(&original, &native_text);
                assert_eq!(actual, oracle, "{name} {opt} PIE={pie}: native oracle");
                native_cases += inputs.len();
                profiles += 1;
                let bytes = std::fs::read(&original).unwrap();
                let module = module_ir::lift_elf(
                    &bytes,
                    "fixture",
                    LinkedOptions {
                        load_bias: if pie { 0x20000 } else { 0 },
                        stack_size: 4096,
                    },
                )
                .unwrap();
                assert_eq!(
                    module.jump_tables.len(),
                    if matches!(name, "nested-switch" | "shared-dispatch") {
                        2
                    } else {
                        1
                    },
                    "{name} {opt} PIE={pie}: {:?}",
                    module.jump_table_diagnostics
                );
                assert!(module.jump_table_diagnostics.is_empty());
                if name == "shared-dispatch" {
                    assert_eq!(module.jump_tables[0].branch, module.jump_tables[1].branch);
                    assert!(module.jump_table_context_limits.is_empty());
                    assert!(
                        module
                            .jump_tables
                            .iter()
                            .all(|t| t.entry_limit_hint == Some(2) && t.entries.len() == 2)
                    );
                }
                for table in &module.jump_tables {
                    for target in table.targets() {
                        assert!(
                            module
                                .program
                                .instructions()
                                .iter()
                                .any(|i| i.address() == target)
                        );
                    }
                }
                let cli = Command::new(env!("CARGO_BIN_EXE_nirvana"))
                    .arg(&original)
                    .args(["--symbol", "fixture", "--emit", "module-jumps"])
                    .output()
                    .unwrap();
                assert!(cli.status.success());
                let json = String::from_utf8(cli.stdout).unwrap();
                assert!(json.contains("\"complete\":false"));
                assert!(json.contains("\"unknown_target\":true"));
                let mut cases: Vec<_> = inputs
                    .iter()
                    .map(|input| Case {
                        input: *input,
                        pc: module.program.entry(),
                        budget: 10_000,
                        patch: None,
                    })
                    .collect();
                let mut expected_rows = Vec::new();
                for (case, oracle) in cases.iter().zip(&oracle) {
                    let (row, status) = expected(&module, case);
                    assert!(
                        matches!(status, Status::Returned(_)),
                        "{name} {opt} PIE={pie}: {status:?}"
                    );
                    assert_eq!(&row[..5], oracle);
                    expected_rows.push(row);
                }
                for budget in [0, 1, 2, 4, 8, 16, 32, 64] {
                    cases.push(Case {
                        input: [4, 17, 23, 3],
                        pc: module.program.entry(),
                        budget,
                        patch: None,
                    });
                }
                // Every table entry is also tested as a resumption PC. The caller
                // state deliberately has no inherited frame or temporary values.
                for table in &module.jump_tables {
                    for target in table.targets() {
                        cases.push(Case {
                            input: [0, 17, 23, 3],
                            pc: target,
                            budget: 4,
                            patch: None,
                        });
                    }
                }
                if name == "dense-switch" {
                    let table = &module.jump_tables[0];
                    let address = table.entries[0].address;
                    let width = table.width.bytes();
                    let target = table.entries[1].target;
                    let value = target.wrapping_sub(table.bias);
                    let patched = Case {
                        input: [0, 17, 23, 3],
                        pc: module.program.entry(),
                        budget: 1000,
                        patch: Some((address, value, width)),
                    };
                    let (row, status) = expected(&module, &patched);
                    assert!(matches!(status, Status::Returned(_)));
                    assert_eq!(
                        row[2], 51,
                        "a rewritten entry must execute case1 using the actual guest table"
                    );
                    cases.push(patched);
                    mutation_cases += 1;
                    let target = state_address(&module);
                    let value = target.wrapping_sub(table.bias);
                    let unknown = Case {
                        input: [0, 17, 23, 3],
                        pc: module.program.entry(),
                        budget: 1000,
                        patch: Some((address, value, width)),
                    };
                    assert!(
                        matches!(expected(&module,&unknown).1,Status::UnknownTarget(pc) if pc==target)
                    );
                    cases.push(unknown);
                    mutation_cases += 1;
                }
                if name == "shared-dispatch" {
                    for (which, table) in module.jump_tables.iter().enumerate() {
                        let patched = Case {
                            input: [0, 17, 23, which as u64],
                            pc: module.program.entry(),
                            budget: 1000,
                            patch: Some((
                                table.entries[0].address,
                                table.entries[1].target.wrapping_sub(table.bias),
                                table.width.bytes(),
                            )),
                        };
                        let (row, status) = expected(&module, &patched);
                        assert!(matches!(status, Status::Returned(_)));
                        assert_eq!(
                            row[2],
                            if which == 0 {
                                51
                            } else {
                                17u64.wrapping_sub(23)
                            }
                        );
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
                            matches!(expected(&module, &unknown).1, Status::UnknownTarget(pc) if pc == state_address(&module))
                        );
                        cases.push(unknown);
                        mutation_cases += 2;
                    }
                }
                for case in &cases[inputs.len()..] {
                    expected_rows.push(expected(&module, case).0);
                }
                generated_cases += check_generated(
                    &module,
                    &cases,
                    &expected_rows,
                    &directory,
                    label == "Clang",
                );
                println!(
                    "{label} {name} {opt} PIE={pie}: {} native/oracle/module inputs; {} boundary/resume/mutation inputs; three generated backends passed",
                    inputs.len(),
                    cases.len() - inputs.len()
                );
            }
        }
    }
    println!(
        "input breadth {label}: {profiles} binary profiles, {native_cases} native/oracle/module cases, {generated_cases} generated full-state cases, {mutation_cases} table mutations"
    );
}
