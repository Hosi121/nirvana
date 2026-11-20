//! Separate source families freeze compiler output before changing discovery.
#[path = "support/module_fixture.rs"]
mod module_fixture;
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use module_fixture::{Case, build, check_generated, expected, state_address};
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Status};

const CLASSES: [u64; 32] = [
    3, 0, 7, 2, 5, 1, 6, 4, 1, 7, 2, 6, 0, 5, 4, 3, 6, 2, 4, 0, 7, 3, 1, 5, 4, 5, 0, 1, 3, 6, 2, 7,
];

fn inputs() -> Vec<[u64; 4]> {
    let mut inputs = Vec::new();
    for key in 0..64u64 {
        inputs.push([key, 17 ^ (key << 58), u64::MAX - 23 + key / 8, key / 8]);
    }
    for key in [
        0,
        1,
        7,
        8,
        15,
        31,
        32,
        63,
        64,
        u64::MAX,
        u64::MAX - 1,
        u64::MAX - 7,
        0x7fff_ffff,
        0x8000_0000,
        1 << 32,
        1 << 63,
    ] {
        inputs.push([key, u64::MAX, 0x1234_5678_9abc_def0, 0x8765_4321_1234_5678]);
    }
    let mut seed = 0x89bd_37a1_c125_ef23u64;
    for _ in 0..64 {
        inputs.push(std::array::from_fn(|_| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        }));
    }
    inputs
}

fn oracle(name: &str, mut r: [u64; 4]) -> Vec<u64> {
    let (a, b, d) = (r[1], r[2], r[3]);
    match name {
        "mapped-switch" => {
            let key = CLASSES[((r[0] ^ d) & 31) as usize];
            r[1] = match key {
                0 => a.wrapping_add(b.wrapping_mul(3)),
                1 => a.rotate_left(9),
                2 => a ^ b.wrapping_add(d),
                3 => a.wrapping_sub(d.wrapping_mul(5)),
                4 => (a ^ b).wrapping_mul(7),
                5 => a.wrapping_add(b & 1023),
                6 => (a >> 11) | (b << 53),
                _ => (a | b) ^ d,
            };
            r[2] = b.wrapping_add(key);
        }
        "state-machine" => {
            let mut phase = r[0] & 7;
            let (mut value, mut total) = (a, b);
            for _ in 0..(d & 7) + 1 {
                phase = match phase {
                    0 => {
                        value = value.wrapping_add(total);
                        3
                    }
                    1 => {
                        total ^= value;
                        6
                    }
                    2 => {
                        value = value.rotate_left(5);
                        7
                    }
                    3 => {
                        value = value.wrapping_mul(3);
                        1
                    }
                    4 => {
                        total = total.wrapping_add(value ^ 0xa5);
                        0
                    }
                    5 => {
                        value = value.wrapping_sub(total);
                        2
                    }
                    6 => {
                        total = total.rotate_right(7);
                        5
                    }
                    _ => {
                        value ^= total.wrapping_add(17);
                        4
                    }
                };
                phase ^= value & 3;
            }
            r[0] = phase;
            r[1] = value;
            r[2] = total;
        }
        "reused-selector" => {
            let first = match r[0] & 7 {
                0 => a.wrapping_add(b),
                1 => a.wrapping_mul(5),
                2 => a ^ d,
                3 => a.rotate_left(7),
                4 => a.wrapping_sub(b),
                5 => a.wrapping_add(b & 255),
                6 => a | d,
                _ => a & b,
            };
            let second = (first ^ b) & 7;
            r[1] = match second {
                0 => first.wrapping_add(11),
                1 => first ^ 0x55,
                2 => first.wrapping_mul(9),
                3 => first.rotate_right(3),
                4 => first.wrapping_sub(d),
                5 => first | b,
                6 => first & d,
                _ => first ^ b,
            };
            r[2] = second;
        }
        _ => panic!("unknown fixture {name}"),
    }
    let value = match name {
        "mapped-switch" => r[1] ^ r[2] ^ r[3],
        "state-machine" => r[1] ^ r[2] ^ r[0],
        _ => r[1] ^ r[2],
    };
    let mut result = vec![value];
    result.extend(r);
    result
}

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
    for name in ["mapped-switch", "state-machine", "reused-selector"] {
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
        "dispatch programs {label}:12 profiles, {native_count} native/oracle/IR cases, {generated_count} generated state comparisons with UBSan"
    );
}
