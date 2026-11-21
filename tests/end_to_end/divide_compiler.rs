use crate::support::module_fixture;
use crate::support::native;
use module_fixture::{Case, build, check_generated_with_state, compile, expected_with_state};
use nirvana::linked_elf::{self, LinkedOptions};
use nirvana::module_ir::{self, Instruction, Status};
use std::process::Command;

fn oracle(mut state: [u64; 4], bits: u32, signed: bool) -> Vec<u64> {
    let valid = if signed {
        let value = if bits == 64 {
            state[0] as i64
        } else {
            state[0] as i32 as i64
        };
        let divisor = if bits == 64 {
            state[1] as i64
        } else {
            state[1] as i32 as i64
        };
        let minimum = if bits == 64 {
            i64::MIN
        } else {
            i32::MIN as i64
        };
        if divisor == 0 || (value == minimum && divisor == -1) {
            false
        } else {
            state[2] = (value / divisor) as u64;
            state[3] = (value % divisor) as u64;
            true
        }
    } else {
        let mask = if bits == 64 {
            u64::MAX
        } else {
            u32::MAX as u64
        };
        let value = state[0] & mask;
        let divisor = state[1] & mask;
        if let Some(quotient) = value.checked_div(divisor) {
            state[2] = quotient;
            state[3] = value % divisor;
            true
        } else {
            false
        }
    };
    let result = if valid {
        state[2] ^ state[3]
    } else {
        state[3] = 1;
        0
    };
    let mut out = vec![result];
    out.extend(state);
    out
}
#[test]
fn gcc_runtime_quotient_remainder_match_native_and_sanitized_c() {
    matrix("cc", "GCC");
}
#[test]
#[ignore = "requires Clang; set NIRVANA_CLANG"]
fn clang_runtime_quotient_remainder_match_native_and_sanitized_c() {
    matrix(
        &std::env::var("NIRVANA_CLANG").unwrap_or_else(|_| "clang".into()),
        "Clang",
    );
}

fn matrix(compiler: &str, label: &str) {
    let scratch = native::Scratch::new();
    let mut inputs = Vec::new();
    let points = [
        0,
        1,
        2,
        3,
        7,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_ffff,
        0x7fff_ffff_ffff_ffff,
        1u64 << 63,
        u64::MAX - 1,
        u64::MAX,
    ];
    for a in points {
        for b in points {
            inputs.push([a, b, 0xabcdef1234567890, 0x76543210fedcba98]);
        }
    }
    let mut seed = 0x61ab_23cd_45ef_7890u64;
    for _ in 0..64 {
        inputs.push(std::array::from_fn(|_| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        }));
    }
    let text: String = inputs
        .iter()
        .map(|r| format!("{} {} {} {}\n", r[0], r[1], r[2], r[3]))
        .collect();
    let mut native_cases = 0;
    let mut generated = 0;
    for bits in [32, 64] {
        for signed in [false, true] {
            for opt in ["-O0", "-O2"] {
                for pie in [false, true] {
                    let directory = scratch.0.join(format!("{bits}-{signed}-{opt}-{pie}"));
                    std::fs::create_dir(&directory).unwrap();
                    let source = directory.join("source.c");
                    let original = directory.join("original");
                    let stripped = directory.join("stripped");
                    std::fs::write(
                        &source,
                        format!(
                            "#define NV_BITS {bits}\n#define NV_SIGNED {}\n{}",
                            u8::from(signed),
                            include_str!("../fixtures/division-runtime.c")
                        ),
                    )
                    .unwrap();
                    build(compiler, &source, &original, opt, pie);
                    let oracle: Vec<_> = inputs.iter().map(|r| oracle(*r, bits, signed)).collect();
                    assert_eq!(native::run(&original, &text), oracle);
                    let options = LinkedOptions {
                        load_bias: if pie { 0x230000 } else { 0 },
                        stack_size: 4096,
                    };
                    let named =
                        linked_elf::load(&std::fs::read(&original).unwrap(), "fixture", options)
                            .unwrap();
                    let entry = named.image.function.address - options.load_bias;
                    compile(
                        Command::new("strip")
                            .args(["--strip-all", "-o"])
                            .arg(&stripped)
                            .arg(&original),
                    );
                    assert_eq!(native::run(&stripped, &text), oracle);
                    let module =
                        module_ir::lift_elf_at(&std::fs::read(stripped).unwrap(), entry, options)
                            .unwrap();
                    let locals = nirvana::module_readable::emit_c_with_locals(&module).unwrap();
                    assert_eq!(
                        locals.report.local_fallback_functions, 0,
                        "{label} {bits} {signed} {opt} {pie}"
                    );
                    assert!(
                        module
                            .program
                            .instructions()
                            .iter()
                            .any(|i| matches!(i, Instruction::Divide { .. })),
                        "{label} {bits} {signed} {opt} {pie}"
                    );
                    let mut registers = module.initial_registers();
                    for (i, r) in registers.iter_mut().enumerate() {
                        if i != 4 {
                            *r = if (16..=20).contains(&i) {
                                i as u64 & 1
                            } else {
                                0x71e2_43a6_851b_27cdu64.wrapping_mul(i as u64 + 1)
                            };
                        }
                    }
                    let mut cases: Vec<_> = inputs
                        .iter()
                        .map(|r| Case {
                            input: *r,
                            pc: module.program.entry(),
                            budget: 1000,
                            patch: None,
                        })
                        .collect();
                    let mut rows = Vec::new();
                    for (case, oracle) in cases.iter().zip(&oracle) {
                        let (row, status) = expected_with_state(&module, case, Some(&registers));
                        assert!(matches!(status, Status::Returned(_)));
                        assert_eq!(&row[..5], oracle);
                        rows.push(row);
                        native_cases += 1;
                    }
                    for budget in 0..=20 {
                        cases.push(Case {
                            input: [13, 3, 17, 23],
                            pc: module.program.entry(),
                            budget,
                            patch: None,
                        });
                    }
                    for division in module
                        .program
                        .instructions()
                        .iter()
                        .filter(|i| matches!(i, Instruction::Divide { .. }))
                    {
                        for budget in [0, 1, 2] {
                            cases.push(Case {
                                input: [13, 3, 17, 23],
                                pc: division.address(),
                                budget,
                                patch: None,
                            });
                        }
                    }
                    for case in &cases[inputs.len()..] {
                        rows.push(expected_with_state(&module, case, Some(&registers)).0);
                    }
                    generated += check_generated_with_state(
                        &module,
                        &cases,
                        &rows,
                        &directory,
                        true,
                        &[64],
                        Some(&registers),
                    );
                    println!(
                        "{label} runtime div{bits} signed={signed} {opt} PIE={pie}:{} native cases,{} generated inputs/backend",
                        inputs.len(),
                        cases.len()
                    );
                }
            }
        }
    }
    println!(
        "{label} runtime division:16 stripped profiles,{native_cases} native/oracle/IR cases,{generated} generated full-state comparisons"
    );
}
