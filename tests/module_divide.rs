#[path = "support/module_fixture.rs"]
#[allow(dead_code)]
mod module_fixture;
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use module_fixture::{
    Case, check_generated_with_state, compile, expected_with_state, prepare_with_state,
    state_address,
};
use nirvana::ir::Width;
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Instruction, Limits, RejectImports, Status};
use nirvana::x86::{self, Operation};
use std::path::Path;
use std::process::Command;

fn build(source: &str, directory: &Path, pie: bool) -> module_ir::Module {
    let file = directory.join("fixture.S");
    let binary = directory.join("fixture");
    std::fs::write(&file, source).unwrap();
    compile(
        Command::new("cc")
            .args(["-nostdlib", "-Wl,-e,fixture"])
            .args(if pie {
                ["-fPIE", "-pie"]
            } else {
                ["-fno-pie", "-no-pie"]
            })
            .arg(&file)
            .arg("-o")
            .arg(&binary),
    );
    module_ir::lift_elf(
        &std::fs::read(binary).unwrap(),
        "fixture",
        LinkedOptions {
            load_bias: if pie { 0x230000 } else { 0 },
            stack_size: 4096,
        },
    )
    .unwrap()
}
fn assert_local_divisions(module: &module_ir::Module) {
    let values = nirvana::module_values::analyze(&module.program).unwrap();
    let plan = nirvana::module_local_plan::recover(&module.program, &values).unwrap();
    for instruction in module.program.instructions() {
        if matches!(instruction, Instruction::Divide { .. }) {
            let function = module
                .program
                .functions()
                .iter()
                .find(|f| (f.address..f.address + f.size).contains(&instruction.address()))
                .unwrap();
            let local = plan
                .functions
                .iter()
                .find(|f| f.address == function.address)
                .unwrap()
                .result
                .as_ref()
                .unwrap();
            assert!(local.steps[&instruction.address()].assignments.is_empty());
        }
    }
    let output = nirvana::module_readable::emit_c_with_locals(module).unwrap();
    assert_eq!(output.report.local_fallback_functions, 0);
}
fn assembly(width: Width, signed: bool, form: usize, wrapper: bool) -> String {
    let index = width.bytes().trailing_zeros() as usize;
    let operand = match form {
        0 => ["%r9b", "%r9w", "%r9d", "%r9"][index],
        1 => "16(%rdi)",
        2 => ["%al", "%ax", "%eax", "%rax"][index],
        3 => ["%dl", "%dx", "%edx", "%rdx"][index],
        4 => "%ah",
        5 => "(%r8)",
        6 => "(%rax)",
        7 => "(%rdx)",
        _ => unreachable!(),
    };
    let mnemonic = format!(
        "{}{}",
        if signed { "idiv" } else { "div" },
        ["b", "w", "l", "q"][index]
    );
    let mut code = String::from(".text\n.globl fixture\n.type fixture,@function\nfixture:\n");
    if wrapper {
        code.push_str("movq $165,24(%rdi)\ncall nv_division_body\nret\n.size fixture,.-fixture\n.type nv_division_body,@function\nnv_division_body:\n");
    }
    code.push_str(&format!("mov 0(%rdi),%rax\nmov 8(%rdi),%rdx\nmov 16(%rdi),%r9\nmov 24(%rdi),%r8\n{mnemonic} {operand}\nmov %rax,0(%rdi)\nmov %rdx,8(%rdi)\nret\n"));
    code.push_str(if wrapper {
        ".size nv_division_body,.-nv_division_body\n"
    } else {
        ".size fixture,.-fixture\n"
    });
    code.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    code
}
fn initial(module: &module_ir::Module) -> Vec<u64> {
    let mut registers = module.initial_registers();
    for (i, value) in registers.iter_mut().enumerate() {
        if i == x86::RSP {
            continue;
        }
        *value = if (16..=20).contains(&i) {
            (i & 1) as u64
        } else {
            0x71a2_b35c_d46e_f789u64.wrapping_mul(i as u64 + 1)
        };
    }
    registers
}

#[test]
fn division_in_loop_diamond_preserves_saved_values_phis_and_every_pc_resume() {
    let scratch = native::Scratch::new();
    for pie in [false, true] {
        let directory = scratch.0.join(format!("loop-{pie}"));
        std::fs::create_dir(&directory).unwrap();
        let module = build(include_str!("fixtures/division-values.S"), &directory, pie);
        assert_local_divisions(&module);
        let registers = initial(&module);
        let mut cases = Vec::new();
        let mut rows = Vec::new();
        for input in [
            [13, 3, 0, 19],
            [13, 3, 1, 19],
            [u64::MAX, 7, 3, 19],
            [17, 0, 5, 19],
        ] {
            let case = Case {
                input,
                pc: module.program.entry(),
                budget: 200,
                patch: None,
            };
            let (row, status) = expected_with_state(&module, &case, Some(&registers));
            if input[1] != 0 {
                let mut value = input[0];
                let mut saved = input[2];
                let mut remainder = 0;
                for _ in 0..3 {
                    remainder = value % input[1];
                    if saved & 1 != 0 {
                        saved = saved.wrapping_add(remainder);
                    }
                    value = (value / input[1]).wrapping_add(value);
                }
                assert!(matches!(status, Status::Returned(_)));
                assert_eq!(&row[..5], &[value, value, remainder, saved, input[3]]);
            } else {
                assert_eq!(status, Status::DivideError);
            }
            cases.push(case);
            rows.push(row);
        }
        for instruction in module.program.instructions() {
            for budget in [0, 1, 2, 8, 40, 200] {
                for divisor in [0, 3] {
                    let case = Case {
                        input: [13, divisor, 5, 19],
                        pc: instruction.address(),
                        budget,
                        patch: None,
                    };
                    rows.push(expected_with_state(&module, &case, Some(&registers)).0);
                    cases.push(case);
                }
            }
        }
        check_generated_with_state(
            &module,
            &cases,
            &rows,
            &directory,
            true,
            &[1, 2, 64],
            Some(&registers),
        );
    }
}

#[test]
fn divide_effects_preserve_fault_pc_budget_and_full_state_in_three_backends() {
    let scratch = native::Scratch::new();
    let mut profiles = 0;
    let mut comparisons = 0;
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for signed in [false, true] {
            for form in 0..8 {
                if form == 4 && width != Width::U8 {
                    continue;
                }
                for wrapper in [false, true] {
                    if wrapper && !(width == Width::U64 && form <= 1) {
                        continue;
                    }
                    for pie in [false, true] {
                        let directory = scratch
                            .0
                            .join(format!("{}-{signed}-{form}-{wrapper}-{pie}", width.bits()));
                        std::fs::create_dir(&directory).unwrap();
                        let module =
                            build(&assembly(width, signed, form, wrapper), &directory, pie);
                        assert_local_divisions(&module);
                        let registers = initial(&module);
                        let divide = module
                            .program
                            .instructions()
                            .iter()
                            .find(|i| matches!(i, Instruction::Divide { .. }))
                            .unwrap();
                        let divisor_pc = divide.address();
                        let state = state_address(&module);
                        let mask = width.mask();
                        let half = 1u64 << (width.bits() - 1);
                        let values = [0, 1, 2, 3, half - 1, half, half + 1, mask - 1, mask];
                        let mut cases = Vec::new();
                        for (i, &a) in values.iter().enumerate() {
                            for (j, &d) in values.iter().enumerate() {
                                let mut input = [
                                    a | (!mask & 0x8123_4567_89ab_cdef),
                                    d | (!mask & 0xf123_4567_89ab_cdef),
                                    values[(i + j) % values.len()],
                                    state + 16,
                                ];
                                if width == Width::U8 {
                                    input[0] = (input[0] & !0xffff) | a | (d << 8);
                                }
                                if form == 6 {
                                    input[0] = state + 16;
                                }
                                if form == 7 {
                                    input[1] = state + 16;
                                }
                                cases.push(Case {
                                    input,
                                    pc: module.program.entry(),
                                    budget: 100,
                                    patch: None,
                                });
                            }
                        }
                        if form == 5 {
                            for pointer in [
                                module.image.memory_base.wrapping_sub(1),
                                module.image.memory_base + module.image.memory.len() as u64,
                                u64::MAX,
                            ] {
                                cases.push(Case {
                                    input: [0, u64::MAX, 0, pointer],
                                    pc: module.program.entry(),
                                    budget: 100,
                                    patch: None,
                                });
                            }
                        }
                        for budget in 0..=12 {
                            cases.push(Case {
                                input: [0, 0, 0, state + 16],
                                pc: module.program.entry(),
                                budget,
                                patch: None,
                            });
                        }
                        for instruction in module.program.instructions() {
                            for budget in [0, 1, 3] {
                                cases.push(Case {
                                    input: [0, 0, 3, state + 16],
                                    pc: instruction.address(),
                                    budget,
                                    patch: None,
                                });
                            }
                        }
                        let mut rows = Vec::new();
                        for case in &cases {
                            let (row, status) =
                                expected_with_state(&module, case, Some(&registers));
                            if case.pc == module.program.entry() && case.budget == 100 {
                                let (a, d, source) = (
                                    case.input[0],
                                    case.input[1],
                                    match form {
                                        0 | 1 | 5 | 6 | 7 => case.input[2],
                                        2 => case.input[0],
                                        3 => case.input[1],
                                        4 => case.input[0] >> 8,
                                        _ => unreachable!(),
                                    },
                                );
                                let result = x86::divide::evaluate(width, signed, a, d, source);
                                if form == 5
                                    && (case.input[3] < module.image.memory_base
                                        || case.input[3]
                                            >= module.image.memory_base
                                                + module.image.memory.len() as u64)
                                {
                                    assert!(
                                        matches!(status,Status::Fault(f) if f.address==case.input[3] && f.width==width.bytes()as u64)
                                    );
                                } else if let Some((a, d)) = result {
                                    assert!(matches!(status,Status::Returned(v) if v==a));
                                    assert_eq!(row[1], a);
                                    assert_eq!(row[2], d);
                                } else {
                                    assert_eq!(status, Status::DivideError);
                                    assert_eq!(row[6], divisor_pc);
                                }
                                if matches!(status, Status::DivideError | Status::Fault(_)) {
                                    let (r, m) =
                                        prepare_with_state(&module, case, Some(&registers));
                                    let before = module
                                        .program
                                        .run(
                                            &r,
                                            module.image.memory_base,
                                            &m,
                                            Limits {
                                                instructions: if wrapper { 6 } else { 4 },
                                                imports: 0,
                                            },
                                            &mut RejectImports,
                                        )
                                        .unwrap();
                                    assert_eq!(before.pc, divisor_pc);
                                    let after = module
                                        .program
                                        .run(
                                            &r,
                                            module.image.memory_base,
                                            &m,
                                            Limits {
                                                instructions: 100,
                                                imports: 0,
                                            },
                                            &mut RejectImports,
                                        )
                                        .unwrap();
                                    assert_eq!(
                                        after.state.registers, before.state.registers,
                                        "#DE/RAM fault changes no registers at the division"
                                    );
                                    assert_eq!(after.state.memory, before.state.memory);
                                }
                            }
                            rows.push(row);
                        }
                        comparisons += check_generated_with_state(
                            &module,
                            &cases,
                            &rows,
                            &directory,
                            true,
                            &[64],
                            Some(&registers),
                        );
                        profiles += 1;
                    }
                }
            }
        }
    }
    println!(
        "{profiles} division instruction profiles; {comparisons} full-state generated comparisons with UBSan"
    );
}

#[test]
fn division_decoding_is_module_only_and_undefined_flags_stay_unavailable() {
    for bytes in [
        &[0xf6, 0xf4][..],
        &[0x66, 0xf7, 0xf9],
        &[0xf7, 0xf2],
        &[0x48, 0xf7, 0xf1],
        &[0x41, 0xf6, 0xf1],
    ] {
        assert!(x86::decode_at(bytes, 0x1000).is_err());
        assert!(matches!(
            x86::decode_reference_at(bytes, 0x1000).unwrap().operation,
            Operation::Divide { .. }
        ));
    }
    assert!(x86::decode_reference_at(&[0xf0, 0x48, 0xf7, 0xf1], 0x1000).is_err());
    let scratch = native::Scratch::new();
    for redefine in [false, true] {
        let source = format!(
            ".text\n.globl fixture\n.type fixture,@function\nfixture:\nmov $1,%eax\nxor %edx,%edx\nmov $1,%ecx\ndiv %ecx\n{}jz 1f\nmov $7,%eax\n1:ret\n.size fixture,.-fixture\n.section .note.GNU-stack,\"\",@progbits\n",
            if redefine { "test %eax,%eax\n" } else { "" }
        );
        let file = scratch.0.join("flags.S");
        let binary = scratch.0.join("flags");
        std::fs::write(&file, source).unwrap();
        compile(
            Command::new("cc")
                .args(["-nostdlib", "-no-pie", "-Wl,-e,fixture"])
                .arg(&file)
                .arg("-o")
                .arg(&binary),
        );
        let result = module_ir::lift_elf(
            &std::fs::read(binary).unwrap(),
            "fixture",
            LinkedOptions {
                load_bias: 0,
                stack_size: 4096,
            },
        );
        if redefine {
            assert!(result.is_ok());
        } else {
            assert!(result.unwrap_err().to_string().contains("flag"));
        }
    }
}

#[test]
fn cwd_cdq_cqo_match_native_and_preserve_partial_register_bits() {
    let scratch = native::Scratch::new();
    let inputs: Vec<_> = [
        0,
        1,
        0x7fff,
        0x8000,
        0xffff,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_ffff,
        1u64 << 63,
        u64::MAX,
    ]
    .into_iter()
    .map(|a| [a, 0xabcd_1234_9876_fedc, 17, 23])
    .collect();
    let text: String = inputs
        .iter()
        .map(|r| format!("{} {} {} {}\n", r[0], r[1], r[2], r[3]))
        .collect();
    for (width, mnemonic) in [
        (Width::U16, "cwd"),
        (Width::U32, "cdq"),
        (Width::U64, "cqo"),
    ] {
        for pie in [false, true] {
            let directory = scratch.0.join(format!("sign-{}-{pie}", width.bits()));
            std::fs::create_dir(&directory).unwrap();
            let source = directory.join("fixture.S");
            let binary = directory.join("native");
            std::fs::write(&source,format!(".text\n.globl fixture\n.type fixture,@function\nfixture:\nmov 0(%rdi),%rax\nmov 8(%rdi),%rdx\n{mnemonic}\nmov %rdx,8(%rdi)\nret\n.size fixture,.-fixture\n.section .note.GNU-stack,\"\",@progbits\n")).unwrap();
            compile(
                Command::new("cc")
                    .args(["-O2", "-fno-stack-protector"])
                    .args(if pie {
                        ["-fPIE", "-pie"]
                    } else {
                        ["-fno-pie", "-no-pie"]
                    })
                    .arg(&source)
                    .arg(native::fixture_root().join("harness.c"))
                    .arg("-o")
                    .arg(&binary),
            );
            let oracle: Vec<_> = inputs
                .iter()
                .map(|r| {
                    let sign = (r[0] >> (width.bits() - 1)) & 1;
                    let d = 0u64.wrapping_sub(sign) & width.mask();
                    vec![
                        r[0],
                        r[0],
                        if width == Width::U16 {
                            r[1] & !width.mask() | d
                        } else {
                            d
                        },
                        r[2],
                        r[3],
                    ]
                })
                .collect();
            assert_eq!(native::run(&binary, &text), oracle);
            let module = module_ir::lift_elf(
                &std::fs::read(binary).unwrap(),
                "fixture",
                LinkedOptions {
                    load_bias: if pie { 0x230000 } else { 0 },
                    stack_size: 4096,
                },
            )
            .unwrap();
            let registers = initial(&module);
            let cases: Vec<_> = inputs
                .iter()
                .map(|r| Case {
                    input: *r,
                    pc: module.program.entry(),
                    budget: 100,
                    patch: None,
                })
                .collect();
            let rows: Vec<_> = cases
                .iter()
                .zip(&oracle)
                .map(|(case, oracle)| {
                    let (row, status) = expected_with_state(&module, case, Some(&registers));
                    assert!(matches!(status, Status::Returned(_)));
                    assert_eq!(&row[..5], oracle);
                    row
                })
                .collect();
            check_generated_with_state(
                &module,
                &cases,
                &rows,
                &directory,
                true,
                &[64],
                Some(&registers),
            );
        }
    }
}
