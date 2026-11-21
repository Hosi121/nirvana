use crate::support::module_fixture::{self, Case};
use crate::support::native;
use nirvana::{
    ir::AccessKind,
    linked_elf::LinkedOptions,
    module_ir::{self, Instruction, Limits, RejectImports, Status},
};
use nirvana::{
    ir::Width,
    x86::{self, StringOperation},
};
use std::time::Duration;
use std::{fmt::Write as _, process::Command};

#[test]
fn move_widths_repeat_prefix_order_and_profile_boundaries_are_explicit() {
    for (bytes, width, repeat) in [
        (&[0xa4][..], Width::U8, false),
        (&[0xa5][..], Width::U32, false),
        (&[0x66, 0xa5][..], Width::U16, false),
        (&[0x48, 0xa5][..], Width::U64, false),
        (&[0xf3, 0xa4][..], Width::U8, true),
        (&[0xf3, 0x66, 0xa5][..], Width::U16, true),
        (&[0x66, 0xf3, 0xa5][..], Width::U16, true),
        (&[0xf3, 0xa5][..], Width::U32, true),
        (&[0xf3, 0x48, 0xa5][..], Width::U64, true),
        (&[0xf3, 0x66, 0x48, 0xa5][..], Width::U64, true),
        (&[0xf3, 0x66, 0x48, 0xa4][..], Width::U8, true),
    ] {
        let decoded = x86::decode_string_at(bytes, 0x1000).unwrap();
        assert_eq!(decoded.size as usize, bytes.len());
        assert_eq!(decoded.operation, StringOperation::Move { width, repeat });
    }
    for bytes in [
        &[][..],
        &[0xf3],
        &[0xf3, 0x48],
        &[0x67, 0xf3, 0xa4],
        &[0xf2, 0xa4],
        &[0xf0, 0xa5],
        &[0x64, 0xf3, 0xa4],
        &[0xf3, 0xf3, 0xa5],
        &[0x48, 0xf3, 0xa5],
    ] {
        assert!(x86::decode_string_at(bytes, 0).is_err());
    }
    assert!(x86::decode_string_at(&[0xa4], u64::MAX).is_err());
}

#[test]
fn native_moves_match_element_snapshots_overlap_flags_and_fault_progress() {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("native.c");
    std::fs::write(&source, include_str!("../fixtures/movs-native.c")).unwrap();
    for opt in ["-O0", "-O2"] {
        let binary = scratch.0.join(opt);
        native::compile_c(&source, &binary, &[opt, "-mno-red-zone"]);
        let result = native::run_output(&binary, Some(""), Duration::from_secs(5));
        assert!(
            result.status.success(),
            "{opt}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

fn module(scratch: &native::Scratch) -> module_ir::Module {
    let mut assembly = String::from(
        r#"
.text
.globl fixture
.type fixture,@function
fixture:
    mov %rdi,%r8
    mov (%r8),%rcx
    mov 8(%r8),%rsi
    mov 16(%r8),%rdi
    mov 24(%r8),%rax
"#,
    );
    for mode in 0..7 {
        writeln!(assembly, "cmp ${mode},%rax\nje .Lmode{mode}").unwrap();
    }
    assembly.push_str("jmp .Lmode7\n");
    for (index, suffix) in ["b", "w", "l", "q"].into_iter().enumerate() {
        for repeat in [false, true] {
            let mode = index * 2 + usize::from(repeat);
            writeln!(
                assembly,
                ".Lmode{mode}:\n{}movs{suffix}\njmp .Ldone",
                if repeat { "rep " } else { "" }
            )
            .unwrap();
        }
    }
    assembly.push_str(
        r#"
.Ldone:
    mov %rcx,(%r8)
    mov %rsi,8(%r8)
    mov %rdi,16(%r8)
    ret
.size fixture,.-fixture
.globl main
.type main,@function
main: xor %eax,%eax
ret
.size main,.-main
.section .note.GNU-stack,"",@progbits
"#,
    );
    let source = scratch.0.join("moves.S");
    let executable = scratch.0.join("moves");
    std::fs::write(&source, assembly).unwrap();
    native::compile(
        Command::new("cc")
            .args(["-fno-pie", "-no-pie"])
            .arg(&source)
            .arg("-o")
            .arg(&executable),
    );
    module_ir::lift_elf(
        &std::fs::read(executable).unwrap(),
        "fixture",
        LinkedOptions {
            load_bias: 0,
            stack_size: 4096,
        },
    )
    .unwrap()
}

fn reference(
    width: usize,
    repeat: bool,
    mut regs: Vec<u64>,
    mut memory: Vec<u8>,
) -> (Status, Vec<u64>, Vec<u8>) {
    let index = |address: u64| {
        address
            .checked_sub(4096)
            .filter(|&p| p <= (64 - width) as u64)
            .map(|p| p as usize)
    };
    while !repeat || regs[x86::RCX] != 0 {
        let Some(source) = index(regs[x86::RSI]) else {
            return (
                Status::Fault(module_ir::Fault {
                    address: regs[x86::RSI],
                    width: width as u64,
                    access: AccessKind::Read,
                }),
                regs,
                memory,
            );
        };
        let mut element = [0; 8];
        element[..width].copy_from_slice(&memory[source..source + width]);
        let Some(target) = index(regs[x86::RDI]) else {
            return (
                Status::Fault(module_ir::Fault {
                    address: regs[x86::RDI],
                    width: width as u64,
                    access: AccessKind::Write,
                }),
                regs,
                memory,
            );
        };
        memory[target..target + width].copy_from_slice(&element[..width]);
        for reg in [x86::RSI, x86::RDI] {
            regs[reg] = if regs[x86::DF] & 1 == 0 {
                regs[reg].wrapping_add(width as u64)
            } else {
                regs[reg].wrapping_sub(width as u64)
            };
        }
        if repeat {
            regs[x86::RCX] -= 1;
        } else {
            break;
        }
    }
    (
        Status::Suspended(module_ir::Limit::Instructions),
        regs,
        memory,
    )
}

#[test]
fn lifted_moves_match_independent_full_state_oracle_for_faults_aliases_and_zero_count() {
    let scratch = native::Scratch::new();
    let module = module(&scratch);
    assert!(module.program.memory_layout().is_none());
    let mut compared = 0;
    for instruction in module.program.instructions() {
        let Instruction::MoveString {
            address,
            size,
            width,
            repeat,
        } = instruction
        else {
            continue;
        };
        for backwards in [0, 1] {
            for count in [0, 1, 2, 3, 9, u64::MAX] {
                for source in [
                    4096,
                    4097,
                    4104,
                    4112,
                    4128,
                    4151,
                    4152,
                    4153,
                    4159,
                    4160,
                    u64::MAX,
                ] {
                    for destination in [
                        4096,
                        4097,
                        4104,
                        4112,
                        4128,
                        4151,
                        4152,
                        4153,
                        4159,
                        4160,
                        u64::MAX,
                    ] {
                        let mut regs: Vec<_> = (0..80u64)
                            .map(|i| i.wrapping_mul(0xabcdef9876543211))
                            .collect();
                        regs[x86::RSI] = source;
                        regs[x86::RDI] = destination;
                        regs[x86::RCX] = count;
                        regs[x86::DF] = backwards;
                        let memory: Vec<_> = (0..64u8)
                            .map(|i| i.wrapping_mul(29).wrapping_add(7))
                            .collect();
                        for budget in [0, 1] {
                            let (status, expected_regs, expected_memory) = if budget == 0 {
                                (
                                    Status::Suspended(module_ir::Limit::Instructions),
                                    regs.clone(),
                                    memory.clone(),
                                )
                            } else {
                                reference(width.bytes(), *repeat, regs.clone(), memory.clone())
                            };
                            let report = module
                                .program
                                .run_from(
                                    *address,
                                    &regs,
                                    4096,
                                    &memory,
                                    Limits {
                                        instructions: budget,
                                        imports: 0,
                                    },
                                    &mut RejectImports,
                                )
                                .unwrap();
                            assert_eq!(
                                report.status, status,
                                "{width:?}/{repeat}/df={backwards}/{count}/{source}/{destination}"
                            );
                            assert_eq!(report.state.registers, expected_regs);
                            assert_eq!(report.state.memory, expected_memory);
                            assert_eq!(
                                report.state.trace,
                                if budget == 0 { vec![] } else { vec![*address] }
                            );
                            assert_eq!(
                                report.pc,
                                if budget == 0 || matches!(status, Status::Fault(_)) {
                                    *address
                                } else {
                                    address + u64::from(*size)
                                }
                            );
                            compared += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(compared, 23232);
    println!("{compared} MOVS full-register/full-RAM/fault/PC/budget comparisons");
}

#[test]
fn move_boundaries_and_three_c_backends_preserve_full_ram_at_every_pc() {
    let scratch = native::Scratch::new();
    let module = module(&scratch);
    let analysis = nirvana::module_values::analyze(&module.program).unwrap();
    let values = analysis
        .functions
        .iter()
        .find(|f| f.function.address == module.program.entry())
        .unwrap()
        .result
        .as_ref()
        .unwrap();
    let boundaries: Vec<_> = values
        .boundaries()
        .iter()
        .filter(|b| {
            matches!(
                b.kind,
                nirvana::module_values::BoundaryKind::MoveString { .. }
            )
        })
        .collect();
    assert_eq!(boundaries.len(), 8);
    let memory = values.memory().unwrap().as_ref().unwrap();
    assert_eq!(
        memory
            .definitions()
            .iter()
            .filter(|d| matches!(d,
                nirvana::memory_ssa::Definition::Opaque { effect, .. }
                if effect.kind == nirvana::memory_ssa::EffectKind::StringMove
            ))
            .count(),
        8
    );
    for boundary in boundaries {
        let nirvana::module_values::BoundaryKind::MoveString { repeat, .. } = boundary.kind else {
            unreachable!()
        };
        let mut inputs = vec![x86::RSI, x86::RDI, x86::DF];
        let mut outputs = vec![x86::RDI, x86::RSI];
        if repeat {
            inputs.push(x86::RCX);
            outputs.push(x86::RCX);
        }
        assert_eq!(
            boundary
                .inputs
                .iter()
                .map(|v| v.register.0)
                .collect::<Vec<_>>(),
            inputs
        );
        assert_eq!(
            boundary
                .outputs
                .iter()
                .map(|v| v.register.0)
                .collect::<Vec<_>>(),
            outputs
        );
        assert!(
            !boundary
                .preserved
                .iter()
                .any(|v| outputs.contains(&v.register.0))
        );
    }
    let local = nirvana::module_readable::emit_c_with_locals(&module).unwrap();
    assert_eq!(local.report.local_fallback_functions, 0);
    assert!(local.code.contains("nv_movs(s,8,1)"));
    let state = module_fixture::state_address(&module);
    let end = module.image.memory_base + module.image.memory.len() as u64;
    let mut compared = 0;
    for backwards in [0, 1] {
        let mut registers = module.initial_registers();
        for (i, r) in registers.iter_mut().enumerate() {
            if i != x86::RSP {
                *r = 0x123456789abcdef0u64.wrapping_mul(i as u64 + 1);
            }
        }
        registers[x86::DF] = backwards;
        registers[x86::RSI] = state + 64;
        registers[x86::RCX] = 2;
        registers[8] = state;
        let mut cases = Vec::new();
        for mode in 0..8 {
            for count in [0, 1, 3, u64::MAX] {
                for (source, destination) in [
                    (state + 64, state + 96),
                    (state + 64, state + 65),
                    (state + 65, state + 64),
                    (state + 64, state + 64),
                    (state, state + 8),
                    (end - 16, state + 64),
                    (state + 64, end - 16),
                    (module.image.memory_base + 8, state + 64),
                    (state + 64, module.image.memory_base + 8),
                    (u64::MAX, u64::MAX),
                ] {
                    cases.push(Case {
                        input: [count, source, destination, mode],
                        pc: module.program.entry(),
                        budget: 100,
                        patch: None,
                    });
                }
            }
        }
        for instruction in module.program.instructions() {
            for budget in [0, 1, 2, 8, 64] {
                cases.push(Case {
                    input: [2, state + 64, state + 65, 7],
                    pc: instruction.address(),
                    budget,
                    patch: None,
                });
            }
        }
        let mut rows = Vec::new();
        let mut memories = Vec::new();
        for case in &cases {
            rows.push(module_fixture::expected_with_state(&module, case, Some(&registers)).0);
            let (input, memory) =
                module_fixture::prepare_with_state(&module, case, Some(&registers));
            let report = module
                .program
                .run_from(
                    case.pc,
                    &input,
                    module.image.memory_base,
                    &memory,
                    Limits {
                        instructions: case.budget,
                        imports: 0,
                    },
                    &mut RejectImports,
                )
                .unwrap();
            memories.push(report.state.memory);
        }
        let directory = scratch.0.join(format!("df-{backwards}"));
        std::fs::create_dir(&directory).unwrap();
        compared += module_fixture::check_generated_with_memory(
            &module, &cases, &rows, &memories, &directory, &registers,
        );
    }
    println!("{compared} sanitized generated C comparisons, including every backing byte");
}
