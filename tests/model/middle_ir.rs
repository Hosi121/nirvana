//! Compare the direct MIR interpreter and reconstructed Low IR, including
//! complete prefixes at every selected budget and first-fault boundaries.
use crate::support::ir::{c, r};
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, UnaryOp as U,
    Width,
};
use nirvana::middle_ir::{Function, Operation, Statement, Terminator};

fn b(op: B, a: Expr, b: Expr) -> Expr {
    Expr::binary(op, a, b)
}

fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn one(assignments: Vec<Assignment>, control: Control) -> Program {
    Program::new(
        0,
        8,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control,
        }],
    )
    .unwrap()
}
fn compare(source: &Program, inputs: &[Vec<u64>], memory: &[u8], limits: &[usize]) -> usize {
    let middle = Function::from_low(source).unwrap();
    let restored = middle.lower().unwrap();
    assert_eq!(restored.instructions(), source.instructions());
    let mut checked = 0;
    for input in inputs {
        for &limit in limits {
            let expected = source.run_with_memory(input, 4096, memory, limit).unwrap();
            assert_eq!(
                middle.run_with_memory(input, 4096, memory, limit).unwrap(),
                expected,
                "MIR input={input:?}, budget={limit}"
            );
            assert_eq!(
                restored
                    .run_with_memory(input, 4096, memory, limit)
                    .unwrap(),
                expected
            );
            checked += 1;
        }
    }
    checked
}

#[test]
fn value_ids_versions_and_lazy_memory_regions_are_explicit() {
    let source = one(
        vec![set(
            0,
            Expr::select(
                r(1),
                Expr::load(r(7), Width::U16),
                Expr::load(c(u64::MAX), Width::U64),
            ),
        )],
        Control::Return(r(0)),
    );
    let middle = Function::from_low(&source).unwrap();
    let Statement::WriteStorage { value, version, .. } = &middle.blocks()[0].steps[0].statements[0]
    else {
        panic!()
    };
    assert!(version.is_some());
    let Operation::Select {
        taken, not_taken, ..
    } = &value.bindings.last().unwrap().operation
    else {
        panic!()
    };
    assert!(taken.bindings.iter().any(|v| matches!(
        v.operation,
        Operation::Load {
            width: Width::U16,
            ..
        }
    )));
    assert!(not_taken.bindings.iter().any(|v| matches!(
        v.operation,
        Operation::Load {
            width: Width::U64,
            ..
        }
    )));
    let input = vec![7, 1, 2, 3, 4, 5, 6, 4096];
    compare(&source, &[input], &[13; 32], &[0, 1, 2]);
}

#[test]
fn stores_preserve_address_checks_lazy_reads_and_partial_instruction_state() {
    let expressions = [
        Expr::load(c(4096), Width::U64),
        Expr::select(
            r(1),
            Expr::load(c(4096), Width::U8),
            Expr::load(c(u64::MAX), Width::U16),
        ),
        b(
            B::Add,
            Expr::load(c(4097), Width::U16),
            Expr::load(c(4190), Width::U64),
        ),
    ];
    let mut observations = 0;
    for address in [c(4096), c(4127), c(u64::MAX), Expr::load(r(7), Width::U64)] {
        for value in &expressions {
            for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
                let source = one(
                    vec![
                        set(0, c(123)),
                        store(c(4104), Width::U8, c(77)),
                        store(address.clone(), width, value.clone()),
                        set(0, c(999)),
                    ],
                    Control::Return(r(0)),
                );
                let inputs = [0, 1]
                    .into_iter()
                    .flat_map(|flag| {
                        [4096, 4127, u64::MAX].map(|pointer| vec![0, flag, 0, 0, 0, 0, 0, pointer])
                    })
                    .collect::<Vec<_>>();
                observations += compare(&source, &inputs, &[0; 32], &[0, 1, 2]);
            }
        }
    }
    assert_eq!(observations, 864);
}

#[test]
fn phi_backedges_unreachable_code_and_budgeted_loops_keep_complete_state() {
    let source = Program::new(
        0,
        8,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![set(2, c(0))],
                control: Control::Branch {
                    condition: r(1),
                    target: 3,
                },
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![set(0, b(B::Add, r(0), c(1))), store(r(7), Width::U64, r(0))],
                control: Control::Next,
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![set(2, b(B::Add, r(2), c(1)))],
                control: Control::Branch {
                    condition: b(B::Ult, r(2), c(4)),
                    target: 1,
                },
            },
            IrInstruction {
                address: 3,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::load(r(7), Width::U64)),
            },
            IrInstruction {
                address: 9,
                size: 1,
                assignments: vec![set(4, r(0))],
                control: Control::Return(Expr::load(c(u64::MAX), Width::U8)),
            },
        ],
    )
    .unwrap();
    let middle = Function::from_low(&source).unwrap();
    assert!(
        middle
            .ssa()
            .values
            .iter()
            .any(|v| matches!(v, nirvana::ssa::Definition::Phi { .. }))
    );
    assert_eq!(middle.blocks().last().unwrap().address, 9);
    let Statement::WriteStorage { version, value, .. } =
        &middle.blocks().last().unwrap().steps[0].statements[0]
    else {
        panic!()
    };
    assert!(version.is_none());
    assert!(matches!(
        value.bindings[0].operation,
        Operation::ReadStorage { version: None, .. }
    ));
    let inputs = [0, 1, u64::MAX]
        .into_iter()
        .flat_map(|n| {
            [0, 1].into_iter().flat_map(move |flag| {
                [4096, 4127].map(|pointer| vec![n, flag, 0, 0, 0, 0, 0, pointer])
            })
        })
        .collect::<Vec<_>>();
    assert_eq!(
        compare(&source, &inputs, &[0; 32], &(0..=16).collect::<Vec<_>>()),
        204
    );
}

#[test]
fn all_scalar_forms_round_trip_with_widths_and_total_arithmetic() {
    let ops = [
        B::Add,
        B::Sub,
        B::Mul,
        B::And,
        B::Or,
        B::Xor,
        B::Shl,
        B::Shr,
        B::Eq,
        B::Ne,
        B::Ult,
        B::Ule,
        B::UMulHigh,
        B::SMulHigh,
        B::AShr,
        B::UDiv,
        B::URem,
        B::SDiv,
        B::SRem,
        B::Insert {
            start: 61,
            width: Width::U16,
        },
    ];
    let unary = [
        U::SignExtend(Width::U8),
        U::SignExtend(Width::U32),
        U::Extract {
            start: 8,
            width: Width::U16,
        },
        U::Extract {
            start: 255,
            width: Width::U64,
        },
    ];
    let inputs = [0, 1, 63, 64, 1 << 63, u64::MAX]
        .into_iter()
        .flat_map(|a| [0, 1, 65, u64::MAX].map(|b| vec![a, b, 0, 0, 0, 0, 0, 4096]))
        .collect::<Vec<_>>();
    for op in ops {
        for u in unary {
            let source = one(
                vec![set(2, b(op, r(0), r(1)))],
                Control::Return(Expr::unary(u, r(2))),
            );
            compare(&source, &inputs, &[0; 32], &[0, 1, 2]);
        }
    }
}

#[test]
fn zero_storage_functions_and_invalid_invocations_are_preserved() {
    let source = Program::new(
        0,
        0,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(c(42)),
        }],
    )
    .unwrap();
    let middle = Function::from_low(&source).unwrap();
    assert!(matches!(
        middle.blocks()[0].terminator,
        Terminator::Return(_)
    ));
    compare(&source, &[vec![]], &[], &[0, 1, 2]);
    assert_eq!(
        middle.run_with_memory(&[7], 4096, &[], 2),
        source.run_with_memory(&[7], 4096, &[], 2)
    );
}

#[test]
fn real_gcc_functions_keep_full_state_across_middle_ir_and_back() {
    use crate::support::native;
    let scratch = native::Scratch::new();
    let mut observations = 0;
    for name in ["shared-tail", "multi-exit-prefix"] {
        for opt in ["-O0", "-O2", "-O3"] {
            let object = scratch.0.join(format!("{name}-{opt}.o"));
            native::object(
                &native::fixture_root().join(format!("cases/{name}.c")),
                &object,
                opt,
                "fixture",
            );
            let source =
                nirvana::frontend::lift_elf_auto(&std::fs::read(object).unwrap(), "fixture")
                    .unwrap()
                    .program;
            let mut inputs = Vec::new();
            let mut memory: Vec<_> = (0..65536).map(|n| (n as u8).wrapping_mul(29)).collect();
            for n in 0..4 {
                memory[4096 + n * 8..4104 + n * 8].copy_from_slice(&(n as u64).to_le_bytes());
            }
            for value in [0, 1, 3, u64::MAX] {
                for pointer in [8192, 67568, u64::MAX] {
                    let mut regs = vec![value; source.register_count()];
                    regs[nirvana::x86::RSP] = 67584;
                    regs[nirvana::x86::RDI] = pointer;
                    inputs.push(regs);
                }
            }
            observations += compare(&source, &inputs, &memory, &[0, 1, 2, 5, 20, 200]);
        }
    }
    assert_eq!(observations, 432);
    println!("{observations} actual GCC full-state MIR/lowered prefix observations");
}

#[test]
fn nested_lazy_regions_keep_condition_faults_and_chosen_arm_order() {
    let value = Expr::select(
        Expr::load(r(7), Width::U8),
        b(
            B::Add,
            Expr::load(c(4104), Width::U64),
            Expr::load(c(4112), Width::U64),
        ),
        Expr::select(
            r(1),
            Expr::load(c(4120), Width::U64),
            Expr::load(c(u64::MAX), Width::U8),
        ),
    );
    let source = one(
        vec![set(0, value.clone()), store(r(6), Width::U8, value)],
        Control::Return(r(0)),
    );
    let inputs: Vec<_> = [0, 1]
        .into_iter()
        .flat_map(|flag| {
            [4096, u64::MAX].into_iter().flat_map(move |pointer| {
                [4096, u64::MAX].map(|destination| vec![0, flag, 0, 0, 0, 0, destination, pointer])
            })
        })
        .collect();
    for byte in [0, 1] {
        compare(&source, &inputs, &[byte; 32], &[0, 1, 2]);
    }
}
