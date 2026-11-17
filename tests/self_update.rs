use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, MemoryFault, Place, Program,
    Reg, RunStatus, Width,
};
use nirvana::self_update::extract;

const OPS: [BinaryOp; 5] = [
    BinaryOp::Add,
    BinaryOp::Mul,
    BinaryOp::And,
    BinaryOp::Or,
    BinaryOp::Xor,
];
fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn b(op: BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn load(address: Expr, width: Width) -> Expr {
    Expr::load(address, width)
}
fn same(a: Reg, b: Reg) -> bool {
    if matches!(a.0, 0 | 1) && matches!(b.0, 0 | 1) {
        true
    } else {
        a == b
    }
}
fn store(address: u64, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: c(address),
            width: Width::U8,
        },
        value,
    }
}
fn program(value: Expr) -> Program {
    Program::new(
        0,
        6,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                store(0x101f, c(0xa5)),
                Assignment {
                    destination: Reg(5).into(),
                    value: c(0xdead_beef_3579_2468),
                },
                Assignment {
                    destination: Reg(0).into(),
                    value,
                },
                store(0x101e, r(0)),
            ],
            control: Control::Return(r(0)),
        }],
    )
    .unwrap()
}

fn replay(value: &Expr, input: &[u64; 6], memory: &[u8]) {
    let before_tree = value.clone();
    let (op, rhs) = extract(value, Reg(0), same).expect("declared self-update case");
    assert_eq!(nodes(&rhs) + 2, nodes(value));
    let before = program(value.clone());
    let after = program(b(op, r(0), rhs));
    for limit in [0, 1, 2] {
        assert_eq!(
            after.run_with_memory(input, 0x1000, memory, limit).unwrap(),
            before
                .run_with_memory(input, 0x1000, memory, limit)
                .unwrap(),
            "op={op:?}, limit={limit}, input={input:?}"
        );
    }
    assert_eq!(value, &before_tree);
}

fn nodes(expr: &Expr) -> usize {
    let mut pending = vec![expr];
    let mut count = 0;
    while let Some(expr) = pending.pop() {
        count += 1;
        match expr {
            Expr::Binary(_, a, b) => {
                pending.push(a);
                pending.push(b);
            }
            Expr::Load { address, .. } => pending.push(address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push(condition);
                pending.push(taken);
                pending.push(not_taken);
            }
            _ => {}
        }
    }
    count
}

#[test]
fn every_associative_operator_preserves_unsigned_boundary_values_and_aliases() {
    let values = [0, 1, 255, 65535, u32::MAX as u64, 1 << 63, u64::MAX];
    for op in OPS {
        let value = b(op, b(op, r(1), r(2)), r(3));
        assert_eq!(extract(&value, Reg(0), same), Some((op, b(op, r(2), r(3)))));
        for initial in values {
            for first in values {
                for second in values {
                    replay(
                        &value,
                        &[initial, initial, first, second, 0, 0x99],
                        &[0x37; 32],
                    );
                }
            }
        }
    }
}

#[test]
fn preserves_all_additional_self_reads_and_opaque_arithmetic_subtrees() {
    let tail = b(
        BinaryOp::Mul,
        b(BinaryOp::And, r(2), c(255)),
        b(BinaryOp::Shl, r(3), c(64)),
    );
    let value = b(
        BinaryOp::Add,
        b(BinaryOp::Add, b(BinaryOp::Add, r(0), c(1)), r(0)),
        tail.clone(),
    );
    assert_eq!(
        extract(&value, Reg(0), same),
        Some((
            BinaryOp::Add,
            b(BinaryOp::Add, b(BinaryOp::Add, c(1), r(0)), tail)
        ))
    );
    for initial in [0, 1, u64::MAX] {
        for shift in [0, 63, 64, 65, u64::MAX] {
            let rhs = b(BinaryOp::Shl, b(BinaryOp::And, r(2), c(0xffff)), c(shift));
            let value = b(BinaryOp::Xor, b(BinaryOp::Xor, r(0), r(0)), rhs);
            replay(
                &value,
                &[initial, initial, u64::MAX, 17, 0, 0xbad],
                &[0x37; 32],
            );
        }
    }
}

#[test]
fn multiple_loads_keep_the_first_fault_and_prior_partial_state_even_after_zero() {
    let memory: Vec<_> = (0..32).map(|n| (n * 13 + 7) as u8).collect();
    for op in OPS {
        let first = load(r(2), Width::U8);
        let second = load(r(3), Width::U16);
        let value = b(op, b(op, r(0), first.clone()), second.clone());
        assert_eq!(
            extract(&value, Reg(0), same),
            Some((op, b(op, first, second)))
        );
        for initial in [0, u64::MAX] {
            for left in [0x1000, 0x101f, 0x1020, u64::MAX] {
                for right in [0x1000, 0x101e, 0x101f, u64::MAX] {
                    replay(&value, &[initial, initial, left, right, 0, 0x99], &memory);
                }
            }
        }
        let report = program(value)
            .run_with_memory(&[0, 0, u64::MAX, 0x1020, 0, 0], 0x1000, &memory, 1)
            .unwrap();
        assert_eq!(
            report.status,
            RunStatus::Fault(MemoryFault {
                access: AccessKind::Read,
                address: u64::MAX,
                width: Width::U8
            })
        );
        assert_eq!(report.state.memory[31], 0xa5);
        assert_eq!(
            report.state.memory[30], memory[30],
            "post-fault store must not execute"
        );
        assert_eq!(report.state.registers[5], 0xdead_beef_3579_2468);
    }
}

#[test]
fn nested_addresses_and_lazy_select_arms_retain_structure_and_execution() {
    let mut memory = vec![0x11; 32];
    memory[..8].copy_from_slice(&0x1010_u64.to_le_bytes());
    memory[8..16].copy_from_slice(&u64::MAX.to_le_bytes());
    memory[16] = 0x77;
    let first = load(load(r(2), Width::U64), Width::U8);
    let selected = Expr::select(r(4), load(r(3), Width::U8), load(c(u64::MAX), Width::U32));
    for op in OPS {
        let value = b(op, b(op, r(1), first.clone()), selected.clone());
        assert_eq!(
            extract(&value, Reg(0), same),
            Some((op, b(op, first.clone(), selected.clone())))
        );
        for initial in [0, 7, u64::MAX] {
            for pointer in [0x1000, 0x1008, 0x101f, u64::MAX] {
                for condition in [0, 1] {
                    replay(
                        &value,
                        &[initial, initial, pointer, 0x1010, condition, 0x999],
                        &memory,
                    );
                }
            }
        }
    }
}

#[test]
fn direct_update_keeps_rhs_verbatim_and_callback_can_exclude_parameters() {
    let rhs = Expr::select(r(4), load(r(2), Width::U64), b(BinaryOp::Sub, r(3), r(0)));
    for op in OPS {
        let value = b(op, r(0), rhs.clone());
        assert_eq!(extract(&value, Reg(0), same), Some((op, rhs.clone())));
        assert_eq!(extract(&value, Reg(0), |_, _| false), None);
    }
}

#[test]
fn rejects_right_only_self_mixed_spines_and_nonassociative_operations() {
    for op in [
        BinaryOp::Sub,
        BinaryOp::Shl,
        BinaryOp::Shr,
        BinaryOp::Eq,
        BinaryOp::Ne,
        BinaryOp::Ult,
        BinaryOp::Ule,
        BinaryOp::UMulHigh,
    ] {
        assert_eq!(extract(&b(op, r(0), c(1)), Reg(0), same), None);
    }
    for value in [
        r(0),
        b(BinaryOp::Add, r(2), r(0)),
        b(BinaryOp::Add, b(BinaryOp::Mul, r(0), c(3)), c(7)),
        b(BinaryOp::Mul, b(BinaryOp::Add, r(0), c(3)), c(7)),
        b(BinaryOp::Add, load(r(0), Width::U8), c(7)),
        b(BinaryOp::Add, load(c(0x1000), Width::U8), r(0)),
        b(BinaryOp::Add, c(1), b(BinaryOp::Add, r(0), c(2))),
        b(BinaryOp::Add, c(1), r(2)),
        b(BinaryOp::Add, Expr::select(c(1), r(0), r(0)), c(7)),
    ] {
        assert_eq!(extract(&value, Reg(0), same), None);
    }
}

#[test]
fn constant_prefix_exception_keeps_later_operands_ordered_for_every_operator() {
    let memory = [0x37; 32];
    for op in OPS {
        for constant in [0, 1, 255, u64::MAX] {
            let prefix = b(op, c(constant), r(1));
            assert_eq!(extract(&prefix, Reg(0), same), Some((op, c(constant))));
            assert_eq!(extract(&prefix, Reg(0), |_, _| false), None);
            let first = load(r(2), Width::U8);
            let second = Expr::select(r(4), load(r(3), Width::U16), c(0));
            let value = b(op, b(op, prefix, first.clone()), second.clone());
            assert_eq!(
                extract(&value, Reg(0), same),
                Some((op, b(op, b(op, c(constant), first), second)))
            );
            for initial in [0, 1, u64::MAX] {
                for left in [0x1000, u64::MAX] {
                    for right in [0x101e, 0x101f] {
                        for condition in [0, 1] {
                            replay(
                                &value,
                                &[initial, initial, left, right, condition, 0x999],
                                &memory,
                            );
                        }
                    }
                }
            }
        }
    }
    let sum = b(
        BinaryOp::Add,
        b(BinaryOp::Add, c(1), r(1)),
        b(BinaryOp::Mul, r(2), c(2)),
    );
    assert_eq!(
        extract(&sum, Reg(0), same),
        Some((
            BinaryOp::Add,
            b(BinaryOp::Add, c(1), b(BinaryOp::Mul, r(2), c(2)))
        ))
    );
    replay(&sum, &[u64::MAX, u64::MAX, 1 << 63, 17, 0, 0x999], &memory);
}

#[test]
fn resource_bounds_reject_the_entire_tree_before_the_callback() {
    let mut deep = r(0);
    for _ in 0..130 {
        deep = b(BinaryOp::Add, deep, c(1));
    }
    let mut broad = c(0);
    for _ in 0..14 {
        broad = b(BinaryOp::Xor, broad.clone(), broad);
    }
    for value in [deep, b(BinaryOp::Add, r(0), broad)] {
        assert_eq!(
            extract(&value, Reg(0), |_, _| panic!(
                "validate resources before callbacks"
            )),
            None
        );
    }
}
