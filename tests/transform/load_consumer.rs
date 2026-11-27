//! The private temporary may change; load order and all other state remain.
use crate::support::ir::{c, r};
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use nirvana::transform::load_consumer::{self, Error};

fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn store(address: Expr, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address,
            width: Width::U8,
        },
        value,
    }
}
fn program(rows: Vec<(Vec<Assignment>, Control)>) -> Program {
    Program::new(
        0,
        8,
        rows.into_iter()
            .enumerate()
            .map(|(n, (assignments, control))| IrInstruction {
                address: n as u64,
                size: 1,
                assignments,
                control,
            })
            .collect(),
    )
    .unwrap()
}
fn changed(source: &Program, f: impl FnOnce(&mut [IrInstruction])) -> Program {
    let mut instructions = source.instructions().to_vec();
    f(&mut instructions);
    Program::new(0, 8, instructions).unwrap()
}
fn compare(source: &Program, candidate: &Program, private: &[Reg]) {
    for seed in [0, 1, 255, 1 << 63, u64::MAX] {
        for pointer in [4095, 4096, 4104, 4127, u64::MAX] {
            for other in [4097, 4112, u64::MAX] {
                let mut input = [seed; 8];
                input[0] = pointer;
                input[7] = other;
                let memory: Vec<_> = (0..32usize)
                    .map(|n| n.wrapping_mul(29).wrapping_add(seed as usize) as u8)
                    .collect();
                for budget in 0..8 {
                    let mut a = source
                        .run_with_memory(&input, 4096, &memory, budget)
                        .unwrap();
                    let mut z = candidate
                        .run_with_memory(&input, 4096, &memory, budget)
                        .unwrap();
                    for reg in private {
                        a.state.registers[reg.0] = 0;
                        z.state.registers[reg.0] = 0;
                    }
                    assert_eq!(a, z, "{seed}/{pointer}/{other}/{budget}");
                }
            }
        }
    }
}
fn basic(value: Expr) -> Program {
    program(vec![
        (
            vec![store(c(4096), c(91)), set(1, Expr::load(r(0), Width::U64))],
            Control::Next,
        ),
        (
            vec![set(3, Expr::load(r(7), Width::U8)), store(c(4104), c(173))],
            Control::Next,
        ),
        (vec![set(2, value)], Control::Return(b(B::Xor, r(2), r(3)))),
    ])
}

#[test]
fn strict_word_contexts_preserve_aliases_intermediate_faults_and_nonprivate_prefixes() {
    let mut contexts = vec![b(B::Add, b(B::And, r(1), c(3)), c(1))];
    for op in [
        B::Add,
        B::Sub,
        B::Mul,
        B::And,
        B::Or,
        B::Xor,
        B::Shl,
        B::Shr,
        B::AShr,
        B::UMulHigh,
        B::SMulHigh,
        B::UDiv,
        B::URem,
        B::SDiv,
        B::SRem,
    ] {
        for constant in [0, 1, 64, 1 << 63, u64::MAX] {
            contexts.push(b(op, r(1), c(constant)));
        }
    }
    for context in contexts {
        let source = basic(context.clone());
        let lowering = load_consumer::lower(&source, &[Reg(0), Reg(7)]).unwrap();
        lowering.validate().unwrap();
        assert_eq!(lowering.source().instructions(), source.instructions());
        let candidate = lowering.program();
        let evidence = lowering.evidence();
        assert_eq!(evidence.folds.len(), 1);
        assert_eq!(evidence.folds[0].expression, context);
        assert_eq!(candidate.instructions()[2].assignments[0].value, r(1));
        compare(&source, candidate, &[Reg(1)]);
    }
}

#[test]
fn a_lazy_consumer_cannot_make_an_original_load_conditional() {
    let source = basic(Expr::select(c(0), r(1), c(17)));
    assert!(load_consumer::propose(&source, &[]).is_none());
    let wrong = changed(&source, |rows| {
        let load = rows[0].assignments[1].value.clone();
        rows[0].assignments[1].value = Expr::select(c(0), load, c(17));
        rows[2].assignments[0].value = r(1);
    });
    assert_eq!(
        load_consumer::validate(&source, &wrong, &[]),
        Err(Error::UnsupportedChange)
    );
}

#[test]
fn another_register_in_the_consumer_cannot_be_read_at_the_earlier_load() {
    let source = program(vec![
        (
            vec![set(4, c(1)), set(1, Expr::load(r(0), Width::U64))],
            Control::Next,
        ),
        (vec![set(4, c(19))], Control::Next),
        (vec![set(2, b(B::Add, r(1), r(4)))], Control::Return(r(2))),
    ]);
    assert!(load_consumer::propose(&source, &[]).is_none());
    let wrong = changed(&source, |rows| {
        let load = rows[0].assignments[1].value.clone();
        rows[0].assignments[1].value = b(B::Add, load, r(4));
        rows[2].assignments[0].value = r(1);
    });
    assert!(load_consumer::validate(&source, &wrong, &[]).is_err());
}

#[test]
fn copied_load_trees_keep_nested_address_loads_and_lazy_address_arms() {
    let address = Expr::select(r(5), r(0), Expr::load(r(7), Width::U64));
    let source = program(vec![
        (vec![set(1, Expr::load(address, Width::U8))], Control::Next),
        (vec![set(2, b(B::Add, r(1), c(1)))], Control::Return(r(2))),
    ]);
    let candidate = load_consumer::propose(&source, &[]).unwrap();
    load_consumer::validate(&source, &candidate, &[]).unwrap();
    compare(&source, &candidate, &[Reg(1)]);
    for mutation in [0, 1, 2] {
        let wrong = changed(&candidate, |rows| {
            let Expr::Binary(_, load, _) = &mut rows[0].assignments[0].value else {
                panic!()
            };
            let Expr::Load { address, width } = &mut **load else {
                panic!()
            };
            match mutation {
                0 => *width = Width::U64,
                1 => **address = r(0),
                _ => **load = c(0),
            }
        });
        assert!(load_consumer::validate(&source, &wrong, &[]).is_err());
    }
}

#[test]
fn parameters_multiple_uses_and_cross_block_consumers_remain_unfolded() {
    let source = basic(b(B::Add, r(1), c(1)));
    let candidate = load_consumer::propose(&source, &[]).unwrap();
    assert!(load_consumer::propose(&source, &[Reg(1)]).is_none());
    assert!(load_consumer::validate(&source, &candidate, &[Reg(1)]).is_err());
    for extra in [r(1), Expr::load(r(1), Width::U8)] {
        let extra = changed(&source, |rows| rows[1].assignments.push(set(6, extra)));
        assert!(load_consumer::propose(&extra, &[]).is_none());
        let wrong = changed(&candidate, |rows| {
            rows[1]
                .assignments
                .push(extra.instructions()[1].assignments[2].clone())
        });
        assert!(load_consumer::validate(&extra, &wrong, &[]).is_err());
    }
    let split = changed(&source, |rows| rows[0].control = Control::Jump(1));
    assert!(load_consumer::propose(&split, &[]).is_none());
}

#[test]
fn composed_depth_and_fold_count_are_bounded_before_adoption() {
    let mut address = r(0);
    for _ in 0..32 {
        address = b(B::Add, address, c(0));
    }
    let load = Expr::load(address, Width::U8);
    let mut context = r(1);
    for _ in 0..100 {
        context = Expr::unary(
            nirvana::ir::UnaryOp::Extract {
                start: 0,
                width: Width::U64,
            },
            context,
        );
    }
    let source = program(vec![(
        vec![set(1, load.clone()), set(2, context.clone())],
        Control::Return(r(2)),
    )]);
    assert!(load_consumer::propose(&source, &[]).is_none());
    let mut producer = load;
    for _ in 0..100 {
        producer = Expr::unary(
            nirvana::ir::UnaryOp::Extract {
                start: 0,
                width: Width::U64,
            },
            producer,
        );
    }
    let wrong = changed(&source, |rows| {
        rows[0].assignments[0].value = producer;
        rows[0].assignments[1].value = r(1);
    });
    assert_eq!(
        load_consumer::validate(&source, &wrong, &[]),
        Err(Error::ResourceLimit)
    );
    let mut assignments = Vec::new();
    for n in 0..=load_consumer::MAX_FOLDS {
        let temp = 2 * n + 1;
        assignments.extend([
            set(temp, Expr::load(r(0), Width::U64)),
            set(temp + 1, b(B::Add, r(temp), c(1))),
        ]);
    }
    let source = Program::new(
        0,
        2 * (load_consumer::MAX_FOLDS + 1) + 1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control: Control::Return(c(0)),
        }],
    )
    .unwrap();
    assert!(load_consumer::propose(&source, &[]).is_none());
}
