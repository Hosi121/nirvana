use nirvana::indexed::{IndexedAddress, recover_indexed};
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Program, Reg, Width};

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}

fn c(value: u64) -> Expr {
    Expr::Const(value)
}

fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}

fn add(left: Expr, right: Expr) -> Expr {
    binary(BinaryOp::Add, left, right)
}

fn sub(left: Expr, right: Expr) -> Expr {
    binary(BinaryOp::Sub, left, right)
}

fn mul(index: Expr, stride: u64) -> Expr {
    binary(BinaryOp::Mul, index, c(stride))
}

fn origin(expression: &Expr) -> Option<(Reg, i64)> {
    match expression {
        Expr::Register(Reg(0)) => Some((Reg(0), 0)),
        Expr::Register(Reg(2)) => Some((Reg(0), -17)),
        _ => None,
    }
}

fn lowered(address: &IndexedAddress) -> Expr {
    add(
        add(r(address.register.0), c(address.offset as u64)),
        mul(address.index.clone(), address.stride),
    )
}

fn program(value: Expr) -> Program {
    Program::new(
        0,
        4,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(value),
        }],
    )
    .unwrap()
}

fn assert_equivalent(expression: Expr) -> IndexedAddress {
    let recovered = recover_indexed(&expression, origin).expect("known indexed shape");
    let original = program(expression);
    let lowered = program(lowered(&recovered));
    let boundaries = [0, 1, 2, 63, 64, 1 << 63, u64::MAX - 1, u64::MAX];
    for base in boundaries {
        for index in boundaries {
            for other in boundaries {
                let state = [base, index, base.wrapping_sub(17), other];
                assert_eq!(
                    original.execute(&state, 1).unwrap().value,
                    lowered.execute(&state, 1).unwrap().value,
                    "{recovered:?}, state={state:?}"
                );
            }
        }
    }
    recovered
}

#[test]
fn constant_offsets_multiply_orders_and_negative_indices_wrap() {
    let cases = [
        add(r(0), mul(r(1), 8)),
        add(mul(r(1), 8), r(0)),
        sub(add(r(2), mul(r(1), 8)), c(31)),
        add(c(u64::MAX), add(mul(r(1), 8), add(c(1 << 63), r(2)))),
        sub(add(r(0), c(7)), mul(r(1), 8)),
        sub(r(0), sub(c(9), binary(BinaryOp::Mul, c(3), r(1)))),
        add(r(0), binary(BinaryOp::Mul, c(u64::MAX), r(1))),
    ];
    for expression in cases {
        assert_equivalent(expression);
    }
    let result = assert_equivalent(sub(add(r(2), mul(r(1), 8)), c(31)));
    assert_eq!(result.offset, -48);
    let result = assert_equivalent(sub(r(0), mul(r(1), 8)));
    assert_eq!(result.stride, 0_u64.wrapping_sub(8));
}

#[test]
fn shift_counts_use_the_ir_mask_including_63_64_and_max() {
    for count in [0, 1, 3, 63, 64, 65, u64::MAX] {
        let result = assert_equivalent(add(r(0), binary(BinaryOp::Shl, r(1), c(count))));
        assert_eq!(result.stride, 1_u64 << (count & 63));
        assert_eq!(result.index, r(1));
    }
}

#[test]
fn pure_dynamic_index_syntax_stays_at_the_original_point() {
    let index = binary(BinaryOp::Xor, r(1), binary(BinaryOp::And, r(3), c(7)));
    let result = assert_equivalent(add(r(2), mul(index.clone(), 4)));
    assert_eq!(result.index, index);
    assert_eq!(result.offset, -17);
    let byte_index = assert_equivalent(add(r(0), binary(BinaryOp::And, r(1), c(31))));
    assert_eq!(byte_index.stride, 1);
    // Numerically equal base/index inputs do not imply disjoint allocations.
    let expression = add(r(0), mul(r(1), 8));
    let indexed = recover_indexed(&expression, origin).unwrap();
    let state = [u64::MAX, u64::MAX, u64::MAX - 17, 0];
    assert_eq!(
        program(expression).execute(&state, 1).unwrap().value,
        program(lowered(&indexed)).execute(&state, 1).unwrap().value
    );
    let execution = Program::new(
        0,
        4,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![Assignment {
                destination: Reg(1).into(),
                value: c(9),
            }],
            control: Control::Return(lowered(&indexed)),
        }],
    )
    .unwrap()
    .execute(&[100, 1, 83, 0], 1)
    .unwrap();
    assert_eq!(
        execution.value, 172,
        "index was not captured before assignment"
    );
}

#[test]
fn an_affine_subtree_resolves_as_one_base_atom() {
    let base = add(r(2), c(5));
    let expression = add(base.clone(), mul(r(1), 8));
    let result = recover_indexed(&expression, |expr| {
        if expr == &base {
            Some((Reg(0), -12))
        } else {
            origin(expr)
        }
    })
    .unwrap();
    assert_eq!(result.offset, -12);
    let state = [100, 3, 83, 0];
    assert_eq!(
        program(expression).execute(&state, 1).unwrap().value,
        program(lowered(&result)).execute(&state, 1).unwrap().value
    );
}

#[test]
fn multiple_syntactic_bases_are_ambiguous_even_when_they_alias() {
    for expression in [
        add(r(0), r(2)),
        add(add(r(0), r(2)), mul(r(1), 8)),
        add(r(0), mul(r(2), 1)),
        add(r(0), binary(BinaryOp::Shl, r(2), c(64))),
        add(r(0), sub(c(0), mul(r(2), u64::MAX))),
    ] {
        assert_eq!(recover_indexed(&expression, origin), None);
        assert_eq!(
            recover_indexed(&expression, |expr| match expr {
                Expr::Register(Reg(0) | Reg(2)) => Some((Reg(0), 0)),
                _ => None,
            }),
            None
        );
    }
}

#[test]
fn scaled_input_origins_are_current_indices_even_when_they_alias_the_base() {
    for expression in [
        add(r(0), mul(r(2), 8)),
        add(r(0), mul(binary(BinaryOp::And, r(2), c(3)), 8)),
        add(r(0), mul(r(0), 8)),
        add(r(0), binary(BinaryOp::Xor, r(2), c(7))),
        add(mul(r(1), 8), mul(r(2), 1)),
    ] {
        assert_equivalent(expression);
    }
    let expression = add(r(0), mul(r(1), 8));
    let result = recover_indexed(&expression, |expr| match expr {
        Expr::Register(reg @ Reg(0..=3)) => Some((*reg, 0)),
        _ => None,
    })
    .unwrap();
    assert_eq!(result.register, Reg(0));
    assert_eq!(result.index, r(1));
    assert_eq!(result.stride, 8);
}

#[test]
fn loads_and_selects_are_rejected_even_if_a_callback_claims_a_base() {
    let load = Expr::load(r(0), Width::U64);
    let select = Expr::select(r(3), r(1), r(1));
    for expression in [
        add(load.clone(), mul(r(1), 8)),
        add(r(0), mul(load.clone(), 8)),
        add(r(0), mul(binary(BinaryOp::Mul, load, c(0)), 8)),
        add(r(0), mul(select, 8)),
        Expr::select(c(1), add(r(0), mul(r(1), 8)), c(0)),
        Expr::select(Expr::load(c(u64::MAX), Width::U8), r(0), r(0)),
    ] {
        let callback = |_: &Expr| -> Option<(Reg, i64)> {
            panic!("reject impure syntax before calling origin")
        };
        assert_eq!(recover_indexed(&expression, callback), None);
    }
}

#[test]
fn absent_base_zero_scale_negative_base_and_multiple_indices_stay_raw() {
    for expression in [
        add(r(1), mul(r(3), 8)),
        add(r(0), mul(r(1), 0)),
        add(r(0), mul(c(3), 8)),
        add(sub(c(0), r(0)), mul(r(1), 8)),
        add(add(r(0), mul(r(1), 8)), mul(r(3), 4)),
        add(r(0), binary(BinaryOp::Mul, r(1), r(3))),
        add(r(0), binary(BinaryOp::Shl, r(1), r(3))),
        add(r(0), c(8)),
    ] {
        assert_eq!(recover_indexed(&expression, origin), None);
    }
}

#[test]
fn depth_and_node_budgets_reject_before_origin_queries() {
    let mut deep = r(0);
    for _ in 0..130 {
        deep = add(deep, c(1));
    }
    let mut broad = r(1);
    for _ in 0..12 {
        broad = binary(BinaryOp::Xor, broad.clone(), broad);
    }
    for expression in [add(deep, mul(r(1), 8)), add(r(0), broad)] {
        assert_eq!(
            recover_indexed(&expression, |_| panic!("resource limit checked first")),
            None
        );
    }
}
