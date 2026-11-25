use super::*;
use crate::model::ir::{Assignment, BinaryOp as B, IrInstruction, Reg, UnaryOp as U};

fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn r(register: usize) -> Expr {
    Expr::Register(Reg(register))
}
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn straight(registers: usize, assignments: Vec<Assignment>, result: Expr) -> Program {
    Program::new(
        0,
        registers,
        vec![ins(0, assignments, Control::Return(result))],
    )
    .unwrap()
}
fn facts(source: &Program) -> (SsaFunction, Vec<Claim>) {
    let graph = SsaFunction::build(source).unwrap();
    let claims = vec![Claim::Fits(Width::U64); graph.values.len()];
    (graph, claims)
}
fn assign(graph: &SsaFunction, claims: &mut [Claim], pc: u64, index: usize, value: Claim) {
    let id = graph
        .values
        .iter()
        .position(|d| {
            matches!(d, Definition::Assignment { site, .. }
        if site.instruction == pc && site.assignment == Some(index))
        })
        .unwrap();
    claims[id] = value;
}
fn checked(
    source: &Program,
    graph: &SsaFunction,
    claims: &[Claim],
    widths: &[Width],
) -> ValidationEvidence {
    validate(source, graph, claims, widths).unwrap()
}

#[test]
fn sign_extended_values_shifts_and_signed_division_are_checked_without_producer_transfer() {
    let p = straight(
        5,
        vec![
            set(1, Expr::unary(U::SignExtend(Width::U8), r(0))),
            set(2, b(B::AShr, r(1), r(3))),
            set(4, b(B::SDiv, r(2), c((-31i64) as u64))),
        ],
        r(4),
    );
    let (graph, mut claims) = facts(&p);
    for index in 0..3 {
        assign(&graph, &mut claims, 0, index, Claim::Fits(Width::U8));
    }
    let widths = [Width::U64, Width::U8, Width::U8, Width::U64, Width::U8];
    let evidence = checked(&p, &graph, &claims, &widths);
    assert_eq!(evidence.assignments, 3);
    assert_eq!(evidence.reads, 5);
    assert_eq!(evidence.narrow_registers, 3);
    assign(&graph, &mut claims, 0, 2, Claim::Constant(0));
    assert_eq!(
        validate(&p, &graph, &claims, &widths),
        Err(Invalid("assignment sign bound"))
    );
}

#[test]
fn wrong_constants_positive_unsigned_values_and_wide_writes_cannot_use_small_signed_storage() {
    for value in [128, 255, 65535, (-129i64) as u64, 1 << 63] {
        let p = straight(1, vec![set(0, c(value))], r(0));
        let (graph, mut claims) = facts(&p);
        assign(&graph, &mut claims, 0, 0, Claim::Constant(value));
        assert!(validate(&p, &graph, &claims, &[Width::U8]).is_err());
        checked(&p, &graph, &claims, &[Width::U64]);
        assign(&graph, &mut claims, 0, 0, Claim::Constant(value ^ 1));
        assert_eq!(
            validate(&p, &graph, &claims, &[Width::U64]),
            Err(Invalid("assignment sign bound"))
        );
    }
    let p = straight(1, vec![set(0, c(128)), set(0, c(1))], r(0));
    let (graph, mut claims) = facts(&p);
    assign(&graph, &mut claims, 0, 0, Claim::Constant(128));
    assign(&graph, &mut claims, 0, 1, Claim::Constant(1));
    assert_eq!(
        validate(&p, &graph, &claims, &[Width::U8]),
        Err(Invalid("storage write sign bound"))
    );
    checked(&p, &graph, &claims, &[Width::U16]);
}

#[test]
fn unsigned_loads_need_the_next_signed_width_and_source_reads_keep_initial_values() {
    for (load, required, wrong) in [
        (Width::U8, Width::U16, Width::U8),
        (Width::U16, Width::U32, Width::U16),
    ] {
        let p = straight(1, vec![set(0, Expr::load(c(100), load))], r(0));
        let (graph, mut claims) = facts(&p);
        assign(&graph, &mut claims, 0, 0, Claim::Fits(required));
        checked(&p, &graph, &claims, &[required]);
        assign(&graph, &mut claims, 0, 0, Claim::Fits(wrong));
        assert_eq!(
            validate(&p, &graph, &claims, &[Width::U64]),
            Err(Invalid("assignment sign bound"))
        );
    }
    let p = straight(
        3,
        vec![
            set(1, r(0)),
            set(0, Expr::unary(U::SignExtend(Width::U8), r(2))),
        ],
        r(0),
    );
    let (graph, mut claims) = facts(&p);
    assign(&graph, &mut claims, 0, 1, Claim::Fits(Width::U8));
    checked(&p, &graph, &claims, &[Width::U64; 3]);
    assert_eq!(
        validate(&p, &graph, &claims, &[Width::U8, Width::U64, Width::U64]),
        Err(Invalid("storage read sign bound"))
    );
}

#[test]
fn both_select_arms_and_memory_addresses_are_original_storage_observations() {
    let p = straight(3, vec![set(0, Expr::select(c(1), c(7), r(1)))], r(0));
    let (graph, mut claims) = facts(&p);
    assign(&graph, &mut claims, 0, 0, Claim::Constant(7));
    checked(&p, &graph, &claims, &[Width::U8, Width::U64, Width::U64]);
    assert_eq!(
        validate(&p, &graph, &claims, &[Width::U8, Width::U8, Width::U64]),
        Err(Invalid("storage read sign bound"))
    );
    let p = straight(
        2,
        vec![Assignment {
            destination: Place::Memory {
                address: r(0),
                width: Width::U8,
            },
            value: b(B::And, Expr::load(r(1), Width::U8), c(0)),
        }],
        c(0),
    );
    let (graph, claims) = facts(&p);
    let evidence = checked(&p, &graph, &claims, &[Width::U64; 2]);
    assert_eq!(evidence.reads, 2);
    for index in [0, 1] {
        let mut widths = [Width::U64; 2];
        widths[index] = Width::U8;
        assert_eq!(
            validate(&p, &graph, &claims, &widths),
            Err(Invalid("storage read sign bound"))
        );
    }
}

#[test]
fn all_phi_alternatives_virtual_entry_and_mutated_ssa_remain_load_bearing() {
    let p = Program::new(
        0,
        2,
        vec![
            ins(0, vec![set(1, c((-2i64) as u64))], Control::Jump(1)),
            ins(
                1,
                vec![set(1, b(B::AShr, r(1), c(1)))],
                Control::Branch {
                    condition: r(0),
                    target: 1,
                },
            ),
            ins(2, vec![], Control::Return(r(1))),
        ],
    )
    .unwrap();
    let (graph, mut claims) = facts(&p);
    assign(&graph, &mut claims, 0, 0, Claim::Constant((-2i64) as u64));
    assign(&graph, &mut claims, 1, 0, Claim::Fits(Width::U8));
    for (index, d) in graph.values.iter().enumerate() {
        if matches!(
            d,
            Definition::Phi {
                register: Reg(1),
                ..
            }
        ) {
            claims[index] = Claim::Fits(Width::U8);
        }
    }
    let widths = [Width::U64, Width::U8];
    assert!(checked(&p, &graph, &claims, &widths).phi_inputs >= 2);
    let mut broken = graph.clone();
    let Definition::Phi { inputs, .. } = broken
        .values
        .iter_mut()
        .find(|d| {
            matches!(
                d,
                Definition::Phi {
                    register: Reg(1),
                    ..
                }
            )
        })
        .unwrap()
    else {
        unreachable!()
    };
    inputs.pop();
    assert!(matches!(
        validate(&p, &broken, &claims, &widths),
        Err(Invalid(_))
    ));
    let p = Program::new(
        0,
        1,
        vec![
            ins(
                0,
                vec![set(0, b(B::AShr, r(0), c(1)))],
                Control::Branch {
                    condition: r(0),
                    target: 0,
                },
            ),
            ins(1, vec![], Control::Return(r(0))),
        ],
    )
    .unwrap();
    let (graph, mut claims) = facts(&p);
    for (index, d) in graph.values.iter().enumerate() {
        if matches!(d, Definition::Phi { .. }) {
            claims[index] = Claim::Fits(Width::U8);
        }
    }
    assert_eq!(
        validate(&p, &graph, &claims, &[Width::U64]),
        Err(Invalid("phi alternative sign bound"))
    );
    for (index, definition) in graph.values.iter().enumerate() {
        if matches!(definition, Definition::Phi { .. }) {
            claims[index] = Claim::Fits(Width::U64);
        }
    }
    let initial = graph
        .values
        .iter()
        .position(|d| matches!(d, Definition::Initial { .. }))
        .unwrap();
    claims[initial] = Claim::Constant(0);
    assert_eq!(
        validate(&p, &graph, &claims, &[Width::U64]),
        Err(Invalid("arbitrary initial boundary"))
    );
}

#[test]
fn source_mismatches_dimensions_unused_storage_and_work_limits_are_explicit() {
    let p = straight(2, vec![set(0, c(3))], r(0));
    let (graph, mut claims) = facts(&p);
    assign(&graph, &mut claims, 0, 0, Claim::Constant(3));
    checked(&p, &graph, &claims, &[Width::U8, Width::U64]);
    assert_eq!(
        validate(&p, &graph, &claims, &[Width::U8, Width::U8]),
        Err(Invalid("unobserved storage width"))
    );
    assert_eq!(
        validate(&p, &graph, &claims[..claims.len() - 1], &[Width::U64; 2]),
        Err(Invalid("candidate dimensions"))
    );
    assert_eq!(
        validate_bounded(&p, &graph, &claims, &[Width::U64; 2], 0),
        Err(Unavailable("work limit"))
    );
    let other = straight(2, vec![set(0, c(4))], r(0));
    assert_eq!(
        validate(&other, &graph, &claims, &[Width::U64; 2]),
        Err(Invalid("assignment sign bound"))
    );
    let mut wrong = graph.clone();
    wrong.blocks[0].points.last_mut().unwrap().reads[0].register = Reg(1);
    assert!(matches!(
        validate(&p, &wrong, &claims, &[Width::U64; 2]),
        Err(Invalid(_))
    ));
}
