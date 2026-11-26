use super::*;
use crate::model::ir::{Assignment, UnaryOp};

fn returning(entry: u64, count: usize, value: Expr) -> Program {
    Program::new(
        entry,
        count,
        vec![IrInstruction {
            address: entry,
            size: 1,
            assignments: vec![],
            control: Control::Return(value),
        }],
    )
    .unwrap()
}
fn model(query: &Query) -> BTreeMap<String, u64> {
    query.names.iter().map(|name| (name.clone(), 0)).collect()
}

#[test]
fn cycles_open_edges_and_foreign_register_mappings_are_rejected_before_solving() {
    let cyclic = Program::new(
        0,
        1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Jump(0),
        }],
    )
    .unwrap();
    assert!(matches!(
        query(&cyclic, &cyclic, &[Reg(0)], &[]),
        Err(Error::Cycle)
    ));
    let open = Program::new(
        0,
        1,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Const(0)),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![],
                control: Control::Jump(99),
            },
        ],
    )
    .unwrap();
    assert!(matches!(
        query(&open, &open, &[Reg(0)], &[]),
        Err(Error::OpenEdge)
    ));
    let good = returning(0, 1, Expr::Const(0));
    for (shared, outputs) in [(vec![Reg(1)], vec![]), (vec![], vec![Reg(1)])] {
        assert!(matches!(
            query(&good, &good, &shared, &outputs),
            Err(Error::BoundaryMapping)
        ));
    }
}

#[test]
fn full_source_depth_and_size_are_checked_including_unreachable_expressions() {
    let too_many = returning(0, MAX_REGISTERS + 1, Expr::Const(0));
    assert!(matches!(
        query(&too_many, &too_many, &[], &[]),
        Err(Error::Limit)
    ));
    let mut deep = Expr::Const(0);
    for _ in 0..MAX_DEPTH + 2 {
        deep = Expr::unary(UnaryOp::SignExtend(Width::U8), deep);
    }
    let source = Program::new(
        0,
        1,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Const(0)),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![],
                control: Control::Return(deep),
            },
        ],
    )
    .unwrap();
    assert!(matches!(
        query(&source, &source, &[], &[]),
        Err(Error::Limit)
    ));
    let source = Program::new(
        0,
        1,
        (0..=MAX_INSTRUCTIONS)
            .map(|pc| IrInstruction {
                address: pc as u64,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Const(0)),
            })
            .collect(),
    )
    .unwrap();
    assert!(matches!(
        query(&source, &source, &[], &[]),
        Err(Error::Limit)
    ));
}

#[test]
fn entry_scope_allows_unreachable_cycles_and_distinct_source_addresses() {
    let source = Program::new(
        0,
        1,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Register(Reg(0))),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![],
                control: Control::Jump(1),
            },
        ],
    )
    .unwrap();
    let other = returning(100, 1, Expr::Register(Reg(0)));
    assert!(query(&source, &other, &[Reg(0)], &[Reg(0)]).is_ok());
    assert_eq!(shape::inspect(&source).unwrap(), [0]);
}

#[test]
fn witnesses_replay_distinct_unshared_inputs_and_reject_a_forged_equal_result() {
    let source = returning(0, 1, Expr::Register(Reg(0)));
    let independent = query(&source, &source, &[], &[]).unwrap();
    let mut values = model(&independent);
    values.insert(independent.input_names[0].clone(), 11);
    values.insert(independent.candidate_names[0].clone(), 12);
    let witness = independent.replay(&values).unwrap();
    assert_eq!(witness.before.status, RunStatus::Returned(11));
    assert_eq!(witness.after.status, RunStatus::Returned(12));
    let same = query(&source, &source, &[Reg(0)], &[Reg(0)]).unwrap();
    assert_eq!(same.input_names, same.candidate_names);
    assert_eq!(
        same.replay(&model(&same)),
        Err(UnknownReason::InvalidCounterexample)
    );
    let mut invalid = model(&independent);
    invalid.insert("size".into(), REPLAY_BYTES + 1);
    assert_eq!(
        independent.replay(&invalid),
        Err(UnknownReason::ReplayLimit)
    );
    invalid.insert("base".into(), u64::MAX);
    invalid.insert("size".into(), 1);
    assert_eq!(
        independent.replay(&invalid),
        Err(UnknownReason::ReplayLimit)
    );
}

#[test]
fn normal_liveouts_are_explicit_and_fault_snapshots_keep_their_separate_scope() {
    let mut left = returning(0, 1, Expr::Const(7));
    let mut instructions = left.instructions().to_vec();
    instructions[0].assignments.push(Assignment {
        destination: Reg(0).into(),
        value: Expr::Const(8),
    });
    let right = Program::new(0, 1, instructions).unwrap();
    let unobserved = query(&left, &right, &[Reg(0)], &[]).unwrap();
    let mut values = model(&unobserved);
    values.insert(unobserved.input_names[0].clone(), 9);
    assert_eq!(
        unobserved.replay(&values),
        Err(UnknownReason::InvalidCounterexample)
    );
    let observed = query(&left, &right, &[Reg(0)], &[Reg(0)]).unwrap();
    let mut values = model(&observed);
    values.insert(observed.input_names[0].clone(), 9);
    assert!(observed.replay(&values).is_ok());
    left = returning(0, 1, Expr::load(Expr::Const(u64::MAX), Width::U64));
    let mut instructions = left.instructions().to_vec();
    instructions[0].assignments.push(Assignment {
        destination: Reg(0).into(),
        value: Expr::Const(8),
    });
    let right = Program::new(0, 1, instructions).unwrap();
    let same_fault = query(&left, &right, &[Reg(0)], &[Reg(0)]).unwrap();
    assert_eq!(
        same_fault.replay(&model(&same_fault)),
        Err(UnknownReason::InvalidCounterexample)
    );
}

#[test]
fn an_unavailable_solver_keeps_an_explicit_unknown_verdict() {
    let program = returning(0, 1, Expr::Const(1));
    let query = query(&program, &program, &[], &[]).unwrap();
    assert!(matches!(
        query.check(&Solver::new("/nirvana-no-such-solver/z3")),
        Verdict::Unknown(UnknownReason::SolverUnavailable(_))
    ));
}

#[test]
fn the_machine_register_space_keeps_sparse_region_boundaries() {
    let source = returning(0, 80, Expr::Register(Reg(79)));
    let other = returning(100, 80, Expr::Register(Reg(79)));
    assert!(query(&source, &other, &[Reg(79)], &[Reg(79)]).is_ok());
}

mod smt;
