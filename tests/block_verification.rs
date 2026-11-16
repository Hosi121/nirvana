use nirvana::block_verify::{BlockVerdict, block_query, validate_program};
use nirvana::ir::{
    AccessKind, Assignment, BlockError, BlockExit, Control, Expr, IrInstruction, Place, Program,
    Reg, Width,
};
use nirvana::reduce::reduce;
use nirvana::verify::{Solver, UnknownReason};

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn p(assignments: Vec<Assignment>, control: Control) -> Program {
    Program::new(
        0,
        3,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control,
        }],
    )
    .unwrap()
}
fn solver() -> Solver {
    Solver::new(std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into()))
}
fn query(a: &Program, b: &Program) -> nirvana::block_verify::BlockQuery {
    block_query(a, b, 0, &[Reg(0), Reg(1), Reg(2)], &[]).unwrap()
}

#[test]
fn block_execution_stops_before_its_successor_and_retains_partial_faults() {
    let p = Program::new(
        0,
        3,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![store(c(0), Width::U8, c(99))],
                control: Control::Jump(1),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![set(0, Expr::load(c(1), Width::U64))],
                control: Control::Return(c(7)),
            },
        ],
    )
    .unwrap();
    let first = p.run_block_with_memory(0, &[0; 3], 0, &[0]).unwrap();
    assert_eq!(first.exit, BlockExit::Next(1));
    assert_eq!(first.state.memory, [99]);
    assert_eq!(first.state.trace, [0]);
    let second = p
        .run_block_with_memory(1, &first.state.registers, 0, &first.state.memory)
        .unwrap();
    assert!(matches!(second.exit, BlockExit::Fault(fault) if fault.access == AccessKind::Read));
    assert_eq!(second.state.memory, [99]);
    assert_eq!(second.state.trace, [1]);
    assert_eq!(
        p.run_block_with_memory(42, &[0; 3], 0, &[]),
        Err(BlockError::UnknownBlock(42))
    );
}

#[test]
fn rejected_shapes_and_missing_solver_do_not_accept_a_program() {
    let a = p(vec![], Control::Return(c(0)));
    let b = Program::new(
        1,
        3,
        vec![IrInstruction {
            address: 1,
            size: 1,
            assignments: vec![],
            control: Control::Return(c(0)),
        }],
    )
    .unwrap();
    let solver = Solver::new("/nirvana-no-such-solver");
    let result = validate_program(&a, &b, &solver);
    assert!(!result.accepted());
    assert_eq!(result.incomplete, Some(UnknownReason::BlockShape));
    let result = validate_program(&a, &a, &solver);
    assert!(!result.accepted());
    assert!(matches!(
        result.blocks[0].verdict,
        BlockVerdict::Unknown(UnknownReason::SolverUnavailable(_))
    ));
    assert_eq!(
        block_query(&a, &a, 0, &[Reg(3)], &[]).unwrap_err(),
        UnknownReason::BoundaryMapping
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3 and run with --include-ignored"]
fn memory_forwarding_partial_widths_and_lazy_reads_are_validated() {
    let solver = solver();
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let before = p(
            vec![store(r(0), width, r(1))],
            Control::Return(Expr::load(r(0), width)),
        );
        let after = p(
            vec![store(r(0), width, r(1))],
            Control::Return(Expr::binary(
                nirvana::ir::BinaryOp::And,
                r(1),
                c(width.mask()),
            )),
        );
        assert_eq!(
            query(&before, &after).check(&solver),
            BlockVerdict::EquivalentUnderModel,
            "{width:?}"
        );
    }
    let before = p(
        vec![],
        Control::Return(Expr::select(
            c(0),
            Expr::load(c(u64::MAX), Width::U64),
            c(7),
        )),
    );
    let after = p(vec![], Control::Return(c(7)));
    assert_eq!(
        query(&before, &after).check(&solver),
        BlockVerdict::EquivalentUnderModel
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3 and run with --include-ignored"]
fn memory_faults_aliases_and_first_fault_effects_produce_replayed_witnesses() {
    let solver = solver();
    let a = p(
        vec![
            store(c(0), Width::U8, c(1)),
            set(0, Expr::load(c(u64::MAX), Width::U64)),
        ],
        Control::Return(c(0)),
    );
    let b = p(
        vec![
            store(c(0), Width::U8, c(2)),
            set(0, Expr::load(c(u64::MAX), Width::U64)),
        ],
        Control::Return(c(0)),
    );
    let BlockVerdict::Counterexample(witness) = query(&a, &b).check(&solver) else {
        panic!("missing pre-fault memory witness")
    };
    assert_eq!(witness.before.exit, witness.after.exit);
    assert!(matches!(witness.before.exit, BlockExit::Fault(_)));
    assert_ne!(witness.before.state.memory, witness.after.state.memory);

    let cases = [
        (
            p(
                vec![
                    set(2, Expr::load(r(0), Width::U64)),
                    store(r(0), Width::U64, c(0)),
                ],
                Control::Return(r(2)),
            ),
            p(
                vec![
                    store(r(0), Width::U64, c(0)),
                    set(2, Expr::load(r(0), Width::U64)),
                ],
                Control::Return(r(2)),
            ),
        ),
        (
            p(vec![], Control::Return(Expr::load(r(0), Width::U8))),
            p(vec![store(r(0), Width::U8, c(0))], Control::Return(c(0))),
        ),
        (
            p(
                vec![store(c(u64::MAX), Width::U64, Expr::load(c(0), Width::U8))],
                Control::Return(c(0)),
            ),
            p(
                vec![
                    set(2, Expr::load(c(0), Width::U8)),
                    store(c(u64::MAX), Width::U64, r(2)),
                ],
                Control::Return(c(0)),
            ),
        ),
        (
            p(
                vec![],
                Control::Return(Expr::select(
                    c(0),
                    Expr::load(c(u64::MAX), Width::U64),
                    c(7),
                )),
            ),
            p(
                vec![set(2, Expr::load(c(u64::MAX), Width::U64))],
                Control::Return(c(7)),
            ),
        ),
    ];
    for (index, (a, b)) in cases.iter().enumerate() {
        let verdict = query(a, b).check(&solver);
        assert!(
            matches!(verdict, BlockVerdict::Counterexample(_)),
            "mutant {index}: {verdict:?}"
        );
    }
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3 and run with --include-ignored"]
fn independent_hidden_inputs_and_loop_boundaries_are_checked() {
    let solver = solver();
    let a = p(vec![], Control::Return(r(0)));
    assert!(matches!(
        block_query(&a, &a, 0, &[], &[]).unwrap().check(&solver),
        BlockVerdict::Counterexample(_)
    ));
    assert_eq!(
        block_query(&a, &a, 0, &[Reg(0)], &[])
            .unwrap()
            .check(&solver),
        BlockVerdict::EquivalentUnderModel
    );
    let looped = Program::new(
        0,
        3,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![set(1, c(0))],
                control: Control::Jump(1),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![set(1, Expr::binary(nirvana::ir::BinaryOp::Add, r(1), c(1)))],
                control: Control::Branch {
                    condition: Expr::binary(nirvana::ir::BinaryOp::Ult, r(1), r(0)),
                    target: 1,
                },
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![],
                control: Control::Return(r(1)),
            },
        ],
    )
    .unwrap();
    let reduced = reduce(&looped).unwrap();
    let result = validate_program(&looped, reduced.program(), &solver);
    assert!(result.accepted(), "{result:?}");
    assert_eq!(result.blocks.len(), 3);
}
