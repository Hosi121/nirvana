use super::*;
use crate::model::ir::{BlockExit, Width};

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn b(op: BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn fixture() -> Program {
    Program::new(
        0,
        6,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    set(
                        1,
                        b(
                            BinaryOp::Add,
                            b(BinaryOp::And, Expr::load(r(3), Width::U8), c(3)),
                            c(1),
                        ),
                    ),
                    set(0, c(0)),
                ],
                control: Control::Jump(10),
            },
            IrInstruction {
                address: 10,
                size: 1,
                assignments: vec![set(4, Expr::load(r(3), Width::U8))],
                control: Control::Next,
            },
            IrInstruction {
                address: 11,
                size: 1,
                assignments: vec![Assignment {
                    destination: Place::Memory {
                        address: b(BinaryOp::Add, r(3), c(8)),
                        width: Width::U8,
                    },
                    value: b(BinaryOp::Add, r(4), r(0)),
                }],
                control: Control::Next,
            },
            IrInstruction {
                address: 12,
                size: 1,
                assignments: vec![],
                control: Control::Branch {
                    condition: b(BinaryOp::And, r(4), c(8)),
                    target: 30,
                },
            },
            IrInstruction {
                address: 13,
                size: 1,
                assignments: vec![set(2, b(BinaryOp::Add, r(0), c(1))), set(0, r(2))],
                control: Control::Branch {
                    condition: b(BinaryOp::Ne, r(0), r(1)),
                    target: 10,
                },
            },
            IrInstruction {
                address: 14,
                size: 1,
                assignments: vec![],
                control: Control::Return(r(0)),
            },
            IrInstruction {
                address: 30,
                size: 1,
                assignments: vec![],
                control: Control::Return(b(BinaryOp::Add, r(0), r(1))),
            },
        ],
    )
    .unwrap()
}
fn normalizers() -> Vec<Assignment> {
    let low = Expr::select(b(BinaryOp::Ult, r(1), c(1)), c(1), r(1));
    vec![
        set(
            1,
            Expr::select(b(BinaryOp::Ult, c(4), low.clone()), c(4), low),
        ),
        set(
            0,
            Expr::select(
                b(BinaryOp::Ult, r(0), r(1)),
                r(0),
                b(BinaryOp::Sub, r(1), c(1)),
            ),
        ),
        set(0, b(BinaryOp::And, r(0), c(3))),
    ]
}
fn solver() -> Solver {
    Solver::new(std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into()))
        .with_timeout(Duration::from_secs(5))
}

#[test]
fn source_projection_and_normalizer_shapes_are_checked_before_solving() {
    let source = fixture();
    let problem = Problem::new(&source, 10, &normalizers()).unwrap();
    problem.validate().unwrap();
    assert!(same(problem.source(), &source));
    assert_eq!(problem.header(), 10);
    for expression in [
        Expr::load(r(3), Width::U8),
        Expr::select(c(0), Expr::load(r(3), Width::U8), r(0)),
        Expr::select(c(1), r(0), Expr::load(r(3), Width::U8)),
    ] {
        let mut value = normalizers();
        // Memory in a lazy unselected arm is still an impure assumption.
        value[1].value = expression;
        assert_eq!(
            Problem::new(&source, 10, &value).unwrap_err(),
            Error::Normalizer
        );
    }
    let mut invalid = normalizers();
    invalid[0].destination = Place::Memory {
        address: r(3),
        width: Width::U8,
    };
    assert_eq!(
        Problem::new(&source, 10, &invalid).unwrap_err(),
        Error::Normalizer
    );
    invalid = normalizers();
    invalid[0].value = r(6);
    assert_eq!(
        Problem::new(&source, 10, &invalid).unwrap_err(),
        Error::Normalizer
    );
    assert!(matches!(
        Problem::new(&source, 11, &normalizers()),
        Err(Error::Extraction(_))
    ));
    assert_eq!(
        Problem::new(&source, 10, &vec![set(0, c(0)); MAX_NORMALIZERS + 1]).unwrap_err(),
        Error::Limit
    );
}

#[test]
fn independent_source_execution_visits_only_the_proposed_header_states() {
    let source = fixture();
    let mut headers = 0;
    for value in 0..=15u64 {
        for pointer in [4096, 4121, u64::MAX] {
            for initial in [0, u64::MAX] {
                let mut input = vec![initial; 6];
                input[3] = pointer;
                let mut memory = vec![value as u8; 32];
                let mut pc = 0;
                for _ in 0..16 {
                    if pc == 10 {
                        headers += 1;
                        // Deliberately independent of the normalizer predicate.
                        assert!(
                            (1..=4).contains(&input[1]) && input[0] < input[1] && input[0] <= 3
                        );
                    }
                    let report = source
                        .run_block_with_memory(pc, &input, 4096, &memory)
                        .unwrap();
                    input = report.state.registers;
                    memory = report.state.memory;
                    match report.exit {
                        BlockExit::Next(next) => pc = next,
                        BlockExit::Returned(_) | BlockExit::Fault(_) => break,
                    }
                }
            }
        }
    }
    assert!(headers > 32);
}

#[test]
fn property_instrumentation_cannot_omit_guards_markers_or_observations() {
    let problem = Problem::new(&fixture(), 10, &normalizers()).unwrap();
    for variant in 0..4 {
        let mut changed = problem.clone();
        let query = &changed.feedback;
        let mut body = query.after.instructions().to_vec();
        let marker = Reg(query.after.register_count() - 1);
        let mut outputs = vec![marker];
        let mut shared = query.shared_inputs().to_vec();
        match variant {
            0 => {
                body.iter_mut()
                    .flat_map(|i| &mut i.assignments)
                    .filter(|a| a.destination == Place::Register(marker))
                    .last()
                    .unwrap()
                    .value = c(0)
            }
            1 => {
                body[0].assignments.remove(1);
            }
            2 => outputs.clear(),
            _ => {
                shared.pop();
            }
        }
        let program =
            Program::new(entry(&query.after), query.after.register_count(), body).unwrap();
        changed.feedback = super::super::query(&query.before, &program, &shared, &outputs).unwrap();
        assert!(changed.validate().is_err());
        let Outcome::Unproved(failure) =
            changed.check(&Solver::new("/missing/solver"), Duration::from_secs(1))
        else {
            panic!("invalid property accepted")
        };
        assert_eq!(failure.checked, 0);
        assert_eq!(
            failure.verdict,
            Verdict::Unknown(UnknownReason::BoundaryMapping)
        );
    }
}

#[test]
fn zero_budget_starts_no_solver_and_hidden_cycles_are_rejected() {
    let source = fixture();
    let problem = Problem::new(&source, 10, &normalizers()).unwrap();
    let Outcome::Unproved(failure) = problem.check(&Solver::new("/missing/solver"), Duration::ZERO)
    else {
        panic!("zero budget accepted")
    };
    assert_eq!(failure.checked, 0);
    assert_eq!(
        failure.verdict,
        Verdict::Unknown(UnknownReason::SolverTimeout)
    );
    let mut code = source.instructions().to_vec();
    code.iter_mut().find(|i| i.address == 13).unwrap().control = Control::Jump(13);
    let source = Program::new(0, 6, code).unwrap();
    assert!(matches!(
        Problem::new(&source, 10, &normalizers()),
        Err(Error::Extraction(_))
    ));
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn induction_proves_relational_entry_facts_over_all_words_and_ram() {
    let source = fixture();
    let problem = Problem::new(&source, 10, &normalizers()).unwrap();
    let Outcome::Verified(certificate) = problem.check(&solver(), Duration::from_secs(10)) else {
        panic!("relational invariant was not proved")
    };
    certificate.validate().unwrap();
    assert!(certificate.matches(&source, 10));
    assert_eq!(
        certificate.bit_caps(&source, 10).unwrap(),
        [2, 64, 64, 64, 64, 64]
    );
    let padded = Program::new(0, 7, source.instructions().to_vec()).unwrap();
    assert!(!certificate.matches(&padded, 10));
    assert!(certificate.supports_unused_extension(&padded, 10));
    assert_eq!(
        certificate.bit_caps(&padded, 10).unwrap(),
        [2, 64, 64, 64, 64, 64, 64]
    );
    assert_eq!(
        certificate.bit_caps(&source, 13).unwrap_err(),
        Error::Source
    );
    let mut code = source.instructions().to_vec();
    code.iter_mut().find(|i| i.address == 14).unwrap().control = Control::Return(c(99));
    let other = Program::new(0, 6, code).unwrap();
    assert!(!certificate.supports_unused_extension(&other, 10));
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn missing_relations_and_wrong_initializers_produce_distinct_replayed_failures() {
    let source = fixture();
    let mut weak = normalizers();
    weak.remove(1);
    let problem = Problem::new(&source, 10, &weak).unwrap();
    let Outcome::Unproved(failure) = problem.check(&solver(), Duration::from_secs(10)) else {
        panic!("noninductive width bound accepted")
    };
    assert_eq!(failure.phase, Phase::Feedback);
    assert!(matches!(failure.verdict, Verdict::Counterexample(_)));
    let mut code = source.instructions().to_vec();
    code[0].assignments[1].value = c(4);
    let source = Program::new(0, 6, code).unwrap();
    let problem = Problem::new(&source, 10, &normalizers()).unwrap();
    let Outcome::Unproved(failure) = problem.check(&solver(), Duration::from_secs(10)) else {
        panic!("false initial fact accepted")
    };
    assert_eq!(failure.phase, Phase::Base);
    assert!(matches!(failure.verdict, Verdict::Counterexample(_)));
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn a_header_at_function_entry_requires_the_fact_on_arbitrary_initial_states() {
    let source = fixture();
    let reentered = Program::new(10, 6, source.instructions().to_vec()).unwrap();
    let problem = Problem::new(&reentered, 10, &normalizers()).unwrap();
    let Outcome::Unproved(failure) = problem.check(&solver(), Duration::from_secs(10)) else {
        panic!("uninitialized header facts accepted")
    };
    assert_eq!(failure.phase, Phase::Base);
    assert!(matches!(failure.verdict, Verdict::Counterexample(_)));
    let identity = Problem::new(&reentered, 10, &[set(0, r(0))]).unwrap();
    assert!(matches!(
        identity.check(&solver(), Duration::from_secs(10)),
        Outcome::Verified(_)
    ));
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn an_aliasing_write_and_reload_must_reestablish_the_loop_entry_relation() {
    let source = fixture();
    let mut code = source.instructions().to_vec();
    let store = code.iter_mut().find(|i| i.address == 11).unwrap();
    store.assignments[0].destination = Place::Memory {
        address: r(3),
        width: Width::U8,
    };
    store.assignments[0].value = b(BinaryOp::Xor, r(0), c(3));
    code.iter_mut()
        .find(|i| i.address == 13)
        .unwrap()
        .assignments
        .insert(
            0,
            set(
                1,
                b(
                    BinaryOp::Add,
                    b(BinaryOp::And, Expr::load(r(3), Width::U8), c(3)),
                    c(1),
                ),
            ),
        );
    let source = Program::new(0, 6, code).unwrap();
    let problem = Problem::new(&source, 10, &normalizers()).unwrap();
    let Outcome::Unproved(failure) = problem.check(&solver(), Duration::from_secs(10)) else {
        panic!("alias-modified bound accepted")
    };
    assert_eq!(failure.phase, Phase::Feedback);
    assert!(matches!(failure.verdict, Verdict::Counterexample(_)));
    // Independently replay the actual source from its function entry. The
    // memory write eventually reduces the limit below the current induction.
    let mut input = vec![0; 6];
    input[3] = 4096;
    let mut memory = vec![0; 32];
    let mut pc = 0;
    let mut violated = false;
    for _ in 0..16 {
        if pc == 10 && input[0] >= input[1] {
            violated = true;
            break;
        }
        let report = source
            .run_block_with_memory(pc, &input, 4096, &memory)
            .unwrap();
        input = report.state.registers;
        memory = report.state.memory;
        let BlockExit::Next(next) = report.exit else {
            break;
        };
        pc = next;
    }
    assert!(
        violated,
        "the negative control must have a real source-level violation"
    );
}
