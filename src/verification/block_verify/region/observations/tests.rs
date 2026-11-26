use super::*;
use crate::model::ir::Assignment;

fn varying_return(value: u64) -> Program {
    Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![Assignment {
                destination: Reg(1).into(),
                value: Expr::Const(value),
            }],
            control: Control::Return(Expr::Register(Reg(0))),
        }],
    )
    .unwrap()
}
fn row(value: u64, registers: &[usize]) -> ReturnOutputs {
    ReturnOutputs {
        value,
        registers: registers.iter().copied().map(Reg).collect(),
    }
}
fn inputs(query: &Query, value: u64) -> BTreeMap<String, u64> {
    let mut model: BTreeMap<_, _> = query.names.iter().map(|name| (name.clone(), 0)).collect();
    model.insert(query.input_names[0].clone(), value);
    model
}

#[test]
fn replay_selects_the_actual_return_and_unlisted_returns_observe_all_registers() {
    let left = varying_return(3);
    let right = varying_return(4);
    let q = query_at_returns(&left, &right, &[Reg(0)], &[row(1, &[]), row(2, &[1])]).unwrap();
    assert_eq!(
        q.replay(&inputs(&q, 1)),
        Err(UnknownReason::InvalidCounterexample)
    );
    for value in [0, 2, 3, u64::MAX] {
        let witness = q.replay(&inputs(&q, value)).unwrap();
        assert_eq!(witness.before.status, RunStatus::Returned(value));
        assert_eq!(witness.before.state.registers[1], 3);
        assert_eq!(witness.after.state.registers[1], 4);
    }
    let q = query_at_returns(&left, &right, &[Reg(0)], &[]).unwrap();
    assert!(q.replay(&inputs(&q, 1)).is_ok());
}

#[test]
fn malformed_or_oversized_return_interfaces_are_rejected_before_solving() {
    let source = varying_return(1);
    for rows in [
        vec![row(0, &[2])],
        vec![row(1, &[]), row(1, &[1])],
        vec![row(0, &vec![1; MAX_REGISTERS + 1])],
        (0..=MAX_INSTRUCTIONS as u64)
            .map(|value| row(value, &[]))
            .collect(),
    ] {
        assert!(matches!(
            query_at_returns(&source, &source, &[], &rows),
            Err(Error::BoundaryMapping)
        ));
    }
}

#[test]
fn return_status_memory_and_faults_are_observed_even_with_no_registers() {
    let source = varying_return(3);
    let other = varying_return(4);
    let q = query_at_returns(&source, &other, &[], &[row(0, &[]), row(1, &[])]).unwrap();
    let mut values = inputs(&q, 0);
    values.insert(q.candidate_names[0].clone(), 1);
    assert!(q.replay(&values).is_ok());

    let faulting = |address| {
        Program::new(
            0,
            2,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(1).into(),
                    value: Expr::load(Expr::Const(address), Width::U8),
                }],
                control: Control::Return(Expr::Const(0)),
            }],
        )
        .unwrap()
    };
    let q = query_at_returns(&faulting(1), &faulting(2), &[], &[row(0, &[])]).unwrap();
    let witness = q.replay(&inputs(&q, 0)).unwrap();
    assert!(matches!(witness.before.status, RunStatus::Fault(_)));
    assert_ne!(witness.before.status, witness.after.status);
}

#[test]
#[ignore = "requires NIRVANA_Z3 for actual solver/replay checks"]
fn solver_observes_guarded_registers_default_returns_and_global_memory_effects() {
    let solver = Solver::new(std::env::var("NIRVANA_Z3").expect("set NIRVANA_Z3"))
        .with_timeout(std::time::Duration::from_secs(5));
    let left = varying_return(3);
    let right = varying_return(4);
    let rows = [row(1, &[])];
    let q = query_at_returns(&left, &right, &[Reg(0)], &rows).unwrap();
    let Verdict::Counterexample(witness) = q.check(&solver) else {
        panic!("unlisted return must expose the register difference")
    };
    assert_ne!(witness.before.status, RunStatus::Returned(1));
    let mut instructions = right.instructions().to_vec();
    instructions[0].control = Control::Return(Expr::Const(1));
    let right = Program::new(0, 2, instructions).unwrap();
    let mut instructions = left.instructions().to_vec();
    instructions[0].control = Control::Return(Expr::Const(1));
    let left = Program::new(0, 2, instructions).unwrap();
    let q = query_at_returns(&left, &right, &[], &rows).unwrap();
    assert_eq!(q.check(&solver), Verdict::EquivalentUnderModel);
    let q = query_at_returns(&left, &right, &[], &[row(1, &[1])]).unwrap();
    assert!(matches!(q.check(&solver), Verdict::Counterexample(_)));

    let storing = |value| {
        Program::new(
            0,
            2,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![Assignment {
                    destination: Place::Memory {
                        address: Expr::Const(0),
                        width: Width::U8,
                    },
                    value: Expr::Const(value),
                }],
                control: Control::Return(Expr::Const(1)),
            }],
        )
        .unwrap()
    };
    let q = query_at_returns(&storing(3), &storing(4), &[], &rows).unwrap();
    let Verdict::Counterexample(witness) = q.check(&solver) else {
        panic!("empty register observations must retain every byte write")
    };
    assert_ne!(witness.before.state.memory, witness.after.state.memory);
    println!("RETURN-OUTPUTS equivalent=1 replayed=3 global_memory=true fallback=true");
}
