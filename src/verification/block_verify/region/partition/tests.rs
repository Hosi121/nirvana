use super::*;
use crate::model::ir::Assignment;

fn program(value: u64, returned: u64) -> Program {
    Program::new(
        0,
        1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![Assignment {
                destination: Reg(0).into(),
                value: Expr::Const(value),
            }],
            control: Control::Return(Expr::Const(returned)),
        }],
    )
    .unwrap()
}
#[test]
fn partitions_keep_the_original_query_and_zero_budget_starts_no_solver() {
    let source = program(1, 1);
    let q = query_at_returns(
        &source,
        &source,
        &[],
        &[ReturnOutputs {
            value: 1,
            registers: vec![Reg(0)],
        }],
    )
    .unwrap();
    let scripts: Vec<_> = q.partition_smt2().collect();
    assert_eq!(scripts.len(), 3);
    assert!(scripts.iter().all(|script| script.starts_with(q.smt2())));
    let result = q.check_partitioned(&Solver::new("/nirvana-no-solver"), Duration::ZERO);
    assert_eq!(
        result,
        PartitionedVerdict {
            verdict: Verdict::Unknown(UnknownReason::SolverTimeout),
            checked: 0,
            total: 3
        }
    );
    assert!(q.input_partitions(Reg(1), 2).is_err());
    assert!(q.input_partitions(Reg(0), 0).is_err());
    assert!(q.input_partitions(Reg(0), 5).is_err());
    assert_eq!(q.input_partitions(Reg(0), 4).unwrap().smt2().count(), 16);
    let refined = q
        .input_partitions(Reg(0), 2)
        .unwrap()
        .with_return_partitions()
        .unwrap();
    assert_eq!(refined.smt2().count(), 12);
    assert!(refined.smt2().all(|script| script.starts_with(q.smt2())
        && script.contains("checked-input-return-partitions-v1")));
    let result = refined.check(&Solver::new("/nirvana-no-solver"), Duration::ZERO);
    assert_eq!(result.checked, 0);
    assert_eq!(result.total, 12);
    assert_eq!(
        result.verdict,
        Verdict::Unknown(UnknownReason::SolverTimeout)
    );
}

#[test]
#[ignore = "requires NIRVANA_Z3; checks actual Rust partition coverage and omission controls"]
fn generated_guards_cover_all_words_and_omitting_a_case_is_detected() {
    let solver =
        Solver::new(std::env::var("NIRVANA_Z3").unwrap()).with_timeout(Duration::from_secs(5));
    let observations = Observations::at_returns(&[
        ReturnOutputs {
            value: 0,
            registers: vec![],
        },
        ReturnOutputs {
            value: u64::MAX,
            registers: vec![],
        },
    ])
    .unwrap();
    let mut families = vec![(
        String::from("(declare-fun normal () Bool)\n(declare-fun tag () (_ BitVec 64))\n"),
        observations.partition_guards("normal", "tag"),
    )];
    for bits in [1, 2, 3, 4] {
        families.push((
            String::from("(declare-fun input () (_ BitVec 64))\n"),
            input_guards("input", bits),
        ));
    }

    let input = input_guards("input", 2);
    let output = observations.partition_guards("normal", "tag");
    families.push((String::from("(declare-fun normal () Bool)\n(declare-fun tag () (_ BitVec 64))\n(declare-fun input () (_ BitVec 64))\n"),input.iter().flat_map(|i|output.iter().map(move|o|format!("(and {i} {o})"))).collect()));
    for (declarations, guards) in families {
        let formula = |guards: &[String]| {
            format!(
                "(set-logic QF_BV)\n{declarations}(assert (not (or {})))\n",
                guards.join(" ")
            )
        };
        assert_eq!(
            solver.run_smt(&formula(&guards), &[]).unwrap().trim(),
            "unsat"
        );
        for index in 0..guards.len() {
            let mut omitted = guards.clone();
            omitted.remove(index);
            assert_eq!(
                solver.run_smt(&formula(&omitted), &[]).unwrap().trim(),
                "sat",
                "missing case {index}"
            );
        }
    }
    let q = query(&program(1, 1), &program(2, 2), &[], &[]).unwrap();
    assert!(matches!(
        q.input_partitions(Reg(0), 2)
            .unwrap()
            .check(&solver, Duration::from_secs(5))
            .verdict,
        Verdict::Counterexample(_)
    ));
    let refined = q
        .input_partitions(Reg(0), 2)
        .unwrap()
        .with_return_partitions()
        .unwrap()
        .check(&solver, Duration::from_secs(5));
    assert!(matches!(refined.verdict, Verdict::Counterexample(_)));
    println!("PARTITION-COVERAGE all_words=true omission_controls=50");
}

#[test]
#[ignore = "requires NIRVANA_Z3; confirms exhaustive partition proofs and replay"]
fn all_normal_default_and_fault_partitions_retain_effect_observations() {
    let solver =
        Solver::new(std::env::var("NIRVANA_Z3").unwrap()).with_timeout(Duration::from_secs(5));
    let rows = [ReturnOutputs {
        value: 1,
        registers: vec![],
    }];
    let q = query_at_returns(&program(1, 1), &program(2, 1), &[], &rows).unwrap();
    let result = q.check_partitioned(&solver, Duration::from_secs(5));
    assert_eq!(result.verdict, Verdict::EquivalentUnderModel);
    assert_eq!(result.checked, result.total);
    for returned in [0, 2, u64::MAX] {
        let q = query_at_returns(&program(1, returned), &program(2, returned), &[], &rows).unwrap();
        assert!(matches!(
            q.check_partitioned(&solver, Duration::from_secs(5)).verdict,
            Verdict::Counterexample(_)
        ));
    }
    let memory = |value, fault| {
        Program::new(
            0,
            1,
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
                control: Control::Return(if fault {
                    Expr::load(Expr::Const(u64::MAX), Width::U64)
                } else {
                    Expr::Const(1)
                }),
            }],
        )
        .unwrap()
    };
    for fault in [false, true] {
        let q = query_at_returns(&memory(1, fault), &memory(2, fault), &[], &rows).unwrap();
        let Verdict::Counterexample(w) =
            q.check_partitioned(&solver, Duration::from_secs(5)).verdict
        else {
            panic!("RAM differences must be retained even before a fault")
        };
        assert_ne!(w.before.state.memory, w.after.state.memory);
    }
    println!("PARTITIONED-REGIONS equivalent=1 replayed=5 fault_ram=true default=true");
}
