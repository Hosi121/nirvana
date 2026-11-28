use super::*;

fn paired_fixture(mask: u64) -> Program {
    let mut code: Vec<_> = fixture()
        .instructions()
        .iter()
        .filter(|i| i.address < 60 || i.address >= 90)
        .cloned()
        .collect();
    for i in &mut code {
        match i.address {
            0 => {
                i.assignments[0].value =
                    Expr::binary(BinaryOp::And, Expr::Register(Reg(7)), Expr::Const(mask))
            }
            10 => i.control = Control::Jump(20),
            20 | 40 => {
                i.assignments[0].value = Expr::binary(
                    BinaryOp::Add,
                    Expr::Register(Reg(0)),
                    Expr::Const((i.address - 20) / 20),
                )
            }
            23 => {
                i.control = Control::Branch {
                    condition: Expr::binary(BinaryOp::Eq, Expr::Register(Reg(7)), Expr::Const(0)),
                    target: 90,
                }
            }
            43 | 44 => i.control = Control::Jump(90),
            _ => {}
        }
    }
    Program::new(0, 9, code).unwrap()
}

#[test]
fn paired_proposals_keep_two_source_events_and_decline_acyclic_or_foreign_sources() {
    let source = paired_fixture(1);
    let ordinary = lane_patterns::discover(&source).unwrap();
    assert!(ordinary.groups().is_empty());
    let found = ordinary.with_pair_groups().unwrap();
    let candidate = propose(&source, &found, 0).unwrap();
    assert_eq!(candidate.rounds(), 2);
    assert_eq!(candidate.envelope().lane_entries, [20, 40]);
    let foreign = paired_fixture(3);
    assert_eq!(propose(&foreign, &found, 0).unwrap_err(), Error::Source);
    let mut acyclic = source.instructions().to_vec();
    acyclic
        .iter_mut()
        .find(|i| i.address == 90)
        .unwrap()
        .control = Control::Jump(100);
    let acyclic = Program::new(0, 9, acyclic).unwrap();
    let acyclic_found = lane_patterns::discover(&acyclic)
        .unwrap()
        .with_pair_groups()
        .unwrap();
    assert_eq!(
        propose(&acyclic, &acyclic_found, 0).unwrap_err(),
        Error::Boundary
    );
    for seed in 0..32u64 {
        for pointer in [1023, 1040, 1136, 1152, u64::MAX] {
            let mut input = vec![0; 9];
            input[1] = pointer;
            input[2] = seed.wrapping_mul(19);
            input[6] = seed ^ 11;
            input[7] = seed;
            let memory: Vec<_> = (0..128u64).map(|n| (n * 29 + seed) as u8).collect();
            let a = source.run_with_memory(&input, 1024, &memory, 1024).unwrap();
            input.push(u64::MAX);
            let b = candidate
                .program()
                .run_with_memory(&input, 1024, &memory, 1024)
                .unwrap();
            assert_eq!(a.status, b.status, "{seed}/{pointer}");
            assert_eq!(a.state.memory, b.state.memory);
        }
    }
}

#[test]
#[ignore = "requires NIRVANA_Z3 and NIRVANA_PAIR_OUT"]
fn paired_lane_source_contract_proofs_require_completion_and_keep_context() {
    let out = std::path::PathBuf::from(std::env::var_os("NIRVANA_PAIR_OUT").unwrap());
    std::fs::create_dir_all(&out).unwrap();
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap())
        .with_timeout(std::time::Duration::from_secs(15));
    let source = paired_fixture(1);
    let found = lane_patterns::discover(&source)
        .unwrap()
        .with_pair_groups()
        .unwrap();
    let proposal = propose(&source, &found, 0).unwrap();
    let problem = proposal.verification_problem().unwrap();
    std::fs::write(
        out.join("pair-completion.smt2"),
        problem.completion_query().smt2(),
    )
    .unwrap();
    std::fs::write(out.join("pair-comparison.smt2"), problem.query().smt2()).unwrap();
    let Outcome::Verified(verified) = problem.check(&solver) else {
        panic!("the bounded paired source must pass original acceptance")
    };
    verified.in_context().unwrap().validate().unwrap();
    use crate::transform::loop_recovery::{self, Outcome as Whole};
    let Whole::Recovered(recovered) =
        loop_recovery::recover(&source, &[Reg(1), Reg(2), Reg(6), Reg(7)], &solver)
    else {
        panic!("the whole pair fallback must recover")
    };
    recovered.validate().unwrap();
    assert_eq!(recovered.entry_attempt().before_lanes, 2);
    let source = paired_fixture(3);
    let found = lane_patterns::discover(&source)
        .unwrap()
        .with_pair_groups()
        .unwrap();
    let proposal = propose(&source, &found, 0).unwrap();
    let problem = proposal.verification_problem().unwrap();
    std::fs::write(
        out.join("pair-incomplete.smt2"),
        problem.completion_query().smt2(),
    )
    .unwrap();
    let Outcome::Incomplete(witness) = problem.check(&solver) else {
        panic!("an over-wide trip domain cannot get a certificate")
    };
    std::fs::write(out.join("pair-incomplete.txt"), format!("{witness:#?}\n")).unwrap();
    println!(
        "PAIRED-LANES bounded completion+source equivalence+context accepted; over-wide bound rejected with retained witness"
    );
}
