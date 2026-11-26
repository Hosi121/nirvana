//! Concrete replay is separate from the abstract event model's branch choices.
use super::*;
use crate as library;
#[path = "../../../tests/support/formal_structure.rs"]
mod cases;

fn run_ast(case: &cases::Case, input: &[u64], memory: &[u8], budget: usize) -> RunReport {
    let mut machine = Machine::with_memory(2, input, 0, memory, budget).unwrap();
    let result = match execute_nodes(&case.body, &mut machine) {
        Ok(Signal::Return(value)) => Ok(value),
        Err(stop) => Err(stop),
        _ => panic!("trial AST fell through"),
    };
    machine.finish(result)
}

#[test]
fn exported_trial_candidates_replay_through_real_validator_and_executor() {
    let cases = cases::cases();
    let mut positives = 0;
    let mut witnesses = 0;
    let mut outcomes = [false; 3];
    for (index, case) in cases.iter().enumerate() {
        let accepted = structure_verify::validate(&case.program, &case.body).is_ok();
        assert_eq!(
            accepted,
            !(3..9).contains(&index) || case.early_budget,
            "{}",
            case.name
        );
        let mut different = false;
        for input in [[0, 0], [1, 0], [0, 1], [1, 1]] {
            for memory in [&[][..], &[0, 1][..]] {
                for budget in 0..=6 {
                    let source = case
                        .program
                        .run_with_memory(&input, 0, memory, budget)
                        .unwrap();
                    let ast = run_ast(case, &input, memory, budget);
                    outcomes[match source.status {
                        crate::ir::RunStatus::Returned(_) => 0,
                        crate::ir::RunStatus::Fault(_) => 1,
                        crate::ir::RunStatus::Suspended => 2,
                    }] = true;
                    // RunReport includes complete registers/RAM/layout, trace,
                    // attempted instruction, status and return/fault details.
                    if accepted {
                        assert_eq!(source, ast, "{} budget={budget}", case.name);
                    }
                    different |= source != ast;
                    if !(3..9).contains(&index) {
                        positives += 1;
                    }
                }
            }
        }
        if !accepted {
            assert!(different, "{} has no concrete replay witness", case.name);
            witnesses += 1;
        }
    }
    assert_eq!(positives, 672);
    assert_eq!(witnesses, 5);
    assert!(outcomes.into_iter().all(|seen| seen));
}
