//! Observe the semantic transition selected by C generation, at its own input
//! state boundary. Earlier reduction has a separate return/memory contract.
use nirvana::{
    ir::{ExecutionError, Program, RunReport},
    semantic_ir::Lowering,
};
use std::sync::Arc;

#[path = "semantic_records.rs"]
mod records;

pub(super) struct Stage {
    pub status: &'static str,
    lowering: Option<Arc<Lowering>>,
    observations: usize,
    failure: Option<String>,
    records: String,
}
impl Stage {
    pub fn new(machine: &Program, lowering: Option<Arc<Lowering>>) -> Self {
        let mut stage = Self {
            status: "not_applied",
            lowering,
            observations: 0,
            failure: None,
            records: String::new(),
        };
        if let Some(lowering) = &stage.lowering {
            if lowering.source().register_count() >= machine.register_count() && lowering.validate()
            {
                stage.status = "passed";
            } else {
                stage.status = "rejected";
                stage.failure = Some("Selected Semantic IR lowering failed validation\n".into());
            }
        }
        stage
    }
    fn record(
        &mut self,
        expected: &Result<RunReport, ExecutionError>,
        actual: &Result<RunReport, ExecutionError>,
        input: &[u64],
        initial: u64,
        budget: usize,
        case: usize,
    ) {
        let (Ok(left), Ok(right)) = (expected, actual) else {
            self.status = "rejected";
            self.failure = Some(format!(
                "Semantic execution profile error: expected={expected:?}, actual={actual:?}\n"
            ));
            return;
        };
        let Some(record) = records::pair(case, budget, initial, input, left, right) else {
            self.status = "rejected";
            self.failure = Some("Semantic observer requires flat guest memory\n".into());
            return;
        };
        if record.len() > records::MAX_LINE_BYTES
            || self.records.len().saturating_add(record.len()) > records::MAX_BYTES
        {
            self.status = "budget_exhausted";
            self.failure = Some(
                "Semantic state-pair record budget exceeded (4 MiB/row, 128 MiB/file)\n".into(),
            );
            return;
        }
        self.records.push_str(&record);
        self.observations += 1;
        if actual != expected {
            self.status = "counterexample";
            self.failure = Some(format!(
                "selected_semantic, fresh_initial={initial}, input={input:?}, budget={budget}\nexpected={expected:?}\nactual={actual:?}\n"
            ));
        }
    }
    pub fn check(&mut self, input: &[u64], ram: &[u8], budget: usize, case: usize) {
        if self.status != "passed" {
            return;
        }
        let Some(lowering) = self.lowering.clone() else {
            return;
        };
        for initial in [0, u64::MAX] {
            let mut extended = input.to_vec();
            extended.resize(lowering.source().register_count(), initial);
            let expected =
                lowering
                    .source()
                    .run_with_memory(&extended, super::super::BASE, ram, budget);
            extended.resize(lowering.program().register_count(), initial);
            let actual = lowering
                .program()
                .run_with_memory(&extended, super::super::BASE, ram, budget)
                .and_then(|report| {
                    let actual = report.state.registers.len();
                    lowering
                        .project_report(report)
                        .ok_or(ExecutionError::RegisterCount {
                            expected: lowering.program().register_count(),
                            actual,
                        })
                });
            self.record(&expected, &actual, input, initial, budget, case);
            if self.status != "passed" {
                break;
            }
        }
    }
    pub fn json(&self, out: &std::path::Path) -> std::io::Result<String> {
        let witness = if let Some(failure) = &self.failure {
            std::fs::write(out.join("selected_semantic.witness.txt"), failure)?;
            "\"selected_semantic.witness.txt\""
        } else {
            "null"
        };
        let semantic = if let Some(lowering) = &self.lowering {
            std::fs::write(out.join(records::FILE), &self.records)?;
            for (name, program) in [
                ("selected-semantic-input.ir.txt", lowering.source()),
                ("selected-semantic-lowered.ir.txt", lowering.program()),
            ] {
                std::fs::write(
                    out.join(name),
                    format!(
                        "entry={} registers={}\n{:#?}\n",
                        program.cfg().block(program.cfg().entry()).start,
                        program.register_count(),
                        program.instructions()
                    ),
                )?;
            }
            let e = lowering.evidence();
            format!(
                "{{\"model\":\"selected-semantic-input-state-v1\",\"source_registers\":{},\"lowered_registers\":{},\"fresh_initializers\":[0,{}],\"inputs\":{},\"divisions\":{},\"remainders\":{},\"replaced_subtrees\":{},\"input_ir\":\"selected-semantic-input.ir.txt\",\"lowered_ir\":\"selected-semantic-lowered.ir.txt\",\"state_pairs\":{{\"model\":\"selected-semantic-state-pairs-v1\",\"file\":\"selected-semantic-states.jsonl\"}}}}",
                lowering.source().register_count(),
                lowering.program().register_count(),
                u64::MAX,
                e.inputs,
                e.divisions,
                e.remainders,
                e.replaced_subtrees
            )
        } else {
            "null".into()
        };
        Ok(format!(
            "{{\"name\":\"selected_semantic\",\"status\":\"{}\",\"observations\":{},\"witness\":{witness},\"semantic\":{semantic}}}",
            self.status, self.observations
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nirvana::{
        ir::{Assignment, BinaryOp as B, Control, Expr, IrInstruction, Reg, RunStatus, Width},
        semantic_ir::SemanticPlan,
    };
    fn source() -> Program {
        let r = |n| Expr::Register(Reg(n));
        let c = Expr::Const;
        let b = Expr::binary;
        let quotient = b(
            B::Sub,
            b(
                B::AShr,
                b(B::SMulHigh, c(0x6666_6666_6666_6667), r(0)),
                c(2),
            ),
            b(B::AShr, r(0), c(63)),
        );
        Program::new(
            0,
            2,
            vec![
                IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![Assignment {
                        destination: Reg(0).into(),
                        value: Expr::load(r(1), Width::U64),
                    }],
                    control: Control::Next,
                },
                IrInstruction {
                    address: 1,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(quotient),
                },
            ],
        )
        .unwrap()
    }
    fn lowering(source: &Program) -> Arc<Lowering> {
        Arc::new(
            SemanticPlan::analyze(source)
                .unwrap()
                .lowering(source)
                .unwrap(),
        )
    }
    #[test]
    fn selected_captures_match_input_registers_ram_faults_and_every_small_cutoff() {
        let source = source();
        let lowering = lowering(&source);
        for value in [0u64, 1, 1 << 63, u64::MAX] {
            for pointer in [
                super::super::super::BASE,
                super::super::super::BASE + 1,
                u64::MAX,
            ] {
                let mut stage = Stage::new(&source, Some(lowering.clone()));
                for budget in 0..=3 {
                    stage.check(&[33, pointer], &value.to_le_bytes(), budget, 0);
                }
                assert_eq!(stage.status, "passed", "{:?}", stage.failure);
                assert_eq!(stage.observations, 8);
            }
        }
    }
    #[test]
    fn only_capture_registers_are_projected_and_fault_or_input_corruption_is_reported() {
        let source = source();
        let lowering = lowering(&source);
        let input = [33, super::super::super::BASE];
        let ram = 42u64.to_le_bytes();
        let expected = source
            .run_with_memory(&input, super::super::super::BASE, &ram, 2)
            .unwrap();
        let mut extended = input.to_vec();
        extended.resize(lowering.program().register_count(), 0);
        let good = lowering
            .program()
            .run_with_memory(&extended, super::super::super::BASE, &ram, 2)
            .unwrap();
        assert!(lowering.project_report(expected.clone()).is_none());
        for field in ["private", "input", "status", "pc", "ram"] {
            let mut actual = good.clone();
            match field {
                "private" => *actual.state.registers.last_mut().unwrap() ^= 1,
                "input" => actual.state.registers[0] ^= 1,
                "status" => actual.status = RunStatus::Returned(99),
                "pc" => actual.state.instruction = Some(999),
                _ => actual.state.memory[0] ^= 1,
            }
            let mut stage = Stage::new(&source, Some(lowering.clone()));
            stage.record(
                &Ok(expected.clone()),
                &Ok(lowering.project_report(actual).unwrap()),
                &input,
                0,
                2,
                0,
            );
            assert_eq!(
                stage.status,
                if field == "private" {
                    "passed"
                } else {
                    "counterexample"
                }
            );
        }
    }
    #[test]
    fn a_result_depending_on_private_initial_state_is_caught_by_the_second_pattern() {
        let source = source();
        let lowering = lowering(&source);
        let input = [0, super::super::super::BASE];
        let ram = 0u64.to_le_bytes();
        let expected = source
            .run_with_memory(&input, super::super::super::BASE, &ram, 2)
            .unwrap();
        let mut stage = Stage::new(&source, Some(lowering));
        for initial in [0, u64::MAX] {
            let mut actual = expected.clone();
            actual.status = RunStatus::Returned(initial);
            stage.record(&Ok(expected.clone()), &Ok(actual), &input, initial, 2, 0);
        }
        assert_eq!(stage.status, "counterexample");
        assert_eq!(stage.observations, 2);
        assert!(
            stage
                .failure
                .unwrap()
                .contains(&format!("fresh_initial={}", u64::MAX))
        );
    }
}
