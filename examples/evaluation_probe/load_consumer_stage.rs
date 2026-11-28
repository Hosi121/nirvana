//! Raw state-pair observations for the checked load-consumer presentation pair.
//! Private temporary values remain in artifacts; only comparison projects them.
use super::{
    records,
    storage_artifacts::{Text, quote},
};
use nirvana::{
    ir::{ExecutionError, RunReport},
    load_consumer::Lowering,
    readable::{self, ReadableC},
};
use std::fmt::Write;
use std::{collections::BTreeSet, sync::Arc};

const WORK: usize = 4_000_000;
pub(super) const NAME: &str = "selected_load_consumer";

pub(super) struct Stage {
    pub status: &'static str,
    lowering: Option<Arc<Lowering>>,
    private: BTreeSet<usize>,
    observations: usize,
    work: usize,
    failure: Option<String>,
    records: records::Buffer,
}

impl Stage {
    pub fn new(output: &ReadableC) -> Self {
        let mut stage = Self {
            status: "not_applied",
            lowering: output.load_consumer_lowering.clone(),
            private: BTreeSet::new(),
            observations: 0,
            work: 0,
            failure: None,
            records: records::Buffer::default(),
        };
        if let Some(lowering) = &stage.lowering {
            stage
                .private
                .extend(lowering.evidence().folds.iter().map(|f| f.temporary.0));
            if lowering.validate().is_err() || readable::loop_recovery::source(output).is_err() {
                stage.status = "rejected";
                stage.failure =
                    Some("Selected load-consumer source/display binding failed\n".into());
            } else {
                stage.status = "passed";
            }
        }
        stage
    }

    fn record(
        &mut self,
        expected: Result<RunReport, ExecutionError>,
        actual: Result<RunReport, ExecutionError>,
        input: &[u64],
        initial: u64,
        budget: usize,
        case: usize,
    ) {
        let (Ok(left), Ok(right)) = (expected, actual) else {
            self.status = "rejected";
            self.failure = Some("Load-consumer execution inputs rejected\n".into());
            return;
        };
        let Some(record) = records::pair(case, budget, initial, input, &left, &right) else {
            self.status = "rejected";
            self.failure = Some("Load-consumer observer requires flat memory\n".into());
            return;
        };
        if !self.records.push(record) {
            self.status = "budget_exhausted";
            self.failure = Some("Load-consumer state-pair budget exceeded\n".into());
            return;
        }
        self.observations += 1;
        if budget == 0 && left != right || !equal_public(&left, &right, &self.private) {
            self.status = "counterexample";
            self.failure = Some(format!(
                "{NAME}, fresh={initial}, input={input:?}, budget={budget}\nexpected={left:?}\nactual={right:?}\n"
            ));
        }
    }

    pub fn check(&mut self, input: &[u64], ram: &[u8], budget: usize, case: usize) {
        if self.status != "passed" {
            return;
        }
        let cost = budget.saturating_mul(4);
        if self.work.saturating_add(cost) > WORK {
            self.status = "budget_exhausted";
            self.failure =
                Some("Independent load-consumer execution-work budget exceeded\n".into());
            return;
        }
        self.work += cost;
        let Some(lowering) = self.lowering.clone() else {
            return;
        };
        if input.len() > lowering.source().register_count() {
            self.status = "rejected";
            self.failure = Some("Machine input exceeds load-consumer namespace\n".into());
            return;
        }
        for initial in [0, u64::MAX] {
            let mut extended = input.to_vec();
            extended.resize(lowering.source().register_count(), initial);
            let expected =
                lowering
                    .source()
                    .run_with_memory(&extended, super::super::BASE, ram, budget);
            let actual =
                lowering
                    .program()
                    .run_with_memory(&extended, super::super::BASE, ram, budget);
            self.record(expected, actual, input, initial, budget, case);
            if self.status != "passed" {
                break;
            }
        }
    }

    pub fn json(&self, out: &std::path::Path) -> std::io::Result<String> {
        let witness = if let Some(failure) = &self.failure {
            let name = format!("{NAME}.witness.txt");
            std::fs::write(out.join(&name), failure)?;
            quote(&name)
        } else {
            "null".into()
        };
        let transition = if let Some(lowering) = &self.lowering {
            for (name, program) in [
                ("load-consumer-input.ir.txt", lowering.source()),
                ("load-consumer-lowered.ir.txt", lowering.program()),
            ] {
                let mut text = Text(String::new());
                write!(
                    text,
                    "entry={} registers={}\n{:#?}\n",
                    program.cfg().block(program.cfg().entry()).start,
                    program.register_count(),
                    program.instructions()
                )
                .map_err(|_| std::io::Error::other("load-consumer IR artifact budget"))?;
                std::fs::write(out.join(name), text.0)?;
            }
            std::fs::write(
                out.join("load-consumer-states.jsonl"),
                self.records.as_str(),
            )?;
            let model = lowering.model_id();
            let stable = model != nirvana::load_consumer::MODEL_ID;
            let memory = model == nirvana::load_consumer::MEMORY_MODEL_ID;
            let checker = if memory {
                "load_consumer::validate_memory_values+readable::loop_recovery::source"
            } else if stable {
                "load_consumer::validate_with_stable_inputs+readable::loop_recovery::source"
            } else {
                "load_consumer::validate+readable::loop_recovery::source"
            };
            let folds = lowering.evidence().folds.iter().map(|f| {
                let inputs = if stable {
                    let inputs = f.inputs.iter().map(|r|r.0).collect::<Vec<_>>();
                    format!(",\"inputs\":{inputs:?}")
                } else { String::new() };
                let producer = if memory { format!(",\"producer_kind\":\"{}\"", f.producer_kind.as_str()) } else { String::new() };
                format!(
                    "{{\"load_pc\":{},\"load_assignment\":{},\"consumer_pc\":{},\"consumer_assignment\":{},\"temporary\":{},\"destination\":{}{inputs}{producer}}}",
                    f.load_instruction, f.load_assignment, f.consumer_instruction,
                    f.consumer_assignment, f.temporary.0, f.destination.0
                )
            }).collect::<Vec<_>>().join(",");
            let private = self.private.iter().copied().collect::<Vec<_>>();
            let parameters = lowering
                .parameters()
                .iter()
                .map(|r| r.0)
                .collect::<Vec<_>>();
            format!(
                "{{\"model\":\"{model}\",\"checker\":\"{checker}\",\"registers\":{},\"entry\":{},\"parameters\":{parameters:?},\"private_registers\":{private:?},\"folds\":[{folds}],\"input_ir\":\"load-consumer-input.ir.txt\",\"lowered_ir\":\"load-consumer-lowered.ir.txt\",\"state_pairs\":{{\"model\":\"load-consumer-state-pairs-v1\",\"file\":\"load-consumer-states.jsonl\",\"encoding\":\"{}\",\"decoded_bytes\":{}}}}}",
                lowering.source().register_count(),
                lowering
                    .source()
                    .cfg()
                    .block(lowering.source().cfg().entry())
                    .start,
                records::ENCODING,
                self.records.decoded_bytes()
            )
        } else {
            "null".into()
        };
        Ok(format!(
            "{{\"name\":\"{NAME}\",\"status\":{:?},\"observations\":{},\"witness\":{witness},\"comparisons\":[\"lowered_zero\",\"lowered_ones\"],\"transition\":{transition}}}",
            self.status, self.observations
        ))
    }
}

fn equal_public(left: &RunReport, right: &RunReport, private: &BTreeSet<usize>) -> bool {
    if left.state.registers.len() != right.state.registers.len()
        || private.iter().any(|r| *r >= left.state.registers.len())
    {
        return false;
    }
    let mut actual = right.clone();
    for &r in private {
        actual.state.registers[r] = left.state.registers[r];
    }
    *left == actual
}

#[cfg(test)]
mod tests {
    use super::*;
    use nirvana::ir::{
        Assignment, BinaryOp as B, Control, Expr, IrInstruction, Program, Reg, Width,
    };

    fn source(constant: u64) -> Program {
        let r = |n| Expr::Register(Reg(n));
        let set = |n, value| Assignment {
            destination: Reg(n).into(),
            value,
        };
        Program::new(
            0,
            4,
            vec![
                IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![set(1, Expr::load(r(0), Width::U64))],
                    control: Control::Next,
                },
                IrInstruction {
                    address: 1,
                    size: 1,
                    assignments: vec![set(
                        3,
                        Expr::load(Expr::binary(B::Add, r(0), Expr::Const(8)), Width::U64),
                    )],
                    control: Control::Next,
                },
                IrInstruction {
                    address: 2,
                    size: 1,
                    assignments: vec![set(
                        2,
                        Expr::binary(
                            B::Add,
                            Expr::binary(B::And, r(1), Expr::Const(3)),
                            Expr::Const(constant),
                        ),
                    )],
                    control: Control::Return(Expr::binary(B::Xor, r(2), r(3))),
                },
            ],
        )
        .unwrap()
    }
    fn render(constant: u64) -> ReadableC {
        readable::emit_readable_c_with_storage_provenance(
            &source(constant),
            readable::ReadableOptions::default(),
        )
        .unwrap()
    }
    fn checked_stage() -> Stage {
        let lowering = Arc::new(nirvana::load_consumer::lower(&source(1), &[Reg(0)]).unwrap());
        lowering.validate().unwrap();
        Stage {
            status: "passed",
            private: lowering
                .evidence()
                .folds
                .iter()
                .map(|f| f.temporary.0)
                .collect(),
            lowering: Some(lowering),
            observations: 0,
            work: 0,
            failure: None,
            records: records::Buffer::default(),
        }
    }

    #[test]
    fn observes_real_private_differences_aliases_faults_and_prefixes_without_erasing_them() {
        for pointer in [
            super::super::super::BASE,
            super::super::super::BASE + 1,
            u64::MAX,
        ] {
            let mut stage = checked_stage();
            let input = [pointer, 13, 29, 47];
            for budget in 0..=3 {
                stage.check(&input, &[0xff; 16], budget, 0);
            }
            assert_eq!(stage.status, "passed", "{:?}", stage.failure);
            assert_eq!(stage.observations, 8);
            assert!(!stage.records.as_str().is_empty());
        }
        let stage = checked_stage();
        let lowering = stage.lowering.as_ref().unwrap();
        let input = [super::super::super::BASE, 13, 29, 47];
        let left = lowering
            .source()
            .run_with_memory(&input, super::super::super::BASE, &[0xff; 16], 1)
            .unwrap();
        let right = lowering
            .program()
            .run_with_memory(&input, super::super::super::BASE, &[0xff; 16], 1)
            .unwrap();
        assert_ne!(
            left, right,
            "the raw private value really changes before its consumer"
        );
        assert!(equal_public(&left, &right, &stage.private));
        let record = records::pair(0, 1, 0, &input, &left, &right).unwrap();
        let mut buffer = records::Buffer::default();
        assert!(buffer.push(record));
        assert!(buffer.as_str().contains("18446744073709551615"));
    }

    #[test]
    fn reports_each_observable_corruption_and_rejects_foreign_source_binding() {
        let mut output = render(1);
        let lowering = checked_stage().lowering.unwrap();
        let input = [super::super::super::BASE, 13, 29, 47];
        let left = lowering
            .source()
            .run_with_memory(&input, super::super::super::BASE, &[0xff; 16], 1)
            .unwrap();
        let right = lowering
            .program()
            .run_with_memory(&input, super::super::super::BASE, &[0xff; 16], 1)
            .unwrap();
        for field in ["register", "ram", "status", "pc", "trace"] {
            let mut wrong = right.clone();
            match field {
                "register" => wrong.state.registers[0] ^= 1,
                "ram" => wrong.state.memory[0] ^= 1,
                "status" => wrong.status = nirvana::ir::RunStatus::Returned(8),
                "pc" => wrong.state.instruction = Some(991),
                "trace" => wrong.state.trace.push(991),
                _ => unreachable!(),
            }
            let mut stage = checked_stage();
            stage.record(Ok(left.clone()), Ok(wrong), &input, 0, 1, 0);
            assert_eq!(stage.status, "counterexample", "{field}");
        }
        output.load_consumer_lowering = Some(Arc::new(
            nirvana::load_consumer::lower(&source(7), &output.parameters).unwrap(),
        ));
        assert_eq!(Stage::new(&output).status, "rejected");
    }

    #[test]
    fn independent_work_limit_stops_without_claiming_complete_observations() {
        let mut stage = checked_stage();
        stage.work = WORK;
        stage.check(&[0; 4], &[0; 16], 1, 0);
        assert_eq!(stage.status, "budget_exhausted");
        assert_eq!(stage.observations, 0);
    }
}
