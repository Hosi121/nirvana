//! Source-entry checks for MIR refinements and saved-value materialization.
use super::records;
use nirvana::{
    ir::{Program, RunReport},
    middle_ir::{Error, Function, MemoryEvidence, SavedEvidence, SavedLowering},
};

enum Lowered {
    Plain(Program),
    Saved(SavedLowering),
}
enum Evidence {
    Memory(MemoryEvidence),
    Saved(SavedEvidence),
}
struct Transition {
    input: Program,
    middle: Function,
    lowered: Lowered,
    evidence: Option<Evidence>,
}
pub(super) struct Stage {
    pub name: &'static str,
    pub status: &'static str,
    transition: Option<Transition>,
    observations: usize,
    failure: Option<String>,
    records: String,
    middle_text: Option<String>,
}
impl Stage {
    pub fn plain(name: &'static str, result: Result<Option<(Function, Program)>, Error>) -> Self {
        Self::from_result(
            name,
            result.map(|result| {
                result.map(|(middle, input)| Transition {
                    input: input.clone(),
                    middle,
                    lowered: Lowered::Plain(input),
                    evidence: None,
                })
            }),
        )
    }
    pub fn memory(source: &Function) -> Self {
        Self::from_result(
            "middle_memory",
            (|| {
                let (middle, evidence) = source.recover_memory_constants()?;
                if evidence.refined_loads == 0 {
                    return if let Some(reason) = evidence.unavailable_reason {
                        Err(Error::Memory(reason))
                    } else {
                        Ok(None)
                    };
                }
                source.validate_memory_recovery(&middle)?;
                Ok(Some(Transition {
                    input: source.lower()?,
                    lowered: Lowered::Plain(middle.lower()?),
                    middle,
                    evidence: Some(Evidence::Memory(evidence)),
                }))
            })(),
        )
    }
    pub fn saved(source: &Function) -> Self {
        Self::from_result(
            "middle_saved",
            (|| {
                let Some((middle, evidence)) = source.recover_saved_values()? else {
                    return Ok(None);
                };
                if evidence.annotated_reads == 0 {
                    return Ok(None);
                }
                source.validate_saved_recovery(&middle)?;
                let lowered = middle
                    .lower_saved_values()?
                    .ok_or(Error::Invalid("missing saved lowering"))?;
                if lowered.source_registers() != source.lower()?.register_count() {
                    return Err(Error::Invalid("saved lowering source register count"));
                }
                Ok(Some(Transition {
                    input: source.lower()?,
                    middle,
                    lowered: Lowered::Saved(lowered),
                    evidence: Some(Evidence::Saved(evidence)),
                }))
            })(),
        )
    }
    fn from_result(name: &'static str, result: Result<Option<Transition>, Error>) -> Self {
        // A bounded MIR dump is part of the retained transition. Classify its
        // resource limit here, so other stage and native/C checks still run.
        let result = result.and_then(|t| {
            let text = t
                .as_ref()
                .filter(|t| t.evidence.is_some())
                .map(|t| t.middle.to_text())
                .transpose()?;
            Ok((t, text))
        });
        let (status, transition, failure, middle_text) = match result {
            Ok((Some(t), text)) => ("passed", Some(t), None, text),
            Ok((None, _)) => ("not_applied", None, None, None),
            Err(
                e @ (Error::Limit(_)
                | Error::Ssa(nirvana::ssa::SsaError::Unavailable(_))
                | Error::Memory(_)),
            ) => ("unavailable", None, Some(e.to_string()), None),
            Err(e) => ("rejected", None, Some(e.to_string()), None),
        };
        Self {
            name,
            status,
            transition,
            failure,
            observations: 0,
            records: String::new(),
            middle_text,
        }
    }
    pub fn comparisons(&self) -> &'static [&'static str] {
        if self.name == "middle_saved" {
            &["direct_middle", "saved_zero", "saved_ones"]
        } else {
            &["direct_middle", "lowered"]
        }
    }
    pub fn cost(&self) -> usize {
        if self.status == "passed" {
            self.comparisons().len()
        } else {
            0
        }
    }
    pub fn exhaust(&mut self) {
        if self.status == "passed" {
            self.status = "budget_exhausted";
        }
    }
    fn record(
        &mut self,
        kind: &str,
        actual: Result<RunReport, String>,
        expected: &RunReport,
        input: &[u64],
        budget: usize,
        case: usize,
    ) {
        let actual = match actual {
            Ok(actual) => actual,
            Err(error) => {
                self.status = "rejected";
                self.failure = Some(error);
                return;
            }
        };
        if matches!(self.name, "middle_memory" | "middle_saved") {
            let Some(record) = records::middle_pair(case, budget, kind, input, expected, &actual)
            else {
                self.status = "rejected";
                self.failure = Some("MIR observer requires flat memory".into());
                return;
            };
            if record.len() > records::MAX_LINE_BYTES
                || self.records.len().saturating_add(record.len()) > records::MAX_BYTES
            {
                self.status = "budget_exhausted";
                self.failure = Some("MIR state-pair record budget exceeded".into());
                return;
            }
            self.records.push_str(&record);
        }
        self.observations += 1;
        if actual != *expected {
            self.status = "counterexample";
            self.failure = Some(format!(
                "{kind}, case={case}, input={input:?}, budget={budget}\nexpected={expected:?}\nactual={actual:?}\n"
            ));
        }
    }
    pub fn check(
        &mut self,
        input: &[u64],
        ram: &[u8],
        budget: usize,
        case: usize,
        expected: &RunReport,
    ) {
        if self.status != "passed" {
            return;
        }
        let Some(t) = &self.transition else { return };
        let mut runs = vec![(
            "direct_middle",
            t.middle
                .run_with_memory(input, super::super::BASE, ram, budget)
                .map_err(|e| e.to_string()),
        )];
        match &t.lowered {
            Lowered::Plain(low) => runs.push((
                "lowered",
                low.run_with_memory(input, super::super::BASE, ram, budget)
                    .map_err(|e| e.to_string()),
            )),
            Lowered::Saved(low) => {
                for (kind, value) in [("saved_zero", 0), ("saved_ones", u64::MAX)] {
                    let mut extended = input.to_vec();
                    extended.resize(low.program().register_count(), value);
                    runs.push((
                        kind,
                        low.program()
                            .run_with_memory(&extended, super::super::BASE, ram, budget)
                            .map_err(|e| e.to_string())
                            .and_then(|r| low.project_report(r).map_err(|e| e.to_string())),
                    ));
                }
            }
        }
        for (kind, actual) in runs {
            self.record(kind, actual, expected, input, budget, case);
            if self.status != "passed" {
                break;
            }
        }
    }
    pub fn json(&self, out: &std::path::Path) -> std::io::Result<String> {
        let witness = if let Some(failure) = &self.failure {
            let name = format!("{}.witness.txt", self.name);
            std::fs::write(out.join(&name), failure)?;
            format!("\"{name}\"")
        } else {
            "null".into()
        };
        let transition = match self
            .transition
            .as_ref()
            .and_then(|t| t.evidence.as_ref().map(|e| (t, e)))
        {
            Some((t, evidence)) => {
                let low = match &t.lowered {
                    Lowered::Plain(p) => p,
                    Lowered::Saved(p) => p.program(),
                };
                for (suffix, program) in [("input.ir.txt", &t.input), ("lowered.ir.txt", low)] {
                    std::fs::write(
                        out.join(format!("{}.{suffix}", self.name)),
                        format!(
                            "entry={} registers={}\n{:#?}\n",
                            program.cfg().block(program.cfg().entry()).start,
                            program.register_count(),
                            program.instructions()
                        ),
                    )?;
                }
                std::fs::write(
                    out.join(format!("{}.mir.txt", self.name)),
                    self.middle_text
                        .as_deref()
                        .expect("retained MIR transition text"),
                )?;
                std::fs::write(
                    out.join(format!("{}.states.jsonl", self.name)),
                    &self.records,
                )?;
                let facts = match evidence {
                    Evidence::Memory(e) => format!(
                        "{{\"loads\":{},\"proved_loads\":{},\"refined_loads\":{},\"analysis_complete\":{}}}",
                        e.loads,
                        e.proved_loads,
                        e.refined_loads,
                        e.unavailable_reason.is_none()
                    ),
                    Evidence::Saved(e) => format!(
                        "{{\"annotated_reads\":{},\"phi_values\":{},\"merged_snapshots\":{},\"proved_loads\":{},\"snapshot_values\":{},\"replaced_reads\":{}}}",
                        e.annotated_reads,
                        e.phi_values,
                        e.merged_snapshots,
                        e.memory.proved_loads,
                        e.memory.snapshot_values,
                        e.memory.replaced_reads
                    ),
                };
                format!(
                    "{{\"model\":\"middle-memory-transition-v1\",\"source_registers\":{},\"lowered_registers\":{},\"input_ir\":\"{}.input.ir.txt\",\"lowered_ir\":\"{}.lowered.ir.txt\",\"middle_ir\":\"{}.mir.txt\",\"facts\":{facts},\"state_pairs\":{{\"model\":\"middle-state-pairs-v1\",\"file\":\"{}.states.jsonl\"}}}}",
                    t.input.register_count(),
                    low.register_count(),
                    self.name,
                    self.name,
                    self.name,
                    self.name
                )
            }
            None => "null".into(),
        };
        Ok(format!(
            "{{\"name\":\"{}\",\"status\":\"{}\",\"observations\":{},\"witness\":{witness},\"comparisons\":{:?},\"transition\":{transition}}}",
            self.name,
            self.status,
            self.observations,
            self.comparisons()
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nirvana::ir::{Assignment, Control, Expr, IrInstruction, Place, Reg, Width};
    #[test]
    fn a_corrupt_lowering_retains_a_full_state_counterexample() {
        let make = |value| {
            Program::new(
                0,
                1,
                vec![IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(value),
                }],
            )
            .unwrap()
        };
        let source = make(Expr::Register(Reg(0)));
        let middle = Function::from_low(&source).unwrap();
        let mut stage = Stage::plain("low_middle", Ok(Some((middle, make(Expr::Const(0))))));
        let expected = source
            .run_with_memory(&[42], super::super::super::BASE, &[], 2)
            .unwrap();
        stage.check(&[42], &[], 2, 0, &expected);
        assert_eq!(stage.status, "counterexample");
        assert!(stage.failure.unwrap().contains("lowered"));
        assert_eq!(stage.observations, 2);
    }
    fn fixture(saved: bool) -> Program {
        let r = |n| Expr::Register(Reg(n));
        let c = Expr::Const;
        let at = |n| Expr::binary(nirvana::ir::BinaryOp::Add, r(7), c(n));
        let set = |n, value| Assignment {
            destination: Place::Register(Reg(n)),
            value,
        };
        let store = |n, width, value| Assignment {
            destination: Place::Memory {
                address: at(n),
                width,
            },
            value,
        };
        let instructions = if saved {
            vec![
                vec![set(0, Expr::load(r(7), Width::U64))],
                vec![store(16, Width::U64, r(0)), set(0, c(0))],
                vec![set(2, Expr::load(at(19), Width::U16))],
            ]
        } else {
            vec![
                vec![store(0, Width::U8, c(3))],
                vec![set(2, Expr::load(r(7), Width::U8))],
            ]
        };
        let len = instructions.len();
        Program::new(
            0,
            32,
            instructions
                .into_iter()
                .enumerate()
                .map(|(i, assignments)| IrInstruction {
                    address: i as u64,
                    size: 1,
                    assignments,
                    control: if i + 1 == len {
                        Control::Return(r(2))
                    } else {
                        Control::Next
                    },
                })
                .collect(),
        )
        .unwrap()
    }
    #[test]
    fn memory_and_saved_transitions_keep_full_original_state_faults_and_prefixes() {
        for saved in [false, true] {
            let source = fixture(saved);
            let middle = Function::from_low(&source).unwrap();
            for pointer in [4224, 4592, u64::MAX] {
                let mut stage = if saved {
                    Stage::saved(&middle)
                } else {
                    Stage::memory(&middle)
                };
                assert_eq!(stage.status, "passed", "{:?}", stage.failure);
                let mut input = vec![0; 32];
                input[7] = pointer;
                for budget in 0..=4 {
                    let expected = source
                        .run_with_memory(&input, super::super::super::BASE, &[0xa5; 512], budget)
                        .unwrap();
                    stage.check(&input, &[0xa5; 512], budget, 0, &expected);
                }
                assert_eq!(stage.status, "passed", "{:?}", stage.failure);
                assert_eq!(stage.observations, if saved { 15 } else { 10 });
            }
        }
    }
    #[test]
    fn corrupt_lowering_and_projected_original_registers_are_counterexamples() {
        let source = fixture(false);
        let middle = Function::from_low(&source).unwrap();
        let mut stage = Stage::memory(&middle);
        let mut input = vec![0; 32];
        input[7] = 4224;
        let expected = source
            .run_with_memory(&input, super::super::super::BASE, &[0xa5; 512], 4)
            .unwrap();
        let mut actual = expected.clone();
        actual.state.registers[0] ^= 1;
        stage.record("lowered", Ok(actual), &expected, &input, 4, 0);
        assert_eq!(stage.status, "counterexample");
        assert!(stage.failure.unwrap().contains("lowered"));
    }
}
