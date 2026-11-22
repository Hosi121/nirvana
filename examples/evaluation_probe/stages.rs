//! Architecture observations are separate from the fixed native/C ABI profile.
//! Entry-prefix comparisons retain every register, RAM byte, PC, trace and fault.
use nirvana::{
    ir::{Program, RunReport},
    middle_ir::Function,
    readable::ReadableC,
};
use std::collections::BTreeSet;

struct Stage {
    name: &'static str,
    status: &'static str,
    middle: Option<(Function, Program)>,
    observations: usize,
    failure: Option<String>,
}
impl Stage {
    fn check(&mut self, input: &[u64], ram: &[u8], budget: usize, expected: &RunReport) {
        if self.status != "passed" {
            return;
        }
        let Some((middle, low)) = &self.middle else {
            return;
        };
        for (kind, actual) in [
            (
                "direct_middle",
                middle
                    .run_with_memory(input, super::BASE, ram, budget)
                    .map_err(|e| e.to_string()),
            ),
            (
                "lowered",
                low.run_with_memory(input, super::BASE, ram, budget)
                    .map_err(|e| e.to_string()),
            ),
        ] {
            self.observations += 1;
            if actual.as_ref().ok() != Some(expected) {
                self.status = "counterexample";
                self.failure = Some(format!(
                    "{kind}, input={input:?}, budget={budget}\nexpected={expected:?}\nactual={actual:?}\n"
                ));
                break;
            }
        }
    }
}
pub(super) struct Stages {
    stages: Vec<Stage>,
    budgets: Vec<usize>,
    transfers: BTreeSet<(u64, u64)>,
    observed: BTreeSet<(u64, u64)>,
    steps: BTreeSet<u64>,
    source_steps: usize,
    work: usize,
}
impl Stages {
    pub fn new(source: &Program, limit: usize) -> Self {
        let base = Function::from_low(source).and_then(|middle| Ok((middle.lower()?, middle)));
        let mut stages = Vec::new();
        let mut add =
            |name, result: Result<Option<(Function, Program)>, nirvana::middle_ir::Error>| {
                let (status, middle, failure) = match result {
                    Ok(Some(pair)) => ("passed", Some(pair), None),
                    Ok(None) => ("not_applied", None, None),
                    Err(
                        error @ (nirvana::middle_ir::Error::Limit(_)
                        | nirvana::middle_ir::Error::Ssa(
                            nirvana::ssa::SsaError::Unavailable(_),
                        )
                        | nirvana::middle_ir::Error::Memory(_)),
                    ) => ("unavailable", None, Some(error.to_string())),
                    Err(error) => ("rejected", None, Some(error.to_string())),
                };
                stages.push(Stage {
                    name,
                    status,
                    middle,
                    observations: 0,
                    failure,
                });
            };
        match base {
            Ok((low, middle))
                if low.instructions() == source.instructions()
                    && low.register_count() == source.register_count() =>
            {
                let predicates = middle.recover_predicates().and_then(|result| {
                    result
                        .map(|(m, _)| m.lower().map(|low| (m, low)))
                        .transpose()
                });
                add("low_middle", Ok(Some((middle, low))));
                add("middle_predicates", predicates);
            }
            Err(error) => {
                add("low_middle", Err(error));
                add("middle_predicates", Ok(None));
            }
            Ok(_) => {
                add(
                    "low_middle",
                    Err(nirvana::middle_ir::Error::Invalid("MIR reconstruction")),
                );
                add("middle_predicates", Ok(None));
            }
        }
        let mut budgets: Vec<_> = [0, 1, 2, 4, 8, 16, 32, 64, 128, limit]
            .into_iter()
            .filter(|n| *n <= limit)
            .collect();
        budgets.sort_unstable();
        budgets.dedup();
        let transfers = source
            .cfg()
            .reachable_blocks()
            .iter()
            .flat_map(|id| {
                let block = source.cfg().block(*id);
                let from = source.instructions()[block.instructions.end - 1].address;
                block
                    .successors
                    .iter()
                    .filter_map(move |edge| match edge.target {
                        nirvana::cfg::Target::Block(to) => {
                            Some((from, source.cfg().block(to).start))
                        }
                        _ => None,
                    })
            })
            .collect();
        Self {
            stages,
            budgets,
            transfers,
            observed: BTreeSet::new(),
            steps: BTreeSet::new(),
            source_steps: source.instructions().len(),
            work: 0,
        }
    }
    pub fn observe(&mut self, source: &Program, input: &[u64], ram: &[u8], complete: &RunReport) {
        self.steps.extend(&complete.state.trace);
        self.observed.extend(
            complete
                .state
                .trace
                .windows(2)
                .map(|p| (p[0], p[1]))
                .filter(|e| self.transfers.contains(e)),
        );
        for &budget in &self.budgets {
            let active = self.stages.iter().filter(|s| s.status == "passed").count();
            if active == 0 {
                break;
            }
            if self
                .work
                .saturating_add(budget.saturating_mul(1 + active * 2))
                > 8_000_000
            {
                for stage in &mut self.stages {
                    if stage.status == "passed" {
                        stage.status = "budget_exhausted";
                    }
                }
                break;
            }
            self.work += budget * (1 + active * 2);
            let expected = source
                .run_with_memory(input, super::BASE, ram, budget)
                .expect("same validated execution inputs");
            for stage in &mut self.stages {
                stage.check(input, ram, budget, &expected);
            }
        }
    }
    pub fn json(&self, output: &ReadableC, out: &std::path::Path) -> std::io::Result<String> {
        let mut stages = Vec::new();
        for stage in &self.stages {
            let witness = if let Some(failure) = &stage.failure {
                let name = format!("{}.witness.txt", stage.name);
                std::fs::write(out.join(&name), failure)?;
                format!("\"{name}\"")
            } else {
                "null".into()
            };
            stages.push(format!(
                "{{\"name\":\"{}\",\"status\":\"{}\",\"observations\":{},\"witness\":{witness}}}",
                stage.name, stage.status, stage.observations
            ));
        }
        let predicates = output.predicates.map_or("null".into(), |e| format!("{{\"pruned_branches\":{},\"constant_assignments\":{},\"blocks_before\":{},\"blocks_after\":{}}}", e.pruned_branches,e.constant_assignments,e.blocks_before,e.blocks_after));
        let continuations = output.continuations.map_or("null".into(), |e| {
            format!(
                "{{\"model\":\"{}\",\"removed_conditions\":{},\"shared_fragments\":{},\"compared_graph_nodes\":{}}}",
                nirvana::readable::CONTINUATION_MODEL_ID,
                e.removed_conditions,
                e.shared_fragments,
                e.compared_graph_nodes
            )
        });
        let status = if self.stages.iter().any(|s| s.status == "counterexample") {
            "counterexample"
        } else if self.stages.iter().any(|s| s.status == "rejected") {
            "rejected"
        } else if self
            .stages
            .iter()
            .any(|s| matches!(s.status, "unavailable" | "budget_exhausted"))
        {
            "inconclusive"
        } else {
            "passed"
        };
        let unobserved = self
            .transfers
            .difference(&self.observed)
            .map(|(a, b)| format!("[{a},{b}]"))
            .collect::<Vec<_>>()
            .join(",");
        let parameter_registers: Vec<_> = output.parameters.iter().map(|reg| reg.0).collect();
        Ok(format!(
            "{{\"schema\":\"nirvana-evaluation-stages-v1\",\"contract\":\"nirvana-entry-full-state-v1\",\"status\":\"{status}\",\"prefix_budgets\":{:?},\"execution\":[{}],\"selected_c\":{{\"predicates\":{predicates},\"continuations\":{continuations},\"parameter_registers\":{parameter_registers:?},\"input_structure_checked\":{},\"display_structure_checked\":{},\"saved_value_rounds\":{},\"fallback_goto\":{}}},\"low_coverage\":{{\"steps_started\":{},\"syntactic_steps\":{},\"transfers_observed\":{},\"syntactic_transfers\":{},\"unobserved_transfers\":[{unobserved}]}}}}",
            self.budgets,
            stages.join(","),
            output.structure_evidence.is_some(),
            output.display_structure_evidence.is_some(),
            output.memory_value_rounds.len(),
            output.fallback_reason.is_some(),
            self.steps.len(),
            self.source_steps,
            self.observed.len(),
            self.transfers.len()
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nirvana::ir::{Control, Expr, IrInstruction, Reg};
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
        let mut stage = Stage {
            name: "bad",
            status: "passed",
            middle: Some((middle, make(Expr::Const(0)))),
            observations: 0,
            failure: None,
        };
        let expected = source
            .run_with_memory(&[42], super::super::BASE, &[], 2)
            .unwrap();
        stage.check(&[42], &[], 2, &expected);
        assert_eq!(stage.status, "counterexample");
        assert!(stage.failure.unwrap().contains("lowered"));
        assert_eq!(stage.observations, 2);
    }
}
