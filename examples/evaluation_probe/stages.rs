//! Architecture observations are separate from the fixed native/C ABI profile.
//! Entry-prefix comparisons retain every register, RAM byte, PC, trace and fault.
use nirvana::{
    ir::{Program, RunReport},
    middle_ir::Function,
    readable::ReadableC,
};
use std::collections::BTreeSet;

#[path = "load_consumer_stage.rs"]
mod load_consumer;
#[path = "semantic_stage.rs"]
mod semantic;

#[path = "analysis_stage.rs"]
mod analysis;
#[path = "middle_stage.rs"]
mod middle;
#[path = "semantic_records.rs"]
mod records;
#[path = "selected_signed_storage_stage.rs"]
mod selected_signed_storage;
#[path = "selected_storage_stage.rs"]
mod selected_storage;
#[path = "storage_artifacts.rs"]
mod storage_artifacts;
use middle::Stage;

pub(super) struct Stages {
    stages: Vec<Stage>,
    semantic: semantic::Stage,
    load_consumer: load_consumer::Stage,
    analysis: analysis::Stage,
    selected_storage: selected_storage::Stage,
    selected_signed_storage: selected_signed_storage::Stage,
    original_registers: usize,
    budgets: Vec<usize>,
    transfers: BTreeSet<(u64, u64)>,
    observed: BTreeSet<(u64, u64)>,
    steps: BTreeSet<u64>,
    source_steps: usize,
    work: usize,
    cases: usize,
}
impl Stages {
    pub fn new(source: &Program, output: &ReadableC, limit: usize) -> Self {
        let base = Function::from_low(source).and_then(|middle| Ok((middle.lower()?, middle)));
        let mut stages = Vec::new();
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
                let memory = Stage::memory(&middle);
                let saved = Stage::saved(&middle);
                stages.push(Stage::plain("low_middle", Ok(Some((middle, low)))));
                stages.push(Stage::plain("middle_predicates", predicates));
                stages.push(memory);
                stages.push(saved);
            }
            result => {
                let error = match result {
                    Err(error) => error,
                    Ok(_) => nirvana::middle_ir::Error::Invalid("MIR reconstruction"),
                };
                stages.push(Stage::plain("low_middle", Err(error)));
                for name in ["middle_predicates", "middle_memory", "middle_saved"] {
                    stages.push(Stage::plain(
                        name,
                        Err(nirvana::middle_ir::Error::Memory(
                            "base MIR unavailable".into(),
                        )),
                    ));
                }
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
            semantic: semantic::Stage::new(source, output.semantic_lowering.clone()),
            load_consumer: load_consumer::Stage::new(output),
            analysis: analysis::Stage::new(source),
            selected_storage: selected_storage::Stage::new(output),
            selected_signed_storage: selected_signed_storage::Stage::new(output),
            original_registers: source.register_count(),
            budgets,
            transfers,
            observed: BTreeSet::new(),
            steps: BTreeSet::new(),
            source_steps: source.instructions().len(),
            work: 0,
            cases: 0,
        }
    }
    pub fn observe(&mut self, source: &Program, input: &[u64], ram: &[u8], complete: &RunReport) {
        let case = self.cases;
        self.cases += 1;
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
            let cost = 1
                + self.stages.iter().map(Stage::cost).sum::<usize>()
                + if self.semantic.status == "passed" {
                    4
                } else {
                    0
                };
            if cost == 1 {
                break;
            }
            if self.work.saturating_add(budget.saturating_mul(cost)) > 8_000_000 {
                for stage in &mut self.stages {
                    stage.exhaust();
                }
                if self.semantic.status == "passed" {
                    self.semantic.status = "budget_exhausted";
                }
                break;
            }
            self.work += budget * cost;
            let expected = source
                .run_with_memory(input, super::BASE, ram, budget)
                .expect("same validated execution inputs");
            for stage in &mut self.stages {
                stage.check(input, ram, budget, case, &expected);
            }
            self.semantic.check(input, ram, budget, case);
        }
        // This observer owns its work quota, preserving existing coverage
        // under the established eight-million-work budget.
        for &budget in &self.budgets {
            self.load_consumer.check(input, ram, budget, case);
        }
    }
    pub fn json(&self, output: &ReadableC, out: &std::path::Path) -> std::io::Result<String> {
        let mut stages = Vec::new();
        for stage in &self.stages {
            stages.push(stage.json(out)?);
        }
        stages.push(self.semantic.json(out)?);
        stages.push(self.load_consumer.json(out)?);
        let base_checks = self.analysis.json(out)?;
        let selected_check = self.selected_storage.json(out)?;
        let analysis_checks = format!(
            "{},{},{}]",
            base_checks.strip_suffix(']').expect("analysis JSON array"),
            selected_check,
            self.selected_signed_storage.json(out)?
        );
        let predicates = output.predicates.map_or("null".into(), |e| format!("{{\"pruned_branches\":{},\"constant_assignments\":{},\"blocks_before\":{},\"blocks_after\":{}}}", e.pruned_branches,e.constant_assignments,e.blocks_before,e.blocks_after));
        let continuations = output.continuations.map_or("null".into(), |e| {
            let order = e.store_order.map_or(String::new(), |o| format!(
                ",\"store_order\":{{\"prefix_nodes\":{},\"range_witnesses\":{},\"swapped_pairs\":{}}}",
                o.prefix_nodes, o.range_witnesses, o.swapped_pairs
            ));
            let effects = e.effect_order.map_or(String::new(), |o| format!(
                ",\"effect_order\":{{\"prefix_nodes\":{},\"range_witnesses\":{},\"store_pairs\":{},\"local_pairs\":{}}}",
                o.prefix_nodes, o.range_witnesses, o.store_pairs, o.local_pairs
            ));
            format!(
                "{{\"model\":\"{}\",\"removed_conditions\":{},\"shared_fragments\":{},\"compared_graph_nodes\":{}{order}{effects}}}",
                e.model(),
                e.removed_conditions,
                e.shared_fragments,
                e.compared_graph_nodes
            )
        });
        let statuses: Vec<_> = self
            .stages
            .iter()
            .map(|s| s.status)
            .chain(std::iter::once(self.semantic.status))
            .chain(std::iter::once(self.load_consumer.status))
            .chain(self.analysis.statuses())
            .chain(std::iter::once(self.selected_storage.status))
            .chain(std::iter::once(self.selected_signed_storage.status))
            .collect();
        let status = if statuses.contains(&"counterexample") {
            "counterexample"
        } else if statuses.contains(&"rejected") {
            "rejected"
        } else if statuses
            .iter()
            .any(|s| matches!(*s, "unavailable" | "budget_exhausted"))
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
            "{{\"schema\":\"nirvana-evaluation-stages-v9\",\"contract\":\"nirvana-stage-input-state-v9\",\"original_registers\":{},\"status\":\"{status}\",\"prefix_budgets\":{:?},\"execution\":[{}],\"analysis_checks\":{analysis_checks},\"selected_c\":{{\"predicates\":{predicates},\"continuations\":{continuations},\"parameter_registers\":{parameter_registers:?},\"input_structure_checked\":{},\"display_structure_checked\":{},\"saved_value_rounds\":{},\"fallback_goto\":{}}},\"low_coverage\":{{\"steps_started\":{},\"syntactic_steps\":{},\"transfers_observed\":{},\"syntactic_transfers\":{},\"unobserved_transfers\":[{unobserved}]}}}}",
            self.original_registers,
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
