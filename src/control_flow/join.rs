//! Bounded common-descendant search in the reducible CFG's forward DAG.
//! This proposes a placement; the independent structural checker decides
//! whether the resulting AST preserves the original control flow.

use std::collections::{BTreeSet, VecDeque};

use crate::control_flow::analysis::ControlFlowAnalysis;
use crate::control_flow::cfg::{BlockId, Cfg, Target};

pub(crate) struct ForwardDag {
    blocks: Vec<BlockId>,
    successors: Vec<Vec<BlockId>>,
    remaining_visits: usize,
}

impl ForwardDag {
    pub fn new(cfg: &Cfg, analysis: &ControlFlowAnalysis) -> Self {
        debug_assert!(analysis.is_reducible());
        let mut successors = vec![Vec::new(); cfg.blocks().len()];
        for &source in analysis.reachable() {
            for edge in &cfg.block(source).successors {
                let Target::Block(target) = edge.target else {
                    unreachable!("closed CFG")
                };
                // Only remove edges already identified by dominance as loop
                // backedges. The acyclicity test lives in the graph analysis.
                if !analysis.dominates(target, source)
                    && !successors[source.index()].contains(&target)
                {
                    successors[source.index()].push(target);
                }
            }
        }
        Self {
            blocks: cfg.blocks().iter().map(|block| block.id).collect(),
            successors,
            remaining_visits: 100_000,
        }
    }

    fn distances(
        &mut self,
        start: BlockId,
        stop: Option<BlockId>,
        scope: Option<&BTreeSet<BlockId>>,
    ) -> Option<Vec<Option<usize>>> {
        let mut distances = vec![None; self.successors.len()];
        let allowed = |id| scope.is_none_or(|scope| scope.contains(&id));
        if !allowed(start) {
            return Some(distances);
        }
        distances[start.index()] = Some(0usize);
        let mut pending = VecDeque::from([start]);
        while let Some(source) = pending.pop_front() {
            self.remaining_visits = self.remaining_visits.checked_sub(1)?;
            if Some(source) == stop {
                continue;
            }
            let distance = distances[source.index()].expect("visited") + 1;
            for &target in &self.successors[source.index()] {
                if allowed(target) && distances[target.index()].is_none() {
                    distances[target.index()] = Some(distance);
                    pending.push_back(target);
                }
            }
        }
        Some(distances)
    }

    /// A join may be reached by only some paths: other paths must transfer
    /// out. Do not look through the enclosing region stop or outside its loop.
    pub fn common_join(
        &mut self,
        left: BlockId,
        right: BlockId,
        stop: Option<BlockId>,
        scope: Option<&BTreeSet<BlockId>>,
    ) -> Option<BlockId> {
        let first = self.distances(left, stop, scope)?;
        let second = self.distances(right, stop, scope)?;
        self.blocks
            .iter()
            .filter_map(|&id| {
                let a = first[id.index()]?;
                let b = second[id.index()]?;
                Some(((a.max(b), a + b, id), id))
            })
            .min_by_key(|(distance, _)| *distance)
            .map(|(_, id)| id)
    }
}
