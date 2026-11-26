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
        allowed: &impl Fn(BlockId) -> bool,
    ) -> Option<Vec<Option<usize>>> {
        let mut distances = vec![None; self.successors.len()];
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
        self.common_join_all([left, right], stop, |id| {
            scope.is_none_or(|scope| scope.contains(&id))
        })
    }

    /// Intersect all descendant sets before choosing a placement. Folding
    /// pairwise nearest joins can discard a later common descendant.
    /// Every traversal consumes the same per-build visit budget.
    pub fn common_join_all(
        &mut self,
        starts: impl IntoIterator<Item = BlockId>,
        stop: Option<BlockId>,
        allowed: impl Fn(BlockId) -> bool,
    ) -> Option<BlockId> {
        let mut scores: Option<Vec<Option<(usize, usize)>>> = None;
        for start in starts {
            let distances = self.distances(start, stop, &allowed)?;
            if let Some(scores) = &mut scores {
                for (score, distance) in scores.iter_mut().zip(distances) {
                    *score = match (*score, distance) {
                        (Some((maximum, sum)), Some(distance)) => {
                            Some((maximum.max(distance), sum.checked_add(distance)?))
                        }
                        _ => None,
                    };
                }
            } else {
                scores = Some(
                    distances
                        .into_iter()
                        .map(|distance| distance.map(|distance| (distance, distance)))
                        .collect(),
                );
            }
        }
        self.blocks
            .iter()
            .zip(scores?)
            .filter_map(|(&id, score)| {
                let (maximum, sum) = score?;
                Some(((maximum, sum, id), id))
            })
            .min_by_key(|(distance, _)| *distance)
            .map(|(_, id)| id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::ir::{Control, Expr, IrInstruction, Program, Reg};

    fn branching_descendants() -> Program {
        let branch = |target| Control::Branch {
            condition: Expr::Register(Reg(0)),
            target,
        };
        Program::new(
            6,
            1,
            [
                branch(3),
                Control::Jump(4),
                branch(4),
                Control::Return(Expr::Const(0)),
                Control::Return(Expr::Const(0)),
                Control::Jump(4),
                branch(0),
                branch(2),
                Control::Jump(5),
            ]
            .into_iter()
            .enumerate()
            .map(|(address, control)| IrInstruction {
                address: address as u64,
                size: 1,
                assignments: vec![],
                control,
            })
            .collect(),
        )
        .unwrap()
    }

    #[test]
    fn all_exits_intersect_before_selecting_the_nearest_join() {
        let source = branching_descendants();
        let analysis = ControlFlowAnalysis::compute(source.cfg()).unwrap();
        let block = |address| source.cfg().block_at(address).unwrap();
        let mut dag = ForwardDag::new(source.cfg(), &analysis);
        let pair = dag.common_join(block(0), block(2), None, None).unwrap();
        assert_eq!(pair, block(3));
        assert_eq!(dag.common_join(pair, block(5), None, None), None);
        assert_eq!(
            dag.common_join_all([block(0), block(2), block(5)], None, |_| true),
            Some(block(4))
        );
    }

    #[test]
    fn all_exit_queries_respect_scope_stop_and_the_shared_visit_budget() {
        let source = branching_descendants();
        let analysis = ControlFlowAnalysis::compute(source.cfg()).unwrap();
        let block = |address| source.cfg().block_at(address).unwrap();
        let starts = [block(0), block(2), block(5)];
        let mut dag = ForwardDag::new(source.cfg(), &analysis);
        assert_eq!(dag.common_join_all(starts, None, |id| id != block(4)), None);
        assert_eq!(dag.common_join_all(starts, Some(block(1)), |_| true), None);
        dag.remaining_visits = 1;
        assert_eq!(dag.common_join_all(starts, None, |_| true), None);
        assert_eq!(dag.common_join(block(4), block(4), None, None), None);
    }
}
