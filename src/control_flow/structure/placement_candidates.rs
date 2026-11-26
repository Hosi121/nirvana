//! Bounded placement alternatives after both uniform policies fail. Branch
//! joins retain the existing order; loop follows use the remaining attempts.
//! Abrupt returning or divergent exits need not share a single post-dominator.

use super::*;

const MAX_CANDIDATES: usize = 8;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Choice {
    Join {
        branch: BlockId,
        join: Option<BlockId>,
    },
    Follow {
        header: BlockId,
        follow: BlockId,
    },
}

#[derive(Default)]
pub(super) struct PlacementPlan {
    chosen: Option<Choice>,
    joins: Vec<Choice>,
    follows: Vec<Choice>,
}

impl PlacementPlan {
    pub(super) fn branch_join(
        &mut self,
        branch: BlockId,
        preferred: Option<BlockId>,
        strict: Option<BlockId>,
        stop: Option<BlockId>,
    ) -> Option<BlockId> {
        for join in [strict, stop] {
            // An absent join is an alternative only when both arms may finish
            // independently. A real enclosing lexical stop stays a boundary.
            if join.is_none() && (stop.is_some() || strict.is_some()) {
                continue;
            }
            let choice = Choice::Join { branch, join };
            if self.chosen == Some(choice) {
                return join;
            }
            if self.chosen.is_none() && join != preferred {
                record(&mut self.joins, choice);
            }
        }
        preferred
    }

    pub(super) fn loop_follow(
        &mut self,
        header: BlockId,
        exits: &BTreeSet<BlockId>,
        contexts: &[LoopContext],
        normal: Result<Option<BlockId>, StructureError>,
    ) -> Result<Option<BlockId>, StructureError> {
        for &follow in exits {
            // The candidate belongs to this natural loop's direct exits and
            // to the active lexical scope, not to an ancestor transfer.
            if contexts
                .last()
                .is_some_and(|parent| !parent.body.contains(&follow))
                || Builder::boundary(follow, contexts).is_some()
            {
                continue;
            }
            let choice = Choice::Follow { header, follow };
            if self.chosen == Some(choice) {
                return Ok(Some(follow));
            }
            if self.chosen.is_none() && normal.as_ref().ok().copied().flatten() != Some(follow) {
                record(&mut self.follows, choice);
            }
        }
        normal
    }
}

fn record(choices: &mut Vec<Choice>, choice: Choice) {
    if choices.len() < MAX_CANDIDATES && !choices.contains(&choice) {
        choices.push(choice);
    }
}

impl StructuredFunction {
    pub(super) fn recover_with_placement_candidates<T>(
        program: &Program,
        copy_limit: usize,
        step_limit: usize,
        analysis: &ControlFlowAnalysis,
        postdom: Option<&PostDominators>,
        mut accept: impl FnMut(Self) -> Option<T>,
    ) -> Option<T> {
        if program.cfg().blocks().len() > 128
            || program.instructions().len() > 1024
            || program.register_count() > 4096
        {
            return None;
        }
        let steps = follow_candidates::bounded_steps(program, analysis.reachable())?;
        let limit = step_limit
            .min(steps.saturating_mul(copy_limit.min(4)))
            .min(8192);
        let mut discovery = PlacementPlan::default();
        let _ = Self::recover_using_plans(
            program,
            copy_limit,
            limit,
            analysis,
            postdom,
            true,
            BuildPlans {
                placement: Some(&mut discovery),
                ..BuildPlans::default()
            },
        );
        // Preserve every earlier branch candidate and its order. Loop follows
        // share the same total eight-attempt limit, rather than adding a pass.
        for chosen in discovery
            .joins
            .into_iter()
            .chain(discovery.follows)
            .take(MAX_CANDIDATES)
        {
            let mut plan = PlacementPlan {
                chosen: Some(chosen),
                ..PlacementPlan::default()
            };
            if let Ok(function) = Self::recover_using_plans(
                program,
                copy_limit,
                limit,
                analysis,
                postdom,
                true,
                BuildPlans {
                    placement: Some(&mut plan),
                    ..BuildPlans::default()
                },
            ) && let Some(accepted) = accept(function)
            {
                // The completed AST is independently checked against the
                // untouched source, including original PCs and ordered effects.
                return Some(accepted);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests;
