//! Bounded branch-local alternatives after both uniform placement policies fail.
//! A nearer forward join can distribute a later tail among too many arms; keeping
//! its post-dominator while using forward joins elsewhere can avoid that growth.

use super::*;

const MAX_CANDIDATES: usize = 8;

#[derive(Clone, Copy, Eq, PartialEq)]
struct Choice {
    branch: BlockId,
    join: Option<BlockId>,
}

#[derive(Default)]
pub(super) struct JoinPlan {
    chosen: Option<Choice>,
    candidates: Vec<Choice>,
}

impl JoinPlan {
    pub(super) fn select(
        &mut self,
        branch: BlockId,
        preferred: Option<BlockId>,
        strict: Option<BlockId>,
        stop: Option<BlockId>,
    ) -> Option<BlockId> {
        for join in [strict, stop] {
            // A real lexical stop is a boundary. An absent strict join is an
            // alternative only when both arms may finish independently.
            if join.is_none() && (stop.is_some() || strict.is_some()) {
                continue;
            }
            let choice = Choice { branch, join };
            if self.chosen == Some(choice) {
                return join;
            }
            if self.chosen.is_none()
                && join != preferred
                && self.candidates.len() < MAX_CANDIDATES
                && !self.candidates.contains(&choice)
            {
                self.candidates.push(choice);
            }
        }
        preferred
    }
}

impl StructuredFunction {
    pub(super) fn recover_with_join_candidates(
        program: &Program,
        copy_limit: usize,
        step_limit: usize,
        analysis: &ControlFlowAnalysis,
        postdom: Option<&PostDominators>,
    ) -> Option<Self> {
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
        let mut discovery = JoinPlan::default();
        let _ = Self::recover_using_plans(
            program,
            copy_limit,
            limit,
            analysis,
            postdom,
            true,
            BuildPlans {
                join: Some(&mut discovery),
                ..BuildPlans::default()
            },
        );
        for chosen in discovery.candidates {
            let mut plan = JoinPlan {
                chosen: Some(chosen),
                candidates: Vec::new(),
            };
            if let Ok(function) = Self::recover_using_plans(
                program,
                copy_limit,
                limit,
                analysis,
                postdom,
                true,
                BuildPlans {
                    join: Some(&mut plan),
                    ..BuildPlans::default()
                },
            ) {
                // recover_using_plans independently checks the completed AST
                // against the untouched source, including original Step PCs.
                return Some(function);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests;
