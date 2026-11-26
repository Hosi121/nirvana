//! Readable-only placement candidates for nested loops with abrupt exits.
//! A direct exit in the active parent can follow the inner tree even when
//! other exits leave through ancestor headers/follows. The unchanged source
//! correspondence checker, rather than post-dominance, accepts each placement.

use super::*;
use crate::model::ir::Place;

const MAX_CANDIDATES: usize = 8;
const MAX_SYNTAX: usize = 65_536;
const MAX_DEPTH: usize = 128;

#[derive(Default)]
pub(super) struct FollowPlan {
    chosen: Option<(BlockId, BlockId)>,
    candidates: Vec<(BlockId, BlockId)>,
}

impl FollowPlan {
    pub(super) fn select(
        &mut self,
        header: BlockId,
        exits: &BTreeSet<BlockId>,
        contexts: &[LoopContext],
        normal: Result<Option<BlockId>, StructureError>,
    ) -> Result<Option<BlockId>, StructureError> {
        let Some(parent) = contexts.last() else {
            return normal;
        };
        let eligible = |exit: BlockId| {
            parent.body.contains(&exit) && Builder::boundary(exit, contexts).is_none()
        };
        if let Some((chosen_header, follow)) = self.chosen {
            // An override is local to one natural loop. Check its actual
            // active context again instead of trusting the discovery pass.
            if chosen_header == header && exits.contains(&follow) && eligible(follow) {
                return Ok(Some(follow));
            }
        } else {
            for &follow in exits {
                let candidate = (header, follow);
                if self.candidates.len() >= MAX_CANDIDATES {
                    break;
                }
                if eligible(follow)
                    && normal.as_ref().ok().copied().flatten() != Some(follow)
                    && !self.candidates.contains(&candidate)
                {
                    self.candidates.push(candidate);
                }
            }
        }
        normal
    }
}

impl StructuredFunction {
    /// Optional readable placement search. The public recovery policy and its
    /// errors remain the baseline; module/core callers do not use this path.
    pub(crate) fn recover_for_readable(program: &Program) -> Result<Self, StructureError> {
        let baseline = Self::recover(program);
        if matches!(&baseline, Ok(function) if function.stats.extra_block_copies == 0) {
            return baseline;
        }
        let reachable = program.cfg().reachable_blocks();
        let Some(steps) = bounded_steps(program, &reachable) else {
            return baseline;
        };
        let analysis = ControlFlowAnalysis::compute(program.cfg()).expect("validated program CFG");
        if !analysis.is_reducible() || analysis.natural_loops().len() < 2 {
            return baseline;
        }
        let postdom = PostDominators::compute(program.cfg()).ok();
        let step_limit = steps * 2;
        let mut discovery = FollowPlan::default();
        // Record candidates in actual active scopes, including those reached
        // before an eventual copy/join failure. This build is not adopted.
        let _ = Self::recover_using_plans(
            program,
            2,
            step_limit,
            &analysis,
            postdom.as_ref(),
            true,
            BuildPlans {
                follow: Some(&mut discovery),
                ..BuildPlans::default()
            },
        );
        let mut selected = baseline;
        for chosen in discovery.candidates {
            let mut plan = FollowPlan {
                chosen: Some(chosen),
                candidates: Vec::new(),
            };
            let candidate = Self::recover_using_plans(
                program,
                2,
                step_limit,
                &analysis,
                postdom.as_ref(),
                true,
                BuildPlans {
                    follow: Some(&mut plan),
                    ..BuildPlans::default()
                },
            );
            selected = match (selected, candidate) {
                (Ok(old), Ok(new))
                    if new.stats.emitted_block_copies <= old.stats.emitted_block_copies
                        && new.evidence.compared_copies <= old.evidence.compared_copies
                        && (new.stats.emitted_block_copies < old.stats.emitted_block_copies
                            || new.evidence.compared_copies < old.evidence.compared_copies) =>
                {
                    Ok(new)
                }
                (Ok(old), _) => Ok(old),
                (Err(_), Ok(new)) => Ok(new),
                (Err(reason), Err(_)) => Err(reason),
            };
        }
        selected
    }
}

// Bound only the optional search's reachable input before cloning syntax or
// running more analysis. Unreachable instructions do not consume its budget.
pub(super) fn bounded_steps(program: &Program, reachable: &BTreeSet<BlockId>) -> Option<usize> {
    let mut remaining = MAX_SYNTAX;
    let mut steps = 0;
    for &id in reachable {
        for instruction in &program.instructions()[program.cfg().block(id).instructions.clone()] {
            remaining = remaining.checked_sub(1)?;
            steps += 1;
            for assignment in &instruction.assignments {
                remaining = remaining.checked_sub(1)?;
                if let Place::Memory { address, .. } = &assignment.destination {
                    bounded_expression(address, &mut remaining)?;
                }
                bounded_expression(&assignment.value, &mut remaining)?;
            }
            match &instruction.control {
                Control::Branch { condition, .. } | Control::Return(condition) => {
                    bounded_expression(condition, &mut remaining)?;
                }
                _ => {}
            }
        }
    }
    Some(steps)
}

fn bounded_expression(expression: &Expr, remaining: &mut usize) -> Option<()> {
    let mut pending = vec![(expression, 0)];
    while let Some((expression, depth)) = pending.pop() {
        if depth > MAX_DEPTH {
            return None;
        }
        *remaining = remaining.checked_sub(1)?;
        match expression {
            Expr::Unary(_, value) | Expr::Load { address: value, .. } => {
                pending.push((value, depth + 1));
            }
            Expr::Binary(_, left, right) => {
                pending.extend([(&**left, depth + 1), (&**right, depth + 1)]);
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([
                (&**condition, depth + 1),
                (&**taken, depth + 1),
                (&**not_taken, depth + 1),
            ]),
            Expr::Const(_) | Expr::Register(_) => {}
        }
    }
    Some(())
}

#[cfg(test)]
mod tests;
