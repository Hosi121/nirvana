//! Redistribute the readable frontend's existing total Step-copy allowance.
//!
//! Public recovery still permits two copies of each block. A CopyLimit failure
//! alone may retry with more copies concentrated in a short shared tail, while
//! retaining at most twice the reachable original instruction count overall.
//! The structurer checks every accepted tree against the actual input program.

use crate::control_flow::structure::{StructureError, StructuredFunction};
use crate::model::ir::{Control, Expr, Place, Program};

const MAX_LOCAL_COPIES: usize = 8;
const MAX_SYNTAX_ITEMS: usize = 65_536;
const MAX_EXPRESSION_DEPTH: usize = 128;

pub(super) fn recover(program: &Program) -> Result<StructuredFunction, StructureError> {
    let baseline = StructuredFunction::recover(program);
    if !matches!(&baseline, Err(StructureError::CopyLimit { limit: 2, .. })) {
        return baseline;
    }
    let Some(step_limit) = retry_step_limit(program) else {
        return baseline;
    };
    // Both local and total limits are enforced before a block is cloned. An
    // exhausted or structurally unavailable retry preserves the original error.
    StructuredFunction::recover_with_step_limit(program, MAX_LOCAL_COPIES, step_limit).or(baseline)
}

fn retry_step_limit(program: &Program) -> Option<usize> {
    let mut syntax = Syntax(MAX_SYNTAX_ITEMS);
    let mut steps = 0usize;
    for id in program.cfg().reachable_blocks() {
        let block = program.cfg().block(id);
        steps = steps.checked_add(block.instructions.len())?;
        for instruction in &program.instructions()[block.instructions.clone()] {
            syntax.spend()?;
            for assignment in &instruction.assignments {
                syntax.spend()?;
                if let Place::Memory { address, .. } = &assignment.destination {
                    syntax.expression(address)?;
                }
                syntax.expression(&assignment.value)?;
            }
            if let Control::Branch { condition, .. } | Control::Return(condition) =
                &instruction.control
            {
                syntax.expression(condition)?;
            }
        }
    }
    steps.checked_mul(2)
}

struct Syntax(usize);

impl Syntax {
    fn spend(&mut self) -> Option<()> {
        self.0 = self.0.checked_sub(1)?;
        Some(())
    }

    fn expression(&mut self, expression: &Expr) -> Option<()> {
        let mut pending = vec![(expression, 1usize)];
        while let Some((expression, depth)) = pending.pop() {
            self.spend()?;
            if depth > MAX_EXPRESSION_DEPTH {
                return None;
            }
            match expression {
                Expr::Const(_) | Expr::Register(_) => {}
                Expr::Unary(_, child) | Expr::Load { address: child, .. } => {
                    pending.push((child, depth + 1));
                }
                Expr::Binary(_, left, right) => {
                    pending.push((right, depth + 1));
                    pending.push((left, depth + 1));
                }
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => {
                    pending.push((not_taken, depth + 1));
                    pending.push((taken, depth + 1));
                    pending.push((condition, depth + 1));
                }
            }
        }
        Some(())
    }
}

#[cfg(test)]
mod tests;
