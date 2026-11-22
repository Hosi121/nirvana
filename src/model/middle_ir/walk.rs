//! Traverse scoped MIR values without expanding shared pure subexpressions.
use super::*;

pub(super) fn visit(
    function: &Function,
    mut visit: impl FnMut(&Binding) -> Result<(), Error>,
) -> Result<(), Error> {
    let mut regions = Vec::new();
    for block in &function.blocks {
        for step in &block.steps {
            for statement in &step.statements {
                match statement {
                    Statement::WriteStorage { value, .. } => regions.push(value),
                    Statement::Store { address, value, .. } => {
                        regions.extend([address, value]);
                    }
                }
            }
        }
        match &block.terminator {
            Terminator::Branch { condition, .. } | Terminator::Return(condition) => {
                regions.push(condition)
            }
            _ => {}
        }
    }
    let mut budget = ssa::Budget::new();
    while let Some(region) = regions.pop() {
        budget
            .spend(region.bindings.len() + 1)
            .map_err(Error::Ssa)?;
        for binding in &region.bindings {
            visit(binding)?;
            if let Operation::Select {
                taken, not_taken, ..
            } = &binding.operation
            {
                regions.extend([taken, not_taken]);
            }
        }
    }
    Ok(())
}

pub(super) fn visit_mut(function: &mut Function, mut visit: impl FnMut(&mut Binding)) {
    let mut regions = Vec::new();
    for block in &mut function.blocks {
        for step in &mut block.steps {
            for statement in &mut step.statements {
                match statement {
                    Statement::WriteStorage { value, .. } => regions.push(value),
                    Statement::Store { address, value, .. } => regions.extend([address, value]),
                }
            }
        }
        match &mut block.terminator {
            Terminator::Branch { condition, .. } | Terminator::Return(condition) => {
                regions.push(condition)
            }
            _ => {}
        }
    }
    while let Some(region) = regions.pop() {
        for binding in &mut region.bindings {
            visit(binding);
            if let Operation::Select {
                taken, not_taken, ..
            } = &mut binding.operation
            {
                regions.extend([taken, not_taken]);
            }
        }
    }
}
