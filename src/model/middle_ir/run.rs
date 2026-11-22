use super::*;
use crate::model::ir::{AccessKind, ExecutionError, Machine, MemoryFault, RunReport, Stop};
use std::collections::BTreeMap;

fn evaluate(region: &Region, function: &Function, machine: &Machine) -> Result<u64, MemoryFault> {
    let mut values = BTreeMap::<ValueId, u64>::new();
    for binding in &region.bindings {
        let value = match &binding.operation {
            Operation::Pure(Pure::Constant(n)) => *n,
            Operation::Pure(Pure::Unary(op, input)) => op.evaluate(values[input]),
            Operation::Pure(Pure::Binary(op, a, b)) => op.evaluate(values[a], values[b]),
            Operation::ReadStorage { storage, .. } | Operation::ReadSaved { storage, .. } => {
                machine.registers[function.storages[storage.0].0]
            }
            Operation::Load { address, width } => machine.load(values[address], *width)?,
            Operation::KnownLoad {
                address,
                width,
                value,
            } => {
                machine.load(values[address], *width)?;
                *value
            }
            Operation::Select {
                condition,
                taken,
                not_taken,
            } => evaluate(
                if values[condition] != 0 {
                    taken
                } else {
                    not_taken
                },
                function,
                machine,
            )?,
        };
        values.insert(binding.id, value);
    }
    Ok(values[&region.result])
}
impl Function {
    /// Execute MIR directly. Scalar operators and checked memory are shared
    /// trusted primitives; expression evaluation and control traversal are separate.
    pub fn run_with_memory(
        &self,
        input: &[u64],
        memory_base: u64,
        memory: &[u8],
        step_limit: usize,
    ) -> Result<RunReport, ExecutionError> {
        let mut machine =
            Machine::with_memory(self.storages.len(), input, memory_base, memory, step_limit)?;
        let mut address = self.entry;
        let result = (|| -> Result<u64, Stop> {
            loop {
                let index = self
                    .blocks
                    .binary_search_by_key(&address, |b| b.address)
                    .expect("validated block target");
                let block = &self.blocks[index];
                for step in &block.steps {
                    machine.step(step.address, &[])?;
                    for statement in &step.statements {
                        match statement {
                            Statement::WriteStorage { storage, value, .. } => {
                                let value = evaluate(value, self, &machine)?;
                                machine.registers[self.storages[storage.0].0] = value;
                            }
                            Statement::Store {
                                address,
                                width,
                                value,
                            } => {
                                let address = evaluate(address, self, &machine)?;
                                machine
                                    .checked_range(address, width.bytes(), AccessKind::Write)
                                    .ok_or(MemoryFault {
                                        access: AccessKind::Write,
                                        address,
                                        width: *width,
                                    })?;
                                let value = evaluate(value, self, &machine)?;
                                machine.store(address, *width, value)?;
                            }
                        }
                    }
                }
                address = match &block.terminator {
                    Terminator::Fallthrough(target) | Terminator::Jump(target) => *target,
                    Terminator::Branch {
                        condition,
                        taken,
                        not_taken,
                    } => {
                        if evaluate(condition, self, &machine)? != 0 {
                            *taken
                        } else {
                            *not_taken
                        }
                    }
                    Terminator::Return(value) => return Ok(evaluate(value, self, &machine)?),
                };
            }
        })();
        Ok(machine.finish(result))
    }
}
