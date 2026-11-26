//! Checked alpha-renaming for sparse register namespaces before region queries.
//! Every instruction, effect and control expression stays in place. Registers
//! absent from all instructions retain their original input value on restore.
use super::{Error, MAX_REGISTERS, shape};
use crate::model::ir::{Control, Expr, IrInstruction, Place, Program, Reg};
use std::collections::BTreeSet;

mod check;
#[cfg(test)]
mod tests;

pub const MODEL_ID: &str = "checked-dense-register-projection-v1";
pub const MAX_SOURCE_REGISTERS: usize = 65_536;

#[derive(Clone, Debug)]
pub struct Compact {
    source: Program,
    program: Program,
    registers: Vec<Reg>,
}
impl Compact {
    pub fn program(&self) -> &Program {
        &self.program
    }
    /// Dense register index -> register in the original Program.
    pub fn registers(&self) -> &[Reg] {
        &self.registers
    }
    pub fn source(&self) -> &Program {
        &self.source
    }
    pub fn dense_register(&self, original: Reg) -> Option<Reg> {
        self.registers
            .binary_search_by_key(&original.0, |r| r.0)
            .ok()
            .map(Reg)
    }
    pub fn project_input(&self, original: &[u64]) -> Result<Vec<u64>, Error> {
        if original.len() != self.source.register_count() {
            return Err(Error::BoundaryMapping);
        }
        Ok(self.registers.iter().map(|r| original[r.0]).collect())
    }
    /// Restore all original registers, including unused slots, from an exact
    /// original input state. Every syntactic register write belongs to the map,
    /// so an unused slot retains its input value.
    pub fn restore_registers(&self, input: &[u64], dense: &[u64]) -> Result<Vec<u64>, Error> {
        if input.len() != self.source.register_count() || dense.len() != self.registers.len() {
            return Err(Error::BoundaryMapping);
        }
        let mut original = input.to_vec();
        for (&register, &value) in self.registers.iter().zip(dense) {
            original[register.0] = value;
        }
        Ok(original)
    }
    pub fn validate(&self) -> Result<(), Error> {
        check::validate(self)
    }
}

fn expressions(instruction: &IrInstruction) -> Vec<&Expr> {
    let mut roots = Vec::new();
    for assignment in &instruction.assignments {
        roots.push(&assignment.value);
        if let Place::Memory { address, .. } = &assignment.destination {
            roots.push(address);
        }
    }
    match &instruction.control {
        Control::Branch { condition, .. } => roots.push(condition),
        Control::Return(value) => roots.push(value),
        _ => {}
    }
    roots
}
fn used(program: &Program) -> BTreeSet<usize> {
    let mut used = BTreeSet::new();
    for instruction in program.instructions() {
        for assignment in &instruction.assignments {
            if let Place::Register(register) = assignment.destination {
                used.insert(register.0);
            }
        }
        let mut pending = expressions(instruction);
        while let Some(expression) = pending.pop() {
            match expression {
                Expr::Register(reg) => {
                    used.insert(reg.0);
                }
                Expr::Unary(_, value) | Expr::Load { address: value, .. } => pending.push(value),
                Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([&**condition, &**taken, &**not_taken]),
                Expr::Const(_) => {}
            }
        }
    }
    used
}
/// Reindex all syntactically read/written registers into a dense namespace.
/// Source instruction/expression bounds remain the region bounds, while the
/// source register space may be sparse. The emitted query retains its existing
/// 128-register limit. Closed cyclic sources are allowed for later extraction.
pub fn compact(source: &Program) -> Result<Compact, Error> {
    shape::bounded_source(source, MAX_SOURCE_REGISTERS)?;
    let registers: Vec<_> = used(source).into_iter().map(Reg).collect();
    if registers.len() > MAX_REGISTERS {
        return Err(Error::Limit);
    }
    build(source, registers)
}

/// Compare two Programs in one original register universe. The common map also
/// retains declared boundary registers that neither instruction stream uses.
/// This prevents unrelated dense indices from being treated as shared inputs.
#[derive(Clone, Debug)]
pub struct Comparison {
    before: Compact,
    after: Compact,
    shared: Vec<Reg>,
    outputs: Vec<Reg>,
}
impl Comparison {
    pub fn before(&self) -> &Compact {
        &self.before
    }
    pub fn after(&self) -> &Compact {
        &self.after
    }
    pub fn query(&self) -> Result<super::Query, Error> {
        super::query(
            self.before.program(),
            self.after.program(),
            &self.shared,
            &self.outputs,
        )
    }
}

pub fn compact_comparison(
    before: &Program,
    after: &Program,
    shared: &[Reg],
    outputs: &[Reg],
) -> Result<Comparison, Error> {
    shape::bounded_source(before, MAX_SOURCE_REGISTERS)?;
    shape::bounded_source(after, MAX_SOURCE_REGISTERS)?;
    if shared.len() > MAX_REGISTERS
        || outputs.len() > MAX_REGISTERS
        || before.register_count() != after.register_count()
        || shared
            .iter()
            .chain(outputs)
            .any(|r| r.0 >= before.register_count())
    {
        return Err(Error::BoundaryMapping);
    }
    let mut registers = used(before);
    registers.extend(used(after));
    registers.extend(shared.iter().chain(outputs).map(|r| r.0));
    if registers.len() > MAX_REGISTERS {
        return Err(Error::Limit);
    }
    let registers: Vec<_> = registers.into_iter().map(Reg).collect();
    let before = build(before, registers.clone())?;
    let after = build(after, registers)?;
    let mapped = |ids: &[Reg]| {
        ids.iter()
            .map(|&r| before.dense_register(r).ok_or(Error::BoundaryMapping))
            .collect::<Result<Vec<_>, _>>()
    };
    let shared = mapped(shared)?;
    let outputs = mapped(outputs)?;
    Ok(Comparison {
        before,
        after,
        shared,
        outputs,
    })
}

fn build(source: &Program, registers: Vec<Reg>) -> Result<Compact, Error> {
    let names = registers
        .iter()
        .enumerate()
        .map(|(n, r)| (r.0, Reg(n)))
        .collect();
    let program = crate::model::ir::renaming::relabel(
        source,
        registers.len(),
        &names,
        crate::model::ir::renaming::Unmapped::Reject,
    )
    .ok_or(Error::BoundaryMapping)?;
    let result = Compact {
        source: source.clone(),
        program,
        registers,
    };
    result.validate()?;
    Ok(result)
}
