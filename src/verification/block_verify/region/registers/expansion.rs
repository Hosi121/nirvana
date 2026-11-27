//! Restore a compact namespace, reserving fresh slots for new local registers.
use super::*;
use crate::model::ir::renaming::{self, Unmapped};
#[cfg(test)]
mod tests;

#[derive(Clone, Debug)]
pub struct Expanded {
    dense: Program,
    program: Program,
    registers: Vec<Reg>,
    original_count: usize,
    original_names: Vec<Reg>,
}
impl Expanded {
    pub fn source(&self) -> &Program {
        &self.dense
    }
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn registers(&self) -> &[Reg] {
        &self.registers
    }
    pub fn project_input(&self, expanded: &[u64]) -> Result<Vec<u64>, Error> {
        if expanded.len() != self.program.register_count() {
            return Err(Error::BoundaryMapping);
        }
        Ok(self.registers.iter().map(|r| expanded[r.0]).collect())
    }
    pub fn extend_input(&self, original: &[u64], fresh: u64) -> Result<Vec<u64>, Error> {
        if original.len() != self.original_count {
            return Err(Error::BoundaryMapping);
        }
        let mut values = original.to_vec();
        values.resize(self.program.register_count(), fresh);
        Ok(values)
    }
    /// Independently check the complete injective mapping and paired syntax.
    pub fn validate(&self) -> Result<(), Error> {
        shape::bounded_source(&self.dense, MAX_REGISTERS)?;
        if self.original_count > MAX_SOURCE_REGISTERS
            || self.original_names.len() > self.dense.register_count()
            || self.registers.len() != self.dense.register_count()
            || self.original_names.windows(2).any(|r| r[0].0 >= r[1].0)
            || self
                .original_names
                .iter()
                .any(|r| r.0 >= self.original_count)
        {
            return Err(Error::BoundaryMapping);
        }
        let extra = self.dense.register_count() - self.original_names.len();
        let count = self
            .original_count
            .checked_add(extra)
            .filter(|n| *n <= MAX_SOURCE_REGISTERS)
            .ok_or(Error::Limit)?;
        for (n, &r) in self.registers.iter().enumerate() {
            let expected = if let Some(&old) = self.original_names.get(n) {
                old
            } else {
                Reg(self.original_count + n - self.original_names.len())
            };
            if r != expected {
                return Err(Error::BoundaryMapping);
            }
        }
        let names = self
            .registers
            .iter()
            .enumerate()
            .map(|(n, &r)| (n, r))
            .collect();
        if !renaming::validate(&self.dense, &self.program, count, &names, Unmapped::Reject) {
            return Err(Error::BoundaryMapping);
        }
        Ok(())
    }
}
impl Compact {
    /// Reverse the checked compact mapping for a bounded candidate. Registers
    /// added by the candidate get distinct slots after the original namespace;
    /// input parameter IDs keep their original meaning in emitted C metadata.
    pub fn expand_candidate(&self, candidate: &Program) -> Result<Expanded, Error> {
        self.validate()?;
        shape::bounded_source(candidate, MAX_REGISTERS)?;
        let extra = candidate
            .register_count()
            .checked_sub(self.registers.len())
            .ok_or(Error::BoundaryMapping)?;
        let count = self
            .source
            .register_count()
            .checked_add(extra)
            .filter(|n| *n <= MAX_SOURCE_REGISTERS)
            .ok_or(Error::Limit)?;
        let mut registers = self.registers.clone();
        registers.extend((self.source.register_count()..count).map(Reg));
        let names = registers.iter().enumerate().map(|(n, &r)| (n, r)).collect();
        let program = renaming::relabel(candidate, count, &names, Unmapped::Reject)
            .ok_or(Error::BoundaryMapping)?;
        let expanded = Expanded {
            dense: candidate.clone(),
            program,
            registers,
            original_count: self.source.register_count(),
            original_names: self.registers.clone(),
        };
        expanded.validate()?;
        Ok(expanded)
    }
}
