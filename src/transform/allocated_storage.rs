//! Checked physical storage IR from an independently validated local allocation.
//!
//! Return, all RAM, first fault, PC, trace and instruction-budget observations
//! retain their meaning. Complete original register snapshots belong to the
//! original IR; multiple source values can reuse one physical slot here.
use crate::dataflow::allocation_verify::{self, AllocationError, AllocationEvidence};
use crate::model::ir::{
    Program, Reg,
    renaming::{self, Unmapped},
};
use std::collections::{BTreeMap, BTreeSet};

#[cfg(test)]
mod tests;

pub const MODEL_ID: &str = "checked-allocated-storage-ir-v1";
pub const MAX_REGISTERS: usize = 65_536;
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    Allocation(AllocationError),
    Limit,
    Correspondence,
    Input,
}
impl From<AllocationError> for Error {
    fn from(e: AllocationError) -> Self {
        Self::Allocation(e)
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "allocated storage: {self:?}")
    }
}
impl std::error::Error for Error {}

#[derive(Clone, Debug)]
pub struct Lowering {
    source: Program,
    program: Program,
    mapping: Vec<(Reg, usize)>,
    names: BTreeMap<usize, Reg>,
    evidence: AllocationEvidence,
}
impl Lowering {
    pub fn source(&self) -> &Program {
        &self.source
    }
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn mapping(&self) -> &[(Reg, usize)] {
        &self.mapping
    }
    pub fn evidence(&self) -> &AllocationEvidence {
        &self.evidence
    }
    pub fn renamed_register(&self, source: Reg) -> Option<Reg> {
        (source.0 < self.source.register_count())
            .then(|| self.names.get(&source.0).copied().unwrap_or(source))
    }
    /// Original inputs keep their positions; the new bank accepts arbitrary
    /// poison. The independent ownership check rejects reads of uninitialized
    /// local slots, so no chosen bank initializer is a semantic assumption.
    pub fn extend_input(&self, input: &[u64], poison: u64) -> Result<Vec<u64>, Error> {
        if input.len() != self.source.register_count() {
            return Err(Error::Input);
        }
        let mut extended = input.to_vec();
        extended.resize(self.program.register_count(), poison);
        Ok(extended)
    }
    pub fn validate(&self) -> Result<(), Error> {
        if self.source.register_count() > MAX_REGISTERS {
            return Err(Error::Limit);
        }
        // Rechecking source also bounds all expression traversals before any
        // recursive clone and independently proves the storage read invariant.
        let evidence = allocation_verify::validate(&self.source, &self.mapping)?;
        if evidence != self.evidence {
            return Err(Error::Correspondence);
        }
        let colors: BTreeSet<_> = self.mapping.iter().map(|(_, c)| *c).collect();
        let count = self
            .source
            .register_count()
            .checked_add(colors.len())
            .filter(|&n| n <= MAX_REGISTERS)
            .ok_or(Error::Limit)?;
        let mut by_color = BTreeMap::new();
        let mut by_slot = BTreeMap::new();
        if self.names.len() != self.mapping.len() {
            return Err(Error::Correspondence);
        }
        for (reg, color) in &self.mapping {
            let slot = *self.names.get(&reg.0).ok_or(Error::Correspondence)?;
            if slot.0 < self.source.register_count()
                || slot.0 >= count
                || by_color
                    .insert(*color, slot.0)
                    .is_some_and(|old| old != slot.0)
                || by_slot
                    .insert(slot.0, *color)
                    .is_some_and(|old| old != *color)
            {
                return Err(Error::Correspondence);
            }
        }
        if !renaming::validate(
            &self.source,
            &self.program,
            count,
            &self.names,
            Unmapped::Identity,
        ) {
            return Err(Error::Correspondence);
        }
        Ok(())
    }
}

/// Give each validated color a fresh slot, disjoint from every original and
/// unmapped parameter register. Sparse color labels never become array sizes.
/// No instruction, expression, or memory evaluation is deleted or reordered.
pub fn lower(source: &Program, mapping: &[(Reg, usize)]) -> Result<Lowering, Error> {
    if source.register_count() > MAX_REGISTERS {
        return Err(Error::Limit);
    }
    let evidence = allocation_verify::validate(source, mapping)?;
    let colors: BTreeSet<_> = mapping.iter().map(|(_, c)| *c).collect();
    let count = source
        .register_count()
        .checked_add(colors.len())
        .filter(|&n| n <= MAX_REGISTERS)
        .ok_or(Error::Limit)?;
    let slots: BTreeMap<_, _> = colors
        .into_iter()
        .enumerate()
        .map(|(n, c)| (c, Reg(source.register_count() + n)))
        .collect();
    let names: BTreeMap<_, _> = mapping.iter().map(|(r, c)| (r.0, slots[c])).collect();
    let program = renaming::relabel(source, count, &names, Unmapped::Identity)
        .ok_or(Error::Correspondence)?;
    let result = Lowering {
        source: source.clone(),
        program,
        mapping: mapping.to_vec(),
        names,
        evidence,
    };
    result.validate()?;
    Ok(result)
}
