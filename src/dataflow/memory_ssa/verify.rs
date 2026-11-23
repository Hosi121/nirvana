//! Source correspondence for memory generations. The checker consumes the
//! proposed graph; it does not call the memory-graph builder or query walker.
use super::*;
use crate::dataflow::address_identity;

mod graph;
#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GraphEvidence {
    pub blocks: usize,
    pub definitions: usize,
    pub accesses: usize,
    pub phi_inputs: usize,
    pub opaque_effects: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ValidationError {
    Invalid(&'static str),
    Unavailable(&'static str),
}
impl std::fmt::Display for ValidationError {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid(reason) => write!(out, "memory SSA graph mismatch: {reason}"),
            Self::Unavailable(reason) => {
                write!(out, "memory SSA graph check unavailable: {reason}")
            }
        }
    }
}
impl std::error::Error for ValidationError {}
use ValidationError::{Invalid, Unavailable};

struct Budget {
    work: usize,
    members: usize,
}
impl Budget {
    fn new() -> Self {
        Self {
            work: MAX_WORK,
            members: 0,
        }
    }
    fn spend(&mut self, amount: usize) -> Result<(), ValidationError> {
        self.work = self
            .work
            .checked_sub(amount)
            .ok_or(Unavailable("work budget"))?;
        Ok(())
    }
    fn retain(&mut self, amount: usize) -> Result<(), ValidationError> {
        self.members = self
            .members
            .checked_add(amount)
            .ok_or(Unavailable("candidate size"))?;
        if self.members > MAX_MEMBERS {
            return Err(Unavailable("candidate size"));
        }
        self.spend(amount)
    }
}

/// Validate generation/event/CFG correspondence for a closed single function.
/// Modular address identities are supplied by the shared address analysis.
/// This first layer does not certify the reaching-writer query results.
pub fn validate_graph(
    source: &Program,
    registers: &SsaFunction,
    candidate: &Analysis,
) -> Result<GraphEvidence, ValidationError> {
    check_registers(source, registers)?;
    let facts = address_identity::ordered_memory_addresses(source, registers, &BTreeSet::new())
        .ok_or(Unavailable("address identities"))?;
    graph_with_facts(
        source,
        registers,
        candidate,
        &[],
        &facts.accesses,
        &facts.forms,
    )
}

fn check_registers(source: &Program, registers: &SsaFunction) -> Result<(), ValidationError> {
    crate::dataflow::ssa::validate(source, registers)
        .map(|_| ())
        .map_err(|e| match e {
            crate::dataflow::ssa::SsaError::Unavailable(_) => Unavailable("register SSA"),
            crate::dataflow::ssa::SsaError::Malformed(_) => Invalid("register SSA"),
        })
}

pub(super) fn graph_with_facts(
    source: &Program,
    registers: &SsaFunction,
    candidate: &Analysis,
    effects: &[Effect],
    accesses: &[MemoryAccess],
    forms: &[Option<address_identity::ModularAddress>],
) -> Result<GraphEvidence, ValidationError> {
    check_registers(source, registers)?;
    graph::validate(source, registers, candidate, effects, accesses, forms)
}
