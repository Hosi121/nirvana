//! Source correspondence for memory generations. The checker consumes the
//! proposed graph; it does not call the memory-graph builder or query walker.
use super::*;
use crate::dataflow::address_identity;

mod graph;
mod queries;
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct QueryEvidence {
    pub queries: usize,
    pub states: usize,
    pub links: usize,
    pub candidate_bytes: usize,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Evidence {
    pub graph: GraphEvidence,
    /// None preserves an unavailable query analysis, without a partial set.
    pub queries: Option<QueryEvidence>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ValidationError {
    Invalid(&'static str),
    Unavailable(&'static str),
}
impl std::fmt::Display for ValidationError {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid(reason) => write!(out, "memory SSA check mismatch: {reason}"),
            Self::Unavailable(reason) => {
                write!(out, "memory SSA check unavailable: {reason}")
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

/// Check the graph and each supplied backwards coverage invariant. Symbolic
/// address identities are shared; traversal, edge substitution, interval/byte
/// checks and closure are independent of the query producer.
pub fn validate(
    source: &Program,
    registers: &SsaFunction,
    candidate: &Analysis,
) -> Result<Evidence, ValidationError> {
    check_registers(source, registers)?;
    let facts = address_identity::ordered_memory_addresses(source, registers, &BTreeSet::new())
        .ok_or(Unavailable("address identities"))?;
    let graph = graph_with_facts(
        source,
        registers,
        candidate,
        &[],
        &facts.accesses,
        &facts.forms,
    )?;
    let queries = query_coverage(candidate, registers, &facts.phi_values)?;
    Ok(Evidence { graph, queries })
}

pub(super) fn query_coverage(
    candidate: &Analysis,
    registers: &SsaFunction,
    values: &Result<
        BTreeMap<crate::dataflow::ssa::ValueId, address_identity::ModularAddress>,
        String,
    >,
) -> Result<Option<QueryEvidence>, ValidationError> {
    if candidate.queries.is_err() {
        if !candidate.query_certificates.is_empty() {
            return Err(Invalid("partial query certificates"));
        }
        return Ok(None);
    }
    let values = values
        .as_ref()
        .map_err(|_| Unavailable("phi address identities"))?;
    queries::validate(candidate, registers, values).map(Some)
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
