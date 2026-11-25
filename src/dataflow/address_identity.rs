//! Source-bound SSA address identities and ordered memory access evidence.
//! Modular equalities are shared by memory SSA and tentative type layouts.
use crate::dataflow::ssa::{Site, SsaFunction, ValueId};
use crate::model::ir::{AccessKind, Program, Width};
mod aliases;
mod collect;
mod modular_verify;
mod verify;
pub(crate) use collect::collect_with_bounds;
pub use modular_verify::ValidationEvidence as ModularEvidence;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Operand {
    Destination,
    Value,
    Control,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PathEdge {
    Left,
    Right,
    Address,
    Condition,
    Taken,
    NotTaken,
    Unary,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ScaledIndex {
    pub value: ValueId,
    pub stride: u64,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AddressShape {
    Absolute(u64),
    Base {
        base: ValueId,
        offset: u64,
        index: Option<ScaledIndex>,
    },
    Unknown,
}

/// A modular equality over SSA values, independent of pointer/object roles.
/// Terms have nonzero coefficients and are sorted by value ID.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ModularAddress {
    pub offset: u64,
    pub terms: Vec<(ValueId, u64)>,
}

pub(crate) struct MemoryAddresses {
    pub accesses: Vec<MemoryAccess>,
    pub forms: Vec<Option<ModularAddress>>,
    pub phi_values: Result<std::collections::BTreeMap<ValueId, ModularAddress>, String>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MemoryAccess {
    pub site: Site,
    pub operand: Operand,
    pub path: Vec<PathEdge>,
    pub kind: AccessKind,
    pub width: Width,
    /// Exact modular address identity for supported affine forms; no bounds or
    /// object-separation claim. Unknown retains the original access evidence.
    pub address: AddressShape,
    /// Only an unmodified root Load assigned to an SSA value has a result ID.
    pub result: Option<ValueId>,
}
/// Exact modular access identities with fresh, uninterpreted effect outputs.
/// All bit hulls are 64: analysis placeholders supply no numeric facts.
pub(crate) fn ordered_memory_addresses(
    source: &Program,
    graph: &SsaFunction,
    opaque: &std::collections::BTreeSet<Site>,
) -> Option<MemoryAddresses> {
    checked_memory_addresses(source, graph, opaque).map(|(facts, _)| facts)
}

/// Publish modular facts only after source-bound independent checking. Access
/// evidence survives an unavailable phi check; queries then remain unavailable.
pub(crate) fn checked_memory_addresses(
    source: &Program,
    graph: &SsaFunction,
    opaque: &std::collections::BTreeSet<Site>,
) -> Option<(MemoryAddresses, ModularEvidence)> {
    let aliases = aliases(source, graph, opaque)?;
    let mut candidate = collect::collect_memory(
        source,
        graph,
        &aliases,
        &vec![64; graph.values.len()],
        opaque,
    )?;
    let evidence = if candidate.phi_values.is_ok() {
        match modular_verify::validate(source, graph, &aliases, opaque, &candidate) {
            Ok(evidence) => evidence,
            Err(reason) if reason.starts_with("unavailable:") => {
                let evidence =
                    modular_verify::validate_accesses(source, graph, &aliases, opaque, &candidate)
                        .ok()?;
                candidate.phi_values = Err(reason);
                evidence
            }
            Err(_) => return None,
        }
    } else {
        modular_verify::validate_accesses(source, graph, &aliases, opaque, &candidate).ok()?
    };
    Some((candidate, evidence))
}

pub(crate) fn aliases(
    source: &Program,
    graph: &SsaFunction,
    opaque: &std::collections::BTreeSet<Site>,
) -> Option<Vec<ValueId>> {
    crate::dataflow::ssa::validate(source, graph).ok()?;
    let candidate = aliases::collect(source, graph, opaque)?;
    verify::validate(source, graph, &candidate, opaque)?;
    Some(candidate)
}
