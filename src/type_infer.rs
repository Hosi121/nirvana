//! SSA value constraints and tentative memory shapes for inspection.
//!
//! These annotations describe observed operations and possible interpretations.
//! They do not choose source declarations, allocations, alias rules or C casts.
//! The original program is never rewritten by this module.
use crate::ir::{AccessKind, Program, Width};
use crate::ssa::{Site, SsaFunction, ValueId};
mod address;
mod analyze;
mod report;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Uses {
    pub signed_compare: bool,
    pub unsigned_compare: bool,
    pub logical_shift: bool,
    pub bitwise: bool,
    pub address_base: bool,
    pub address_index: bool,
    pub returned: bool,
    pub stored: bool,
}
impl Uses {
    pub(crate) fn union(self, other: Self) -> Self {
        Self {
            signed_compare: self.signed_compare || other.signed_compare,
            unsigned_compare: self.unsigned_compare || other.unsigned_compare,
            logical_shift: self.logical_shift || other.logical_shift,
            bitwise: self.bitwise || other.bitwise,
            address_base: self.address_base || other.address_base,
            address_index: self.address_index || other.address_index,
            returned: self.returned || other.returned,
            stored: self.stored || other.stored,
        }
    }
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ValueFacts {
    /// Unsigned upper bit bound, 0..=64; zero denotes exactly zero. This is not
    /// the declared width or signedness of a source-language variable.
    pub maximum_bits: u8,
    pub direct_uses: Uses,
    /// Possible uses propagated through copies and phi alternatives.
    pub flow_uses: Uses,
}
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
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FieldCandidate {
    pub offset: u64,
    pub width: Width,
    pub reads: bool,
    pub writes: bool,
    pub loaded_values: Vec<ValueId>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArrayCandidate {
    pub offset: u64,
    pub stride: u64,
    pub width: Width,
    pub indices: Vec<ValueId>,
    pub loaded_values: Vec<ValueId>,
    pub reads: bool,
    pub writes: bool,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LayoutCandidate {
    pub base: ValueId,
    pub fields: Vec<FieldCandidate>,
    pub arrays: Vec<ArrayCandidate>,
    /// Distinct scalar access intervals which overlap. Same offset/width
    /// repeated accesses share one candidate field rather than an overlap.
    pub overlaps: Vec<(usize, usize)>,
    /// Relative interval endpoints could not be represented in signed offsets.
    pub ambiguous_intervals: bool,
}
#[derive(Clone, Debug)]
pub struct TypeAnalysis {
    graph: SsaFunction,
    aliases: Vec<ValueId>,
    facts: Vec<ValueFacts>,
    accesses: Vec<MemoryAccess>,
    layouts: Vec<LayoutCandidate>,
}
impl TypeAnalysis {
    pub fn analyze(source: &Program) -> Option<Self> {
        analyze::analyze(source)
    }
    pub fn graph(&self) -> &SsaFunction {
        &self.graph
    }
    pub fn aliases(&self) -> &[ValueId] {
        &self.aliases
    }
    pub fn values(&self) -> &[ValueFacts] {
        &self.facts
    }
    pub fn accesses(&self) -> &[MemoryAccess] {
        &self.accesses
    }
    pub fn layouts(&self) -> &[LayoutCandidate] {
        &self.layouts
    }
}

/// Check unsigned bit bounds against arbitrary initial values and all SSA edges.
pub fn validate_bounds(source: &Program, graph: &SsaFunction, bits: &[u8]) -> bool {
    analyze::validate_bounds(source, graph, bits)
}

impl TypeAnalysis {
    /// A bounded JSON inspection report; interpretations remain candidates.
    pub fn to_json(&self) -> Option<String> {
        report::render(self)
    }
}
