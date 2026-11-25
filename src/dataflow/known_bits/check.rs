//! Numeric checking separate from the KnownBits inference transfer.
//!
//! The checked SSA mapping, bounded `ssa_facts` source walk and candidate
//! shape/purity matcher remain trusted structural machinery. MemorySSA and
//! `LoadInputs` keep their existing source-bound byte provenance. Their generic
//! reconstruction runs with THIS domain, including unknown partial bytes.
//! This is not an independent implementation of the entire source traversal.

use super::KnownBits;
use crate::dataflow::ssa::{self, SsaError, SsaEvidence, SsaFunction};
use crate::dataflow::ssa_facts::{self, Domain, FactEvidence, LoadInputs};
use crate::model::ir::{BinaryOp, Program, UnaryOp, Width};

mod kernel;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CheckingDomain {
    Bottom,
    Facts(KnownBits),
}

impl Domain for CheckingDomain {
    fn bottom() -> Self {
        Self::Bottom
    }

    fn unknown() -> Self {
        Self::Facts(KnownBits { zero: 0, one: 0 })
    }

    fn constant(value: u64) -> Self {
        Self::Facts(KnownBits {
            zero: !value,
            one: value,
        })
    }

    fn number(self) -> Option<u64> {
        match self {
            Self::Facts(value)
                if value.zero & value.one == 0 && value.zero | value.one == u64::MAX =>
            {
                Some(value.one)
            }
            _ => None,
        }
    }

    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, value) | (value, Self::Bottom) => value,
            (Self::Facts(a), Self::Facts(b)) => Self::Facts(KnownBits {
                zero: a.zero & b.zero,
                one: a.one & b.one,
            }),
        }
    }

    fn finish(self) -> Self {
        if self == Self::Bottom {
            Self::unknown()
        } else {
            self
        }
    }

    fn valid(self) -> bool {
        matches!(self, Self::Facts(value) if value.zero & value.one == 0)
    }

    fn follows_from(self, derived: Self) -> bool {
        match (self, derived) {
            (Self::Facts(claim), Self::Facts(actual)) => {
                actual.zero & actual.one == 0
                    && claim.zero & !actual.zero == 0
                    && claim.one & !actual.one == 0
            }
            _ => false,
        }
    }

    fn unary(operation: UnaryOp, value: Self) -> Self {
        match value {
            Self::Facts(value) => Self::Facts(kernel::unary(operation, value)),
            Self::Bottom => Self::Bottom,
        }
    }

    fn binary(operation: BinaryOp, left: Self, right: Self) -> Self {
        match (left, right) {
            (Self::Facts(a), Self::Facts(b)) => Self::Facts(kernel::binary(operation, a, b)),
            _ => Self::Bottom,
        }
    }

    fn select(condition: Self, taken: Self, not_taken: Self) -> Self {
        if taken == not_taken {
            return taken;
        }
        match condition {
            Self::Facts(bits) if bits.zero == u64::MAX && bits.one == 0 => not_taken,
            Self::Facts(bits) if bits.one != 0 => taken,
            Self::Facts(_) => taken.join(not_taken),
            Self::Bottom => Self::Bottom,
        }
    }

    fn load(width: Width) -> Self {
        Self::Facts(KnownBits {
            zero: !((1u128 << width.bits()) - 1) as u64,
            one: 0,
        })
    }

    fn binary_cost(operation: BinaryOp, left: Self, right: Self) -> usize {
        if left.number().is_some() && right.number().is_some() {
            return 0;
        }
        match operation {
            BinaryOp::Add | BinaryOp::Sub
                if left == Self::unknown() || right == Self::unknown() =>
            {
                0
            }
            BinaryOp::Add | BinaryOp::Sub => 64,
            BinaryOp::Shl | BinaryOp::Shr | BinaryOp::AShr if right.number().is_none() => 64,
            _ => 1,
        }
    }
}

pub(super) fn dimensions(graph: &SsaFunction, values: &[KnownBits]) -> Result<(), SsaError> {
    if values.len() != graph.values.len() || values.len() > ssa::MAX_VALUES {
        return Err(SsaError::Malformed("bit fact vector"));
    }
    Ok(())
}

fn states(graph: &SsaFunction, values: &[KnownBits]) -> Result<Vec<CheckingDomain>, SsaError> {
    dimensions(graph, values)?;
    Ok(values.iter().copied().map(CheckingDomain::Facts).collect())
}

pub(super) fn validate_facts(
    source: &Program,
    graph: &SsaFunction,
    values: &[KnownBits],
    loads: &LoadInputs,
) -> Result<SsaEvidence, SsaError> {
    let states = states(graph, values)?;
    ssa_facts::validate_facts_with_loads(source, graph, &states, loads)
}

pub(super) fn validate(
    source: &Program,
    graph: &SsaFunction,
    values: &[KnownBits],
    loads: &LoadInputs,
    candidate: &Program,
) -> Result<FactEvidence, SsaError> {
    let states = states(graph, values)?;
    ssa_facts::validate_with_loads(source, graph, &states, loads, candidate)
}

#[cfg(test)]
mod smt_tests;
#[cfg(test)]
mod tests;
