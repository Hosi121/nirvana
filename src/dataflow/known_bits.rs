//! Validated per-bit facts over SSA. Zero/one masks describe bit patterns,
//! independently of source-language types and signedness annotations.
use crate::dataflow::ssa::{self, SsaError, SsaEvidence, SsaFunction};
use crate::dataflow::ssa_facts::{self, Domain};
use crate::model::ir::{BinaryOp as B, Program, UnaryOp, Width};
mod transfer;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct KnownBits {
    zero: u64,
    one: u64,
}
impl KnownBits {
    pub const UNKNOWN: Self = Self { zero: 0, one: 0 };
    pub fn new(zero: u64, one: u64) -> Option<Self> {
        (zero & one == 0).then_some(Self { zero, one })
    }
    pub const fn constant(value: u64) -> Self {
        Self {
            zero: !value,
            one: value,
        }
    }
    pub const fn zero(self) -> u64 {
        self.zero
    }
    pub const fn one(self) -> u64 {
        self.one
    }
    pub const fn minimum(self) -> u64 {
        self.one
    }
    pub const fn maximum(self) -> u64 {
        !self.zero
    }
    pub fn number(self) -> Option<u64> {
        (self.valid() && (self.zero | self.one) == u64::MAX).then_some(self.one)
    }
    pub const fn contains(self, value: u64) -> bool {
        value & self.zero == 0 && value & self.one == self.one
    }
    /// Join value sets: retain bits known on both alternatives.
    pub const fn join(self, other: Self) -> Self {
        Self {
            zero: self.zero & other.zero,
            one: self.one & other.one,
        }
    }
    pub fn unary(op: UnaryOp, value: Self) -> Self {
        transfer::unary(op, value)
    }
    pub fn binary(op: B, left: Self, right: Self) -> Self {
        transfer::binary(op, left, right)
    }
    fn valid(self) -> bool {
        self.zero & self.one == 0
    }
    fn follows_from(self, derived: Self) -> bool {
        self.zero & !derived.zero == 0 && self.one & !derived.one == 0
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    Bottom,
    Facts(KnownBits),
}
impl Domain for State {
    fn bottom() -> Self {
        Self::Bottom
    }
    fn unknown() -> Self {
        Self::Facts(KnownBits::UNKNOWN)
    }
    fn constant(n: u64) -> Self {
        Self::Facts(KnownBits::constant(n))
    }
    fn number(self) -> Option<u64> {
        match self {
            Self::Facts(v) => v.number(),
            Self::Bottom => None,
        }
    }
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, v) | (v, Self::Bottom) => v,
            (Self::Facts(a), Self::Facts(b)) => Self::Facts(a.join(b)),
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
        match self {
            Self::Facts(v) => v.valid(),
            Self::Bottom => false,
        }
    }
    fn follows_from(self, derived: Self) -> bool {
        match (self, derived) {
            (Self::Facts(a), Self::Facts(b)) => a.follows_from(b),
            _ => false,
        }
    }
    fn unary(op: UnaryOp, v: Self) -> Self {
        match v {
            Self::Facts(v) => Self::Facts(KnownBits::unary(op, v)),
            Self::Bottom => Self::Bottom,
        }
    }
    fn binary(op: B, a: Self, b: Self) -> Self {
        match (a, b) {
            (Self::Facts(a), Self::Facts(b)) => Self::Facts(KnownBits::binary(op, a, b)),
            _ => Self::Bottom,
        }
    }
    fn select(c: Self, t: Self, n: Self) -> Self {
        match c {
            _ if t == n => t,
            Self::Facts(c) if c.number() == Some(0) => n,
            Self::Facts(c) if c.one != 0 => t,
            Self::Facts(_) => t.join(n),
            Self::Bottom => Self::Bottom,
        }
    }
    fn load(width: Width) -> Self {
        Self::Facts(KnownBits {
            zero: !width.mask(),
            one: 0,
        })
    }
    fn binary_cost(op: B, a: Self, b: Self) -> usize {
        if a.number().is_some() && b.number().is_some() {
            return 0;
        }
        match op {
            B::Add | B::Sub if a == Self::unknown() || b == Self::unknown() => 0,
            B::Add | B::Sub => 64,
            B::Shl | B::Shr | B::AShr if b.number().is_none() => 64,
            _ => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct BitEvidence {
    pub ssa: SsaEvidence,
    pub known_values: usize,
    pub constant_values: usize,
    pub replacements: usize,
}
#[derive(Clone, Debug)]
pub struct BitPlan {
    graph: SsaFunction,
    values: Vec<KnownBits>,
}
impl BitPlan {
    pub fn analyze(source: &Program) -> Option<Self> {
        let graph = SsaFunction::build(source)?;
        let values = analyze_values(source, &graph).ok()?;
        let plan = Self { graph, values };
        Some(plan)
    }
    pub fn graph(&self) -> &SsaFunction {
        &self.graph
    }
    pub fn values(&self) -> &[KnownBits] {
        &self.values
    }
    /// Replace only proved constant, load-free fragments. Statement order,
    /// lazy load arms, stores and branch destinations retain their source sites.
    pub fn propose(&self, source: &Program) -> Option<(Program, BitEvidence)> {
        let states = self
            .values
            .iter()
            .copied()
            .map(State::Facts)
            .collect::<Vec<_>>();
        let (candidate, e) = ssa_facts::propose(source, &self.graph, &states)?;
        Some((candidate, convert(e, &self.values)))
    }
}

/// Reuse a source-bound SSA graph, for example from type or lifetime analysis.
/// Facts use that graph's value IDs and are checked against the supplied source.
pub fn analyze_values(source: &Program, graph: &SsaFunction) -> Result<Vec<KnownBits>, SsaError> {
    ssa::validate(source, graph)?;
    let values = ssa_facts::solve::<State>(source, graph)?
        .into_iter()
        .map(|s| match s {
            State::Facts(v) => v,
            State::Bottom => KnownBits::UNKNOWN,
        })
        .collect::<Vec<_>>();
    validate_facts(source, graph, &values)?;
    Ok(values)
}
fn states(graph: &SsaFunction, values: &[KnownBits]) -> Result<Vec<State>, SsaError> {
    if values.len() != graph.values.len() || values.len() > ssa::MAX_VALUES {
        return Err(SsaError::Malformed("bit fact vector"));
    }
    Ok(values.iter().copied().map(State::Facts).collect())
}
pub fn validate_facts(
    source: &Program,
    graph: &SsaFunction,
    values: &[KnownBits],
) -> Result<SsaEvidence, SsaError> {
    ssa_facts::validate_facts(source, graph, &states(graph, values)?)
}
pub fn validate(
    source: &Program,
    graph: &SsaFunction,
    values: &[KnownBits],
    candidate: &Program,
) -> Result<BitEvidence, SsaError> {
    ssa_facts::validate(source, graph, &states(graph, values)?, candidate)
        .map(|e| convert(e, values))
}
fn convert(e: ssa_facts::FactEvidence, values: &[KnownBits]) -> BitEvidence {
    BitEvidence {
        ssa: e.ssa,
        known_values: values.iter().filter(|v| **v != KnownBits::UNKNOWN).count(),
        constant_values: e.constant_values,
        replacements: e.replacements,
    }
}
