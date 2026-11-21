//! Certified constant propagation over source-bound SSA, including loop phis.
//!
//! The solver's optimistic bottom is internal. Published facts use only Unknown
//! or Known; a separate closed-invariant check validates every claimed constant.
//! Rewriting retains all statements and syntactic loads. Pure fragments may
//! become constants, preserving checked memory, fault order and source traces.
use crate::dataflow::ssa::{SsaError, SsaEvidence, SsaFunction};
use crate::dataflow::ssa_facts::{self, Domain};
use crate::model::ir::{BinaryOp as B, Program};
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstantValue {
    Unknown,
    Known(u64),
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ConstantEvidence {
    pub ssa: SsaEvidence,
    pub constant_values: usize,
    pub replacements: usize,
}
#[derive(Clone, Debug)]
pub struct ConstantPlan {
    graph: SsaFunction,
    values: Vec<ConstantValue>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    Bottom,
    Known(u64),
    Unknown,
}
impl State {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x,
            (Self::Known(a), Self::Known(b)) if a == b => Self::Known(a),
            _ => Self::Unknown,
        }
    }
    fn published(self) -> ConstantValue {
        match self {
            Self::Known(n) => ConstantValue::Known(n),
            _ => ConstantValue::Unknown,
        }
    }
}
impl From<ConstantValue> for State {
    fn from(v: ConstantValue) -> Self {
        match v {
            ConstantValue::Known(n) => Self::Known(n),
            ConstantValue::Unknown => Self::Unknown,
        }
    }
}
impl ConstantPlan {
    pub fn analyze(source: &Program) -> Option<Self> {
        let graph = SsaFunction::build(source)?;
        let values = ssa_facts::solve::<State>(source, &graph)
            .ok()?
            .into_iter()
            .map(State::published)
            .collect::<Vec<_>>();
        validate_facts(source, &graph, &values).ok()?;
        Some(Self { graph, values })
    }
    pub fn graph(&self) -> &SsaFunction {
        &self.graph
    }
    pub fn values(&self) -> &[ConstantValue] {
        &self.values
    }
    pub fn propose(&self, source: &Program) -> Option<(Program, ConstantEvidence)> {
        let states = self
            .values
            .iter()
            .copied()
            .map(State::from)
            .collect::<Vec<_>>();
        let (candidate, evidence) = ssa_facts::propose(source, &self.graph, &states)?;
        Some((candidate, convert(evidence)))
    }
}
fn convert(e: ssa_facts::FactEvidence) -> ConstantEvidence {
    ConstantEvidence {
        ssa: e.ssa,
        constant_values: e.constant_values,
        replacements: e.replacements,
    }
}
pub fn validate_facts(
    source: &Program,
    graph: &SsaFunction,
    values: &[ConstantValue],
) -> Result<SsaEvidence, SsaError> {
    if values.len() != graph.values.len() || values.len() > crate::dataflow::ssa::MAX_VALUES {
        return Err(SsaError::Malformed("constant vector"));
    }
    let states = values.iter().copied().map(State::from).collect::<Vec<_>>();
    ssa_facts::validate_facts(source, graph, &states)
}
pub fn validate(
    source: &Program,
    graph: &SsaFunction,
    values: &[ConstantValue],
    candidate: &Program,
) -> Result<ConstantEvidence, SsaError> {
    if values.len() != graph.values.len() || values.len() > crate::dataflow::ssa::MAX_VALUES {
        return Err(SsaError::Malformed("constant vector"));
    }
    let states = values.iter().copied().map(State::from).collect::<Vec<_>>();
    ssa_facts::validate(source, graph, &states, candidate).map(convert)
}
impl Domain for State {
    fn bottom() -> Self {
        Self::Bottom
    }
    fn unknown() -> Self {
        Self::Unknown
    }
    fn constant(n: u64) -> Self {
        Self::Known(n)
    }
    fn number(self) -> Option<u64> {
        if let Self::Known(n) = self {
            Some(n)
        } else {
            None
        }
    }
    fn join(self, other: Self) -> Self {
        self.join(other)
    }
    fn finish(self) -> Self {
        if self == Self::Bottom {
            Self::Unknown
        } else {
            self
        }
    }
    fn valid(self) -> bool {
        self != Self::Bottom
    }
    fn follows_from(self, derived: Self) -> bool {
        self == Self::Unknown || self == derived
    }
    fn unary(op: crate::model::ir::UnaryOp, v: Self) -> Self {
        unary(op, v)
    }
    fn binary(op: B, a: Self, b: Self) -> Self {
        binary(op, a, b)
    }
    fn select(c: Self, t: Self, n: Self) -> Self {
        select(c, t, n)
    }
}
fn binary(op: B, a: State, b: State) -> State {
    match (a, b) {
        (State::Known(a), State::Known(b)) => State::Known(op.evaluate(a, b)),
        (State::Unknown, _) | (_, State::Unknown) => State::Unknown,
        _ => State::Bottom,
    }
}

fn unary(op: crate::model::ir::UnaryOp, value: State) -> State {
    match value {
        State::Known(n) => State::Known(op.evaluate(n)),
        other => other,
    }
}
fn select(c: State, t: State, n: State) -> State {
    match c {
        State::Known(0) => n,
        State::Known(_) => t,
        _ if t == n => t,
        State::Unknown => t.join(n),
        _ => State::Bottom,
    }
}
