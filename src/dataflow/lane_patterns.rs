//! Bounded proposal discovery for repeated load/update/store kernels.
//!
//! Descriptors retain source SSA identities and captured load sites. Matching
//! proposes a parameterized expression family; control, memory ordering, alias
//! independence and loop equivalence remain separate validation obligations.
use crate::dataflow::ssa::{Definition, PointValues, RegisterValue, Site, SsaFunction, ValueId};
use crate::model::ir::{
    Assignment, BinaryOp, Expr, IrInstruction, Place, Program, Reg, UnaryOp, Width,
};
use std::collections::BTreeMap;

mod group;
mod resolve;

pub const MODEL_ID: &str = "source-bound-lane-pattern-proposals-v1";
pub const MAX_REGISTERS: usize = 128;
pub const MAX_INSTRUCTIONS: usize = 1024;
pub const MAX_KERNELS: usize = 64;
pub const MAX_TERMS: usize = 65_536;
pub const MAX_DEPTH: usize = 32;
pub const MAX_WORK: usize = 2_000_000;
pub const MIN_LANES: usize = 3;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    Limit,
    SourceUnavailable,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "lane discovery: {self:?}")
    }
}
impl std::error::Error for Error {}

/// Pure syntax over source SSA values and one captured load/old accumulator.
/// `Lane` substitutes the corresponding group's exact offset at each site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternExpr {
    Constant(u64),
    Value(ValueId),
    Accumulator,
    Loaded,
    Lane,
    Unary(UnaryOp, Box<Self>),
    Binary(BinaryOp, Box<Self>, Box<Self>),
    Select(Box<Self>, Box<Self>, Box<Self>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Kernel {
    pub load: Site,
    pub update: Site,
    pub store: Site,
    pub accumulator: Reg,
    pub load_width: Width,
    pub store_width: Width,
    pub load_address: PatternExpr,
    pub update_expression: PatternExpr,
    pub store_address: PatternExpr,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LaneGroup {
    pub kernels: Vec<Kernel>,
    pub offsets: Vec<u64>,
    pub step: u64,
    pub load_address: PatternExpr,
    pub update_expression: PatternExpr,
    pub store_address: PatternExpr,
}

#[derive(Clone, Debug)]
pub struct Discovery {
    source: Program,
    ssa: SsaFunction,
    aliases: Vec<ValueId>,
    kernels: Vec<Kernel>,
    groups: Vec<LaneGroup>,
}
impl Discovery {
    pub fn kernels(&self) -> &[Kernel] {
        &self.kernels
    }
    pub fn groups(&self) -> &[LaneGroup] {
        &self.groups
    }
    pub fn ssa(&self) -> &SsaFunction {
        &self.ssa
    }
    /// Find storage that holds this exact normalized SSA value before a point.
    /// A non-entry register without an incoming phi stays unavailable; its
    /// original input value is not assumed to survive an earlier overwrite.
    pub fn available_register(&self, site: Site, value: ValueId) -> Option<Reg> {
        let wanted = *self.aliases.get(value.0)?;
        let block = self
            .ssa
            .blocks
            .iter()
            .find(|block| block.points.iter().any(|point| point.site == site))?;
        let mut current = vec![None; self.source.register_count()];
        if block.start == self.ssa.entry {
            for (id, definition) in self.ssa.values.iter().enumerate() {
                if let Definition::Initial { register } = definition {
                    current[register.0] = Some(ValueId(id));
                }
            }
        }
        for &id in &block.phis {
            let Definition::Phi { register, .. } = self.ssa.values[id.0] else {
                return None;
            };
            current[register.0] = Some(id);
        }
        for point in &block.points {
            if point.site == site {
                break;
            }
            if let Some(id) = point.definition {
                let Definition::Assignment { register, .. } = self.ssa.values[id.0] else {
                    return None;
                };
                current[register.0] = Some(id);
            }
        }
        current
            .iter()
            .position(|value| value.is_some_and(|value| self.aliases[value.0] == wanted))
            .map(Reg)
    }
    /// Expand a read's pure copy/definition chain in this retained source.
    /// Captured loads remain separate events and are unavailable as pure terms.
    pub fn register_expression(&self, site: Site, register: Reg) -> Option<PatternExpr> {
        let value = self
            .ssa
            .point(site)?
            .reads
            .iter()
            .find(|read| read.register == register)?
            .value;
        resolve::pure_value(&self.source, &self.ssa, &self.aliases, value)
    }
    pub fn belongs_to(&self, source: &Program) -> bool {
        self.source.register_count() == source.register_count()
            && self.source.cfg().block(self.source.cfg().entry()).start
                == source.cfg().block(source.cfg().entry()).start
            && self.source.instructions() == source.instructions()
    }
}

struct Budget {
    work: usize,
    terms: usize,
    exhausted: bool,
}
impl Budget {
    fn new() -> Self {
        Self {
            work: MAX_WORK,
            terms: MAX_TERMS,
            exhausted: false,
        }
    }
    fn spend(&mut self, count: usize) -> Option<()> {
        match self.work.checked_sub(count) {
            Some(left) => {
                self.work = left;
                Some(())
            }
            None => {
                self.exhausted = true;
                None
            }
        }
    }
    fn node(&mut self) -> Option<()> {
        match self.terms.checked_sub(1) {
            Some(left) => {
                self.terms = left;
                Some(())
            }
            None => {
                self.exhausted = true;
                None
            }
        }
    }
}

/// Discover at least three equally spaced lane offsets without source PC or
/// register-role hints. Only constants that vary together become parameters;
/// identical constants in other positions remain invariants. This greedy
/// discovery is a bounded proposal search, with no completeness claim.
pub fn discover(source: &Program) -> Result<Discovery, Error> {
    if source.register_count() > MAX_REGISTERS || source.instructions().len() > MAX_INSTRUCTIONS {
        return Err(Error::Limit);
    }
    let graph = SsaFunction::build(source).ok_or(Error::SourceUnavailable)?;
    let instructions: BTreeMap<_, _> = source
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let points: BTreeMap<_, _> = graph
        .blocks
        .iter()
        .flat_map(|b| &b.points)
        .map(|p| (p.site, p))
        .collect();
    let mut budget = Budget::new();
    let aliases =
        resolve::aliases(&graph, &instructions, &points, &mut budget).ok_or(Error::Limit)?;
    let mut kernels = Vec::new();
    for instruction in source.instructions() {
        for (index, assignment) in instruction.assignments.iter().enumerate() {
            if !matches!(assignment.destination, Place::Memory { .. }) {
                continue;
            }
            let site = Site {
                instruction: instruction.address,
                assignment: Some(index),
            };
            // Only entry-reachable SSA points participate.
            if !points.contains_key(&site) {
                continue;
            }
            if let Some(kernel) =
                resolve::kernel(&graph, &instructions, &points, &aliases, site, &mut budget)
            {
                if kernels.len() == MAX_KERNELS {
                    return Err(Error::Limit);
                }
                kernels.push(kernel);
            }
            if budget.exhausted {
                return Err(Error::Limit);
            }
        }
    }
    let groups = group::discover(&kernels, &mut budget);
    if budget.exhausted {
        return Err(Error::Limit);
    }
    Ok(Discovery {
        source: source.clone(),
        ssa: graph,
        aliases,
        kernels,
        groups,
    })
}

#[cfg(test)]
mod tests;
