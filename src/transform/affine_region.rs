//! Pure finite-control equivalence for one arbitrary u64 symbolic input.
//!
//! Every value is represented exactly as a*A+b modulo 2^64. Finite control
//! domains come exclusively from finite_region's prefix model. Acceptance is
//! normal scalar fallthrough for every finite case and every A, not a proof of
//! traces, prefix memory behavior, original source structure or generated C.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::control_flow::structure::Node;
use crate::model::ir::{BinaryOp, Expr, Place, Reg};
use crate::transform::finite_region::{self, FiniteError, PrefixDomain};

pub const MAX_CASES: usize = 256;
pub const MAX_INPUTS: usize = 16;
pub const MAX_OBSERVED: usize = 128;
pub const MAX_REGISTERS: usize = 4096;
pub const MAX_NODES: usize = 4096;
pub const MAX_EXPRESSION_NODES: usize = 65_536;
pub const MAX_NODE_DEPTH: usize = 64;
pub const MAX_EXPRESSION_DEPTH: usize = 128;
pub const MAX_CASE_WORK: usize = 20_000;
pub const MAX_WORK: usize = 4_000_000;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AffineEvidence {
    pub cases: usize,
    /// Finite inputs only. The symbolic input ranges over every u64.
    pub inputs: Vec<(Reg, Vec<u64>)>,
    pub symbolic_input: Reg,
    pub observed: Vec<Reg>,
    /// Safe maxima include every input and every write by both regions.
    /// Any nonconstant affine value has the conservative upper bound u64::MAX.
    pub maxima: Vec<(Reg, u64)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AffineError {
    Malformed {
        register: Option<Reg>,
        detail: &'static str,
    },
    Unsupported {
        detail: &'static str,
    },
    UnknownInput {
        register: Reg,
    },
    Prefix(FiniteError),
    Counterexample {
        /// Includes the symbolic input with the concrete value zero or one.
        inputs: Vec<(Reg, u64)>,
        register: Reg,
        original: u64,
        candidate: u64,
    },
    Unavailable {
        resource: &'static str,
    },
}
impl AffineError {
    pub fn is_resource_limit(&self) -> bool {
        matches!(self, Self::Unavailable { .. })
            || matches!(self, Self::Prefix(error) if error.is_resource_limit())
    }
}
impl fmt::Display for AffineError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed { register, detail } => {
                write!(f, "malformed affine region {register:?}: {detail}")
            }
            Self::Unsupported { detail } => write!(f, "unsupported affine region: {detail}"),
            Self::UnknownInput { register } => write!(
                f,
                "non-symbolic r{} has no finite prefix domain",
                register.0
            ),
            Self::Prefix(error) => write!(f, "affine prefix: {error}"),
            Self::Counterexample {
                inputs,
                register,
                original,
                candidate,
            } => write!(
                f,
                "affine region differs for {inputs:?}: r{} is {original}, candidate {candidate}",
                register.0
            ),
            Self::Unavailable { resource } => {
                write!(f, "affine region unavailable: {resource} limit")
            }
        }
    }
}
impl std::error::Error for AffineError {}
type Result<T> = std::result::Result<T, AffineError>;
fn unsupported(detail: &'static str) -> AffineError {
    AffineError::Unsupported { detail }
}
fn unavailable(resource: &'static str) -> AffineError {
    AffineError::Unavailable { resource }
}
fn malformed(register: Option<Reg>, detail: &'static str) -> AffineError {
    AffineError::Malformed { register, detail }
}
struct Work(usize);
impl Work {
    fn spend(&mut self, amount: usize) -> Result<()> {
        self.0 = self
            .0
            .checked_sub(amount)
            .ok_or_else(|| unavailable("whole work"))?;
        Ok(())
    }
}

/// Validate pure regions for every finite Cartesian control case and every
/// u64 value of exactly one designated Unknown prefix input. Prefix correlations
/// are safely overapproximated; no caller-supplied ranges or seed samples enter
/// the acceptance decision. Neither input AST is mutated or cloned recursively.
pub fn validate(
    prefix: &[Node],
    original: &[Node],
    candidate: &[Node],
    inputs: &[Reg],
    observed: &[Reg],
    symbolic: Reg,
) -> Result<AffineEvidence> {
    let mut work = Work(MAX_WORK);
    let input_set = labels(inputs, MAX_INPUTS, "inputs")?;
    let observed_set = labels(observed, MAX_OBSERVED, "observed")?;
    if !input_set.contains(&symbolic.0) {
        return Err(malformed(
            Some(symbolic),
            "symbolic register is not an input",
        ));
    }
    let mut bounds = Bounds::default();
    bounds
        .registers
        .extend(input_set.iter().chain(&observed_set).copied());
    scan(prefix, false, &mut bounds, &mut work)?;
    for region in [original, candidate] {
        let uses = scan(region, true, &mut bounds, &mut work)?;
        if let Some(&reg) = uses.reads.difference(&input_set).next() {
            return Err(malformed(Some(Reg(reg)), "region read outside inputs"));
        }
        if let Some(&reg) = uses.writes.difference(&observed_set).next() {
            return Err(malformed(Some(Reg(reg)), "region write outside observed"));
        }
    }
    let derived = finite_region::derive_domains(prefix, inputs).map_err(AffineError::Prefix)?;
    let mut domains = Vec::new();
    let mut cases = 1usize;
    let mut maxima = BTreeMap::from([(symbolic.0, u64::MAX)]);
    for (reg, domain) in derived {
        if reg == symbolic {
            if domain != PrefixDomain::Unknown {
                return Err(malformed(
                    Some(reg),
                    "symbolic input must have Unknown prefix domain",
                ));
            }
            continue;
        }
        let PrefixDomain::Finite(values) = domain else {
            return Err(AffineError::UnknownInput { register: reg });
        };
        if values.is_empty() {
            return Err(unsupported("empty prefix domain"));
        }
        cases = cases
            .checked_mul(values.len())
            .filter(|&n| n <= MAX_CASES)
            .ok_or_else(|| unavailable("Cartesian cases"))?;
        maxima.insert(reg.0, *values.iter().max().unwrap());
        domains.push((reg, values));
    }
    for case in 0..cases {
        work.spend(inputs.len() * 2 + observed.len())?;
        let mut index = case;
        let mut initial = BTreeMap::from([(symbolic.0, Value { a: 1, b: 0 })]);
        for (reg, values) in &domains {
            initial.insert(reg.0, Value::constant(values[index % values.len()]));
            index /= values.len();
        }
        let mut remaining = MAX_CASE_WORK;
        let left = execute(
            original,
            initial.clone(),
            &mut maxima,
            &mut work,
            &mut remaining,
        )?;
        let right = execute(
            candidate,
            initial.clone(),
            &mut maxima,
            &mut work,
            &mut remaining,
        )?;
        for &reg in observed {
            let left = *left
                .get(&reg.0)
                .ok_or_else(|| unsupported("original observed register is uninitialized"))?;
            let right = *right
                .get(&reg.0)
                .ok_or_else(|| unsupported("candidate observed register is uninitialized"))?;
            if left != right {
                let seed = u64::from(left.b == right.b);
                let inputs = inputs
                    .iter()
                    .map(|&reg| (reg, initial[&reg.0].evaluate(seed)))
                    .collect();
                return Err(AffineError::Counterexample {
                    inputs,
                    register: reg,
                    original: left.evaluate(seed),
                    candidate: right.evaluate(seed),
                });
            }
        }
    }
    Ok(AffineEvidence {
        cases,
        inputs: domains,
        symbolic_input: symbolic,
        observed: observed.to_vec(),
        maxima: maxima
            .into_iter()
            .map(|(reg, maximum)| (Reg(reg), maximum))
            .collect(),
    })
}

fn labels(registers: &[Reg], maximum: usize, resource: &'static str) -> Result<BTreeSet<usize>> {
    if registers.len() > maximum {
        return Err(unavailable(resource));
    }
    let mut result = BTreeSet::new();
    for &reg in registers {
        if !result.insert(reg.0) {
            return Err(malformed(Some(reg), "duplicate register"));
        }
    }
    Ok(result)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Value {
    a: u64,
    b: u64,
}
impl Value {
    fn constant(b: u64) -> Self {
        Self { a: 0, b }
    }
    fn evaluate(self, seed: u64) -> u64 {
        self.a.wrapping_mul(seed).wrapping_add(self.b)
    }
    fn maximum(self) -> u64 {
        if self.a == 0 { self.b } else { u64::MAX }
    }
    fn truth(self) -> Result<bool> {
        if self.a != 0 {
            return Err(unsupported("symbolic control condition"));
        }
        Ok(self.b != 0)
    }
    fn scale(self, scale: u64) -> Self {
        Self {
            a: self.a.wrapping_mul(scale),
            b: self.b.wrapping_mul(scale),
        }
    }
}
fn apply(op: BinaryOp, x: Value, y: Value) -> Result<Value> {
    use BinaryOp::*;
    if x.a == 0 && y.a == 0 {
        let (a, b) = (x.b, y.b);
        return Ok(Value::constant(match op {
            Add => a.wrapping_add(b),
            Sub => a.wrapping_sub(b),
            Mul => a.wrapping_mul(b),
            And => a & b,
            Or => a | b,
            Xor => a ^ b,
            Shl => a.wrapping_shl((b & 63) as u32),
            Shr => a.wrapping_shr((b & 63) as u32),
            Eq => u64::from(a == b),
            Ne => u64::from(a != b),
            Ult => u64::from(a < b),
            Ule => u64::from(a <= b),
            UMulHigh => ((u128::from(a) * u128::from(b)) >> 64) as u64,
        }));
    }
    Ok(match op {
        Add => Value {
            a: x.a.wrapping_add(y.a),
            b: x.b.wrapping_add(y.b),
        },
        Sub => Value {
            a: x.a.wrapping_sub(y.a),
            b: x.b.wrapping_sub(y.b),
        },
        Mul if x.a == 0 => y.scale(x.b),
        Mul if y.a == 0 => x.scale(y.b),
        Shl if y.a == 0 => x.scale(1u64.wrapping_shl((y.b & 63) as u32)),
        Shr if y.a == 0 && y.b & 63 == 0 => x,
        Eq | Ne | Ult | Ule if x == y => Value::constant(u64::from(matches!(op, Eq | Ule))),
        And if x.a == 0 && x.b == 0 || y.a == 0 && y.b == 0 => Value::constant(0),
        And if x.a == 0 && x.b == u64::MAX => y,
        And if y.a == 0 && y.b == u64::MAX => x,
        Or if x.a == 0 && x.b == 0 => y,
        Or if y.a == 0 && y.b == 0 => x,
        Or if x.a == 0 && x.b == u64::MAX || y.a == 0 && y.b == u64::MAX => {
            Value::constant(u64::MAX)
        }
        Xor if x.a == 0 && x.b == 0 => y,
        Xor if y.a == 0 && y.b == 0 => x,
        UMulHigh if x.a == 0 && x.b == 0 || y.a == 0 && y.b == 0 => Value::constant(0),
        _ => return Err(unsupported("operation is not supported affine arithmetic")),
    })
}

#[derive(Default)]
struct Bounds {
    nodes: usize,
    expressions: usize,
    registers: BTreeSet<usize>,
}
#[derive(Default)]
struct Uses {
    reads: BTreeSet<usize>,
    writes: BTreeSet<usize>,
}
fn scan(nodes: &[Node], pure: bool, bounds: &mut Bounds, work: &mut Work) -> Result<Uses> {
    if bounds
        .nodes
        .checked_add(nodes.len())
        .is_none_or(|n| n > MAX_NODES)
    {
        return Err(unavailable("AST nodes"));
    }
    let mut pending: Vec<_> = nodes.iter().map(|node| (node, 1usize, 0usize)).collect();
    let mut uses = Uses::default();
    while let Some((node, depth, loops)) = pending.pop() {
        work.spend(1)?;
        bounds.nodes += 1;
        if bounds.nodes > MAX_NODES || depth > MAX_NODE_DEPTH {
            return Err(unavailable("AST nodes/depth"));
        }
        let mut expressions = Vec::new();
        match node {
            Node::Step { assignments, .. } => {
                if assignments.len() > MAX_EXPRESSION_NODES {
                    return Err(unavailable("assignments"));
                }
                for assignment in assignments {
                    work.spend(1)?;
                    bounds.expressions += 1;
                    if bounds.expressions > MAX_EXPRESSION_NODES {
                        return Err(unavailable("assignments/expressions"));
                    }
                    match &assignment.destination {
                        Place::Register(reg) => {
                            bounds.registers.insert(reg.0);
                            if bounds.registers.len() > MAX_REGISTERS {
                                return Err(unavailable("active registers"));
                            }
                            uses.writes.insert(reg.0);
                        }
                        Place::Memory { address, .. } => {
                            if pure {
                                return Err(unsupported("region contains a store"));
                            }
                            expressions.push(address);
                        }
                    }
                    expressions.push(&assignment.value);
                }
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                if taken
                    .len()
                    .checked_add(not_taken.len())
                    .is_none_or(|n| n > MAX_NODES)
                {
                    return Err(unavailable("AST nodes"));
                }
                expressions.push(condition);
                if bounds.nodes + pending.len() + taken.len() + not_taken.len() > MAX_NODES {
                    return Err(unavailable("pending AST nodes"));
                }
                pending.extend(
                    taken
                        .iter()
                        .chain(not_taken)
                        .map(|node| (node, depth + 1, loops)),
                );
            }
            Node::Loop(body) => {
                if body.len() > MAX_NODES {
                    return Err(unavailable("AST nodes"));
                }
                if bounds.nodes + pending.len() + body.len() > MAX_NODES {
                    return Err(unavailable("pending AST nodes"));
                }
                pending.extend(body.iter().map(|node| (node, depth + 1, loops + 1)));
            }
            Node::Evaluate(value) => expressions.push(value),
            Node::Break | Node::Continue if pure && loops == 0 => {
                return Err(unsupported("escaping loop transfer"));
            }
            Node::Return(_) | Node::BreakOuter { .. } | Node::ContinueOuter { .. } if pure => {
                return Err(unsupported("region has return/nonlocal transfer"));
            }
            Node::Return(value) => expressions.push(value),
            _ => {}
        }
        for expression in expressions {
            let mut pending = vec![(expression, 1usize)];
            while let Some((expression, depth)) = pending.pop() {
                work.spend(1)?;
                bounds.expressions += 1;
                if bounds.expressions > MAX_EXPRESSION_NODES || depth > MAX_EXPRESSION_DEPTH {
                    return Err(unavailable("expressions/depth"));
                }
                match expression {
                    Expr::Register(reg) => {
                        uses.reads.insert(reg.0);
                        bounds.registers.insert(reg.0);
                    }
                    Expr::Const(_) => {}
                    Expr::Binary(_, a, b) => pending.extend([(&**a, depth + 1), (&**b, depth + 1)]),
                    Expr::Select {
                        condition,
                        taken,
                        not_taken,
                    } => pending.extend([
                        (&**condition, depth + 1),
                        (&**taken, depth + 1),
                        (&**not_taken, depth + 1),
                    ]),
                    Expr::Load { address, .. } => {
                        if pure {
                            return Err(unsupported("region contains a load"));
                        }
                        pending.push((address, depth + 1));
                    }
                }
                if bounds.registers.len() > MAX_REGISTERS {
                    return Err(unavailable("active registers"));
                }
            }
        }
        if bounds.registers.len() > MAX_REGISTERS {
            return Err(unavailable("active registers"));
        }
    }
    Ok(uses)
}

enum Flow {
    Normal,
    Break,
    Continue,
}
struct Machine<'a> {
    values: BTreeMap<usize, Value>,
    maxima: &'a mut BTreeMap<usize, u64>,
    work: &'a mut Work,
    remaining: &'a mut usize,
}
impl Machine<'_> {
    fn tick(&mut self) -> Result<()> {
        self.work.spend(1)?;
        *self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or_else(|| unavailable("case execution"))?;
        Ok(())
    }
    fn expression(&mut self, value: &Expr) -> Result<Value> {
        self.tick()?;
        match value {
            Expr::Const(value) => Ok(Value::constant(*value)),
            Expr::Register(reg) => self
                .values
                .get(&reg.0)
                .copied()
                .ok_or_else(|| unsupported("unbound case register")),
            Expr::Binary(op, a, b) => {
                let a = self.expression(a)?;
                let b = self.expression(b)?;
                apply(*op, a, b)
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let branch = self.expression(condition)?.truth()?;
                self.expression(if branch { taken } else { not_taken })
            }
            Expr::Load { .. } => Err(unsupported("region contains a load")),
        }
    }
    fn nodes(&mut self, nodes: &[Node]) -> Result<Flow> {
        for node in nodes {
            self.tick()?;
            let flow = match node {
                Node::Step { assignments, .. } => {
                    for assignment in assignments {
                        self.tick()?;
                        let Place::Register(reg) = assignment.destination else {
                            return Err(unsupported("region contains a store"));
                        };
                        let value = self.expression(&assignment.value)?;
                        self.values.insert(reg.0, value);
                        self.maxima
                            .entry(reg.0)
                            .and_modify(|max| *max = (*max).max(value.maximum()))
                            .or_insert(value.maximum());
                    }
                    Flow::Normal
                }
                Node::Evaluate(value) => {
                    self.expression(value)?;
                    Flow::Normal
                }
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    let branch = self.expression(condition)?.truth()?;
                    self.nodes(if branch { taken } else { not_taken })?
                }
                Node::Loop(body) => loop {
                    self.tick()?;
                    match self.nodes(body)? {
                        Flow::Normal | Flow::Continue => {}
                        Flow::Break => break Flow::Normal,
                    }
                },
                Node::Break => Flow::Break,
                Node::Continue => Flow::Continue,
                _ => return Err(unsupported("region has return/nonlocal transfer")),
            };
            if !matches!(flow, Flow::Normal) {
                return Ok(flow);
            }
        }
        Ok(Flow::Normal)
    }
}
fn execute(
    nodes: &[Node],
    initial: BTreeMap<usize, Value>,
    maxima: &mut BTreeMap<usize, u64>,
    work: &mut Work,
    remaining: &mut usize,
) -> Result<BTreeMap<usize, Value>> {
    let mut machine = Machine {
        values: initial,
        maxima,
        work,
        remaining,
    };
    if !matches!(machine.nodes(nodes)?, Flow::Normal) {
        return Err(unsupported("region transfer escapes its loop"));
    }
    Ok(machine.values)
}
