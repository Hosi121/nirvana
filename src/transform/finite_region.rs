//! Exhaustive pure-region equivalence under finite values derived from a prefix.
//!
//! Prefix facts overapproximate arbitrary program inputs on successful
//! continuation. The certificate covers normal scalar fallthrough only, not
//! instruction traces, prefix memory effects, or a source-structure certificate.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::control_flow::structure::Node;
use crate::model::ir::{BinaryOp, Expr, Place, Reg};

pub const MAX_SET_VALUES: usize = 16;
pub const MAX_CASES: usize = 256;
pub const MAX_INPUTS: usize = 16;
pub const MAX_OBSERVED: usize = 128;
pub const MAX_REGISTERS: usize = 4_096;
pub const MAX_NODES: usize = 4_096;
pub const MAX_EXPRESSION_NODES: usize = 65_536;
pub const MAX_NODE_DEPTH: usize = 64;
pub const MAX_EXPRESSION_DEPTH: usize = 128;
pub const MAX_CASE_WORK: usize = 20_000;
pub const MAX_WORK: usize = 4_000_000;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FiniteEvidence {
    pub cases: usize,
    pub inputs: Vec<(Reg, Vec<u64>)>,
    pub observed: Vec<Reg>,
    /// Maxima include every input value and every write by either region.
    pub maxima: Vec<(Reg, u64)>,
}

/// Conservative values on successful continuation of the actual prefix.
/// Unknown includes values that cannot be represented by the bounded set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PrefixDomain {
    Unknown,
    Finite(Vec<u64>),
}

/// Share the prefix model with other independently checked region proposals.
/// This derives bounds from arbitrary entry values, never from caller guesses.
pub fn derive_domains(prefix: &[Node], inputs: &[Reg]) -> Result<Vec<(Reg, PrefixDomain)>> {
    labels(inputs, MAX_INPUTS, "inputs")?;
    let mut work = Work(MAX_WORK);
    scan(prefix, false, &mut Bounds::default(), &mut work)?;
    let mut facts = BTreeMap::new();
    prefix_facts(prefix, &mut facts, &mut work)?;
    Ok(inputs
        .iter()
        .map(|&reg| {
            let domain = match facts.get(&reg.0) {
                Some(Values::Finite(values)) => {
                    PrefixDomain::Finite(values.iter().copied().collect())
                }
                _ => PrefixDomain::Unknown,
            };
            (reg, domain)
        })
        .collect())
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FiniteError {
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
    Counterexample {
        inputs: Vec<(Reg, u64)>,
        register: Reg,
        original: u64,
        candidate: u64,
    },
    Unavailable {
        resource: &'static str,
    },
}
impl FiniteError {
    pub fn is_resource_limit(&self) -> bool {
        matches!(self, Self::Unavailable { .. })
    }
}
impl fmt::Display for FiniteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed { register, detail } => {
                write!(f, "malformed finite region {register:?}: {detail}")
            }
            Self::Unsupported { detail } => write!(f, "unsupported finite region: {detail}"),
            Self::UnknownInput { register } => {
                write!(f, "prefix does not bound r{} to a finite set", register.0)
            }
            Self::Counterexample {
                inputs,
                register,
                original,
                candidate,
            } => write!(
                f,
                "finite region differs for {inputs:?}: r{} is {original}, candidate {candidate}",
                register.0
            ),
            Self::Unavailable { resource } => {
                write!(f, "finite region unavailable: {resource} limit")
            }
        }
    }
}
impl std::error::Error for FiniteError {}
type Result<T> = std::result::Result<T, FiniteError>;
fn unsupported(detail: &'static str) -> FiniteError {
    FiniteError::Unsupported { detail }
}
fn unavailable(resource: &'static str) -> FiniteError {
    FiniteError::Unavailable { resource }
}

struct Work(usize);
impl Work {
    fn spend(&mut self) -> Result<()> {
        self.reserve(1)
    }

    fn reserve(&mut self, amount: usize) -> Result<()> {
        self.0 = self
            .0
            .checked_sub(amount)
            .ok_or_else(|| unavailable("whole work"))?;
        Ok(())
    }
}

#[derive(Clone)]
enum Values {
    Unknown,
    Finite(BTreeSet<u64>),
}
impl Values {
    fn constant(value: u64) -> Self {
        Self::Finite(BTreeSet::from([value]))
    }
}

/// Inputs are not user-provided bounds: their full finite domains are derived
/// from the unchanged prefix. Both regions must terminate normally for every
/// Cartesian case before any evidence is returned.
pub fn validate(
    prefix: &[Node],
    original: &[Node],
    candidate: &[Node],
    inputs: &[Reg],
    observed: &[Reg],
) -> Result<FiniteEvidence> {
    let mut work = Work(MAX_WORK);
    let input_set = labels(inputs, MAX_INPUTS, "inputs")?;
    let observed_set = labels(observed, MAX_OBSERVED, "observed")?;
    let mut bounds = Bounds::default();
    scan(prefix, false, &mut bounds, &mut work)?;
    for region in [original, candidate] {
        let uses = scan(region, true, &mut bounds, &mut work)?;
        if let Some(&register) = uses.reads.difference(&input_set).next() {
            return Err(FiniteError::Malformed {
                register: Some(Reg(register)),
                detail: "region read outside inputs",
            });
        }
        if let Some(&register) = uses.writes.difference(&observed_set).next() {
            return Err(FiniteError::Malformed {
                register: Some(Reg(register)),
                detail: "region write outside observed",
            });
        }
    }
    let mut facts = BTreeMap::new();
    prefix_facts(prefix, &mut facts, &mut work)?;
    let mut domains = Vec::new();
    let mut cases = 1usize;
    let mut maxima = BTreeMap::new();
    for &reg in inputs {
        let Some(Values::Finite(values)) = facts.get(&reg.0) else {
            return Err(FiniteError::UnknownInput { register: reg });
        };
        cases = cases
            .checked_mul(values.len())
            .filter(|n| *n <= MAX_CASES)
            .ok_or_else(|| unavailable("Cartesian cases"))?;
        if values.is_empty() {
            return Err(unsupported("empty abstract domain"));
        }
        maxima.insert(reg.0, *values.last().unwrap());
        domains.push((reg, values.iter().copied().collect::<Vec<_>>()));
    }
    for case in 0..cases {
        let mut index = case;
        let mut assignment = Vec::new();
        let mut initial = BTreeMap::new();
        for (reg, values) in &domains {
            let value = values[index % values.len()];
            index /= values.len();
            assignment.push((*reg, value));
            initial.insert(reg.0, value);
        }
        let mut remaining = MAX_CASE_WORK;
        let left = execute(
            original,
            initial.clone(),
            &mut maxima,
            &mut work,
            &mut remaining,
        )?;
        let right = execute(candidate, initial, &mut maxima, &mut work, &mut remaining)?;
        for &reg in observed {
            let left = left
                .get(&reg.0)
                .copied()
                .ok_or_else(|| unsupported("original observed value is uninitialized"))?;
            let right = right
                .get(&reg.0)
                .copied()
                .ok_or_else(|| unsupported("candidate observed value is uninitialized"))?;
            if left != right {
                return Err(FiniteError::Counterexample {
                    inputs: assignment,
                    register: reg,
                    original: left,
                    candidate: right,
                });
            }
        }
    }
    Ok(FiniteEvidence {
        cases,
        inputs: domains,
        observed: observed.to_vec(),
        maxima: maxima
            .into_iter()
            .map(|(reg, value)| (Reg(reg), value))
            .collect(),
    })
}

fn labels(registers: &[Reg], max: usize, resource: &'static str) -> Result<BTreeSet<usize>> {
    if registers.len() > max {
        return Err(unavailable(resource));
    }
    let mut result = BTreeSet::new();
    for &reg in registers {
        if !result.insert(reg.0) {
            return Err(FiniteError::Malformed {
                register: Some(reg),
                detail: "duplicate label",
            });
        }
    }
    Ok(result)
}

fn apply(op: BinaryOp, a: u64, b: u64) -> u64 {
    op.evaluate(a, b)
}

fn union(a: Values, b: Values) -> Values {
    match (a, b) {
        (Values::Finite(mut a), Values::Finite(b)) => {
            a.extend(b);
            if a.len() <= MAX_SET_VALUES {
                Values::Finite(a)
            } else {
                Values::Unknown
            }
        }
        _ => Values::Unknown,
    }
}
// A constant-depth rejection hint only: every accepted interval still comes
// exclusively from the full raw-expression recognizer and its validator.
fn remainder_shape_hint(expression: &Expr) -> bool {
    let Expr::Binary(BinaryOp::Sub, _, product) = expression else {
        return false;
    };
    let product = match &**product {
        Expr::Binary(BinaryOp::And, a, b) => match (&**a, &**b) {
            (body, Expr::Const(_)) | (Expr::Const(_), body) => body,
            _ => return false,
        },
        product => product,
    };
    let Expr::Binary(BinaryOp::Mul, a, b) = product else {
        return false;
    };
    [(&**a, &**b), (&**b, &**a)]
        .into_iter()
        .any(|(quotient, factor)| {
            if !matches!(factor, Expr::Const(divisor) if *divisor >= 2) {
                return false;
            }
            let product = match quotient {
                Expr::Binary(BinaryOp::UMulHigh, _, _) => quotient,
                Expr::Binary(BinaryOp::Shr, product, count)
                    if matches!(&**count, Expr::Const(shift) if *shift <= 63) =>
                {
                    &**product
                }
                _ => return false,
            };
            matches!(
                product,
                Expr::Binary(BinaryOp::UMulHigh | BinaryOp::Mul, a, b)
                    if matches!(&**a, Expr::Const(m) if *m != 0)
                        || matches!(&**b, Expr::Const(m) if *m != 0)
            )
        })
}

fn abstract_value(
    expression: &Expr,
    facts: &BTreeMap<usize, Values>,
    work: &mut Work,
) -> Result<Values> {
    work.spend()?;
    let value = match expression {
        Expr::Unary(op, value) => match abstract_value(value, facts, work)? {
            Values::Finite(values) => {
                let mut mapped = BTreeSet::new();
                for value in values {
                    work.spend()?;
                    mapped.insert(op.evaluate(value));
                }
                Values::Finite(mapped)
            }
            Values::Unknown => Values::Unknown,
        },
        Expr::Const(value) => Values::constant(*value),
        Expr::Register(reg) => facts.get(&reg.0).cloned().unwrap_or(Values::Unknown),
        Expr::Load { .. } => Values::Unknown,
        Expr::Binary(op, left, right) => {
            let left = abstract_value(left, facts, work)?;
            let right = abstract_value(right, facts, work)?;
            if let (Values::Finite(a), Values::Finite(b)) = (&left, &right) {
                let mut values = BTreeSet::new();
                for &a in a {
                    for &b in b {
                        work.spend()?;
                        values.insert(apply(*op, a, b));
                        if values.len() > MAX_SET_VALUES {
                            return Ok(Values::Unknown);
                        }
                    }
                }
                Values::Finite(values)
            } else if *op == BinaryOp::And {
                let mask = match (&left, &right) {
                    (Values::Finite(v), _) | (_, Values::Finite(v)) if v.len() == 1 => {
                        v.first().copied()
                    }
                    _ => None,
                };
                if let Some(mask) = mask.filter(|m| m.count_ones() <= 4) {
                    let mut values = BTreeSet::new();
                    let mut value = mask;
                    loop {
                        work.spend()?;
                        values.insert(value);
                        if value == 0 {
                            break;
                        }
                        value = value.wrapping_sub(1) & mask;
                    }
                    Values::Finite(values)
                } else {
                    Values::Unknown
                }
            } else {
                Values::Unknown
            }
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            let condition = abstract_value(condition, facts, work)?;
            match condition {
                Values::Finite(values) if values.iter().all(|v| *v == 0) => {
                    abstract_value(not_taken, facts, work)?
                }
                Values::Finite(values) if values.iter().all(|v| *v != 0) => {
                    abstract_value(taken, facts, work)?
                }
                _ => union(
                    abstract_value(taken, facts, work)?,
                    abstract_value(not_taken, facts, work)?,
                ),
            }
        }
    };
    if matches!(value, Values::Unknown) && remainder_shape_hint(expression) {
        // Recognition independently proves a raw, pure unsigned remainder.
        // Reserve a conservative upper bound for its own scans, both quotient
        // recognizers and nested independent certificate validation. Repeated
        // unsuccessful probes therefore consume this pass's ordinary budget.
        work.reserve(16 * crate::transform::remainder_expr::MAX_WORK)?;
        if let Some(remainder) = crate::transform::remainder_expr::recognize(expression)
            && remainder.maximum_remainder < MAX_SET_VALUES as u64
        {
            // This numeric interval is a sound overapproximation, not a
            // possible-one mask or a guess from tested dividend values. Loads
            // in other prefix assignments stay at their original sites.
            let mut values = BTreeSet::new();
            for value in 0..=remainder.maximum_remainder {
                work.spend()?;
                values.insert(value);
            }
            return Ok(Values::Finite(values));
        }
    }
    Ok(value)
}

fn kill_writes(nodes: &[Node], facts: &mut BTreeMap<usize, Values>, work: &mut Work) -> Result<()> {
    let mut pending: Vec<_> = nodes.iter().collect();
    while let Some(node) = pending.pop() {
        work.spend()?;
        match node {
            Node::Step { assignments, .. } => {
                for assignment in assignments {
                    work.spend()?;
                    if let Place::Register(reg) = assignment.destination {
                        facts.remove(&reg.0);
                    }
                }
            }
            Node::If {
                taken, not_taken, ..
            } => pending.extend(taken.iter().chain(not_taken)),
            Node::Loop(body) => pending.extend(body),
            _ => {}
        }
    }
    Ok(())
}
fn prefix_facts(
    nodes: &[Node],
    facts: &mut BTreeMap<usize, Values>,
    work: &mut Work,
) -> Result<()> {
    for node in nodes {
        work.spend()?;
        match node {
            Node::Step { assignments, .. } => {
                for assignment in assignments {
                    work.spend()?;
                    if let Place::Register(reg) = assignment.destination {
                        let value = abstract_value(&assignment.value, facts, work)?;
                        facts.insert(reg.0, value);
                    }
                }
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => match abstract_value(condition, facts, work)? {
                Values::Finite(values) if values.iter().all(|v| *v == 0) => {
                    prefix_facts(not_taken, facts, work)?
                }
                Values::Finite(values) if values.iter().all(|v| *v != 0) => {
                    prefix_facts(taken, facts, work)?
                }
                _ => kill_writes(std::slice::from_ref(node), facts, work)?,
            },
            Node::Loop(body) => kill_writes(body, facts, work)?,
            Node::Evaluate(_) => {}
            _ => return Err(unsupported("prefix has an escaping transfer")),
        }
    }
    Ok(())
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
    if nodes.len() > MAX_NODES {
        return Err(unavailable("AST nodes"));
    }
    let mut pending: Vec<_> = nodes.iter().map(|n| (n, 1, 0)).collect();
    let mut uses = Uses::default();
    while let Some((node, depth, loops)) = pending.pop() {
        work.spend()?;
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
                    work.spend()?;
                    bounds.expressions += 1;
                    match &assignment.destination {
                        Place::Register(reg) => {
                            uses.writes.insert(reg.0);
                            bounds.registers.insert(reg.0);
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
                pending.extend(taken.iter().chain(not_taken).map(|n| (n, depth + 1, loops)));
            }
            Node::Loop(body) => {
                if body.len() > MAX_NODES {
                    return Err(unavailable("AST nodes"));
                }
                pending.extend(body.iter().map(|n| (n, depth + 1, loops + 1)));
            }
            Node::Evaluate(value) => expressions.push(value),
            Node::Return(value) => {
                if pure || depth == 1 {
                    return Err(unsupported("return in finite region/prefix"));
                }
                expressions.push(value);
            }
            Node::Break | Node::Continue => {
                if (pure && loops == 0) || (!pure && depth == 1) {
                    return Err(unsupported("escaping loop transfer"));
                }
            }
            Node::BreakOuter { .. } | Node::ContinueOuter { .. } => {
                if pure || depth == 1 {
                    return Err(unsupported("nonlocal transfer"));
                }
            }
        }
        for expression in expressions {
            let mut pending = vec![(expression, 1)];
            while let Some((expression, depth)) = pending.pop() {
                work.spend()?;
                bounds.expressions += 1;
                if bounds.expressions > MAX_EXPRESSION_NODES || depth > MAX_EXPRESSION_DEPTH {
                    return Err(unavailable("expressions/depth"));
                }
                match expression {
                    Expr::Unary(_, value) => pending.push((value, depth + 1)),
                    Expr::Register(reg) => {
                        uses.reads.insert(reg.0);
                        bounds.registers.insert(reg.0);
                    }
                    Expr::Const(_) => {}
                    Expr::Load { address, .. } => {
                        if pure {
                            return Err(unsupported("region contains a load"));
                        }
                        pending.push((address, depth + 1));
                    }
                    Expr::Binary(_, left, right) => {
                        pending.extend([(&**right, depth + 1), (&**left, depth + 1)])
                    }
                    Expr::Select {
                        condition,
                        taken,
                        not_taken,
                    } => pending.extend([
                        (&**not_taken, depth + 1),
                        (&**taken, depth + 1),
                        (&**condition, depth + 1),
                    ]),
                }
                if bounds.registers.len() > MAX_REGISTERS {
                    return Err(unavailable("registers"));
                }
            }
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
    values: BTreeMap<usize, u64>,
    maxima: &'a mut BTreeMap<usize, u64>,
    work: &'a mut Work,
    remaining: &'a mut usize,
}
impl Machine<'_> {
    fn tick(&mut self) -> Result<()> {
        self.work.spend()?;
        *self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or_else(|| unavailable("case execution"))?;
        Ok(())
    }
    fn expression(&mut self, expression: &Expr) -> Result<u64> {
        self.tick()?;
        Ok(match expression {
            Expr::Const(value) => *value,
            Expr::Unary(op, value) => op.evaluate(self.expression(value)?),
            Expr::Register(reg) => *self
                .values
                .get(&reg.0)
                .ok_or_else(|| unsupported("unbound case register"))?,
            Expr::Binary(op, left, right) => {
                let left = self.expression(left)?;
                let right = self.expression(right)?;
                apply(*op, left, right)
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let condition = self.expression(condition)?;
                self.expression(if condition != 0 { taken } else { not_taken })?
            }
            Expr::Load { .. } => return Err(unsupported("region contains a load")),
        })
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
                            .and_modify(|max| *max = (*max).max(value))
                            .or_insert(value);
                    }
                    Flow::Normal
                }
                Node::Evaluate(expression) => {
                    self.expression(expression)?;
                    Flow::Normal
                }
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    let condition = self.expression(condition)?;
                    self.nodes(if condition != 0 { taken } else { not_taken })?
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
                _ => return Err(unsupported("region has a return/nonlocal transfer")),
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
    initial: BTreeMap<usize, u64>,
    maxima: &mut BTreeMap<usize, u64>,
    work: &mut Work,
    remaining: &mut usize,
) -> Result<BTreeMap<usize, u64>> {
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
