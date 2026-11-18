//! Certified constant propagation over source-bound SSA, including loop phis.
//!
//! The solver's optimistic bottom is internal. Published facts use only Unknown
//! or Known; a separate closed-invariant check validates every claimed constant.
//! Rewriting retains all statements and syntactic loads. Pure fragments may
//! become constants, preserving checked memory, fault order and source traces.
use crate::ir::{BinaryOp as B, Control, Expr, Place, Program};
use crate::ssa::{
    self, Budget, Definition, PointValues, Site, SsaError, SsaEvidence, SsaFunction, ValueId,
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

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
        let values = solve(source, &graph).ok()?;
        validate_facts(source, &graph, &values).ok()?;
        Some(Self { graph, values })
    }
    pub fn graph(&self) -> &SsaFunction {
        &self.graph
    }
    pub fn values(&self) -> &[ConstantValue] {
        &self.values
    }
    /// All operations keep their source sites; only pure expression fragments
    /// are replaced. Observable dead-code elimination is a separate checked pass.
    pub fn propose(&self, source: &Program) -> Option<(Program, ConstantEvidence)> {
        let mut budget = Budget::new();
        ssa::preflight(source, &mut budget).ok()?;
        validate_facts(source, &self.graph, &self.values).ok()?;
        let points = point_map(&self.graph);
        let mut instructions = source.instructions().to_vec();
        for ins in &mut instructions {
            for (assignment, a) in ins.assignments.iter_mut().enumerate() {
                let site = Site {
                    instruction: ins.address,
                    assignment: Some(assignment),
                };
                let Some(point) = points.get(&site) else {
                    continue;
                };
                let mut cursor = 0;
                if let Place::Memory { address, .. } = &mut a.destination {
                    *address = rewrite(address, point, &self.values, &mut cursor, &mut budget)
                        .ok()?
                        .0;
                }
                a.value = rewrite(&a.value, point, &self.values, &mut cursor, &mut budget)
                    .ok()?
                    .0;
                if cursor != point.reads.len() {
                    return None;
                }
            }
            if let Control::Branch { condition, .. } | Control::Return(condition) = &mut ins.control
            {
                let Some(point) = points.get(&Site {
                    instruction: ins.address,
                    assignment: None,
                }) else {
                    continue;
                };
                let mut cursor = 0;
                *condition = rewrite(condition, point, &self.values, &mut cursor, &mut budget)
                    .ok()?
                    .0;
                if cursor != point.reads.len() {
                    return None;
                }
            }
        }
        let candidate = Program::new(
            source.cfg().block(source.cfg().entry()).start,
            source.register_count(),
            instructions,
        )
        .ok()?;
        let evidence = validate(source, &self.graph, &self.values, &candidate).ok()?;
        (evidence.replacements > 0).then_some((candidate, evidence))
    }
}
fn point_map(graph: &SsaFunction) -> BTreeMap<Site, &PointValues> {
    graph
        .blocks
        .iter()
        .flat_map(|b| &b.points)
        .map(|p| (p.site, p))
        .collect()
}
fn source_expr(source: &Program, site: Site) -> Result<&Expr, SsaError> {
    let i = source
        .instructions()
        .binary_search_by_key(&site.instruction, |i| i.address)
        .map_err(|_| SsaError::Malformed("constant site"))?;
    let assignment = site
        .assignment
        .ok_or(SsaError::Malformed("constant definition site"))?;
    Ok(&source.instructions()[i]
        .assignments
        .get(assignment)
        .ok_or(SsaError::Malformed("constant assignment"))?
        .value)
}
fn solve(source: &Program, graph: &SsaFunction) -> Result<Vec<ConstantValue>, SsaError> {
    let mut budget = Budget::new();
    ssa::preflight(source, &mut budget)?;
    let points = point_map(graph);
    let mut users = vec![Vec::new(); graph.values.len()];
    for (index, definition) in graph.values.iter().enumerate() {
        let inputs: Vec<ValueId> = match definition {
            Definition::Initial { .. } => vec![],
            Definition::Phi { inputs, .. } => inputs.iter().map(|p| p.value).collect(),
            Definition::Assignment { site, .. } => points
                .get(site)
                .ok_or(SsaError::Malformed("SSA point"))?
                .reads
                .iter()
                .map(|r| r.value)
                .collect(),
        };
        for id in inputs {
            budget.spend(1)?;
            users
                .get_mut(id.0)
                .ok_or(SsaError::Malformed("SSA input"))?
                .push(index);
        }
    }
    let mut values = vec![State::Bottom; graph.values.len()];
    let mut queued = vec![true; values.len()];
    let mut queue: VecDeque<_> = (0..values.len()).collect();
    while let Some(index) = queue.pop_front() {
        budget.spend(1)?;
        queued[index] = false;
        let value = match &graph.values[index] {
            Definition::Initial { .. } => State::Unknown,
            Definition::Phi { inputs, .. } => inputs.iter().try_fold(State::Bottom, |a, p| {
                budget.spend(1)?;
                Ok::<_, SsaError>(a.join(values[p.value.0]))
            })?,
            Definition::Assignment { site, .. } => {
                let point = points.get(site).ok_or(SsaError::Malformed("SSA point"))?;
                let mut cursor = 0;
                let value = evaluate(
                    source_expr(source, *site)?,
                    point,
                    &values,
                    &mut cursor,
                    &mut budget,
                )?
                .0;
                if cursor != point.reads.len() {
                    return Err(SsaError::Malformed("SSA constant reads"));
                }
                value
            }
        };
        let next = values[index].join(value);
        if next != values[index] {
            values[index] = next;
            for &user in &users[index] {
                budget.spend(1)?;
                if !queued[user] {
                    queue.push_back(user);
                    queued[user] = true;
                }
            }
        }
    }
    Ok(values.into_iter().map(State::published).collect())
}
/// Closed invariants over arbitrary initial registers. Unknown denotes every
/// u64 value. Every Known claim must follow from actual SSA operands/phi edges;
/// optimistic bottom is never accepted as proof of an incoming value.
pub fn validate_facts(
    source: &Program,
    graph: &SsaFunction,
    values: &[ConstantValue],
) -> Result<SsaEvidence, SsaError> {
    let evidence = ssa::validate(source, graph)?;
    if values.len() != graph.values.len() {
        return Err(SsaError::Malformed("constant vector"));
    }
    let mut budget = Budget::new();
    let points = point_map(graph);
    let states: Vec<_> = values.iter().copied().map(State::from).collect();
    for (index, definition) in graph.values.iter().enumerate() {
        budget.spend(1)?;
        let ConstantValue::Known(expected) = values[index] else {
            continue;
        };
        let actual = match definition {
            Definition::Initial { .. } => {
                return Err(SsaError::Malformed("constant initial value"));
            }
            Definition::Phi { inputs, .. } => {
                if inputs.is_empty() {
                    return Err(SsaError::Malformed("empty constant phi"));
                }
                inputs.iter().try_fold(State::Bottom, |a, p| {
                    budget.spend(1)?;
                    Ok::<_, SsaError>(a.join(states[p.value.0]))
                })?
            }
            Definition::Assignment { site, .. } => {
                let point = points.get(site).ok_or(SsaError::Malformed("SSA point"))?;
                let mut cursor = 0;
                let actual = evaluate(
                    source_expr(source, *site)?,
                    point,
                    &states,
                    &mut cursor,
                    &mut budget,
                )?
                .0;
                if cursor != point.reads.len() {
                    return Err(SsaError::Malformed("constant reads"));
                }
                actual
            }
        };
        if actual != State::Known(expected) {
            return Err(SsaError::Malformed("unproved constant invariant"));
        }
    }
    Ok(evidence)
}
fn read(
    expr: &Expr,
    point: &PointValues,
    states: &[State],
    cursor: &mut usize,
) -> Result<State, SsaError> {
    let Expr::Register(register) = expr else {
        return Err(SsaError::Malformed("register read"));
    };
    let entry = point
        .reads
        .get(*cursor)
        .ok_or(SsaError::Malformed("missing SSA read"))?;
    *cursor += 1;
    if entry.register != *register {
        return Err(SsaError::Malformed("SSA read register"));
    }
    states
        .get(entry.value.0)
        .copied()
        .ok_or(SsaError::Malformed("constant SSA value"))
}
fn evaluate(
    expr: &Expr,
    point: &PointValues,
    states: &[State],
    cursor: &mut usize,
    budget: &mut Budget,
) -> Result<(State, bool), SsaError> {
    budget.spend(1)?;
    Ok(match expr {
        Expr::Const(n) => (State::Known(*n), true),
        Expr::Register(_) => (read(expr, point, states, cursor)?, true),
        Expr::Load { address, .. } => {
            evaluate(address, point, states, cursor, budget)?;
            (State::Unknown, false)
        }
        Expr::Binary(op, a, b) => {
            let (a, ap) = evaluate(a, point, states, cursor, budget)?;
            let (b, bp) = evaluate(b, point, states, cursor, budget)?;
            (binary(*op, a, b), ap && bp)
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            let (c, cp) = evaluate(condition, point, states, cursor, budget)?;
            let (t, tp) = evaluate(taken, point, states, cursor, budget)?;
            let (n, np) = evaluate(not_taken, point, states, cursor, budget)?;
            (select(c, t, n), cp && tp && np)
        }
    })
}
fn binary(op: B, a: State, b: State) -> State {
    match (a, b) {
        (State::Known(a), State::Known(b)) => State::Known(match op {
            B::Add => a.wrapping_add(b),
            B::Sub => a.wrapping_sub(b),
            B::Mul => a.wrapping_mul(b),
            B::And => a & b,
            B::Or => a | b,
            B::Xor => a ^ b,
            B::Shl => a.wrapping_shl((b & 63) as u32),
            B::Shr => a.wrapping_shr((b & 63) as u32),
            B::Eq => (a == b) as u64,
            B::Ne => (a != b) as u64,
            B::Ult => (a < b) as u64,
            B::Ule => (a <= b) as u64,
            B::UMulHigh => ((u128::from(a) * u128::from(b)) >> 64) as u64,
        }),
        (State::Unknown, _) | (_, State::Unknown) => State::Unknown,
        _ => State::Bottom,
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
fn rewrite(
    expr: &Expr,
    point: &PointValues,
    values: &[ConstantValue],
    cursor: &mut usize,
    budget: &mut Budget,
) -> Result<(Expr, State, bool), SsaError> {
    budget.spend(1)?;
    let (mapped, value, pure) = match expr {
        Expr::Const(n) => (expr.clone(), State::Known(*n), true),
        Expr::Register(_) => {
            let entry = point
                .reads
                .get(*cursor)
                .ok_or(SsaError::Malformed("SSA read"))?;
            *cursor += 1;
            let value = values
                .get(entry.value.0)
                .copied()
                .ok_or(SsaError::Malformed("constant reference"))?;
            (expr.clone(), value.into(), true)
        }
        Expr::Load { address, width } => {
            let (a, _, _) = rewrite(address, point, values, cursor, budget)?;
            (Expr::load(a, *width), State::Unknown, false)
        }
        Expr::Binary(op, a, b) => {
            let (a, av, ap) = rewrite(a, point, values, cursor, budget)?;
            let (b, bv, bp) = rewrite(b, point, values, cursor, budget)?;
            (Expr::binary(*op, a, b), binary(*op, av, bv), ap && bp)
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            let (c, cv, cp) = rewrite(condition, point, values, cursor, budget)?;
            let (t, tv, tp) = rewrite(taken, point, values, cursor, budget)?;
            let (n, nv, np) = rewrite(not_taken, point, values, cursor, budget)?;
            (Expr::select(c, t, n), select(cv, tv, nv), cp && tp && np)
        }
    };
    Ok((
        if pure && let State::Known(n) = value {
            Expr::Const(n)
        } else {
            mapped
        },
        value,
        pure,
    ))
}
/// Independently inspect an actual candidate; no inserted reads, changed effects,
/// discarded lazy loads, or changed branch destinations are accepted.
pub fn validate(
    source: &Program,
    graph: &SsaFunction,
    values: &[ConstantValue],
    candidate: &Program,
) -> Result<ConstantEvidence, SsaError> {
    let evidence = validate_facts(source, graph, values)?;
    let mut budget = Budget::new();
    ssa::preflight(candidate, &mut budget)?;
    if source.register_count() != candidate.register_count()
        || source.instructions().len() != candidate.instructions().len()
        || source.cfg().block(source.cfg().entry()).start
            != candidate.cfg().block(candidate.cfg().entry()).start
    {
        return Err(SsaError::Malformed("constant program layout"));
    }
    let points = point_map(graph);
    let states: Vec<_> = values.iter().copied().map(State::from).collect();
    let reachable: BTreeSet<_> = source
        .cfg()
        .reachable_blocks()
        .into_iter()
        .flat_map(|id| {
            source.instructions()[source.cfg().block(id).instructions.clone()]
                .iter()
                .map(|i| i.address)
        })
        .collect();
    let mut replacements = 0;
    for (a, b) in source.instructions().iter().zip(candidate.instructions()) {
        budget.spend(1)?;
        if !reachable.contains(&a.address) {
            if a != b {
                return Err(SsaError::Malformed("unreachable changed"));
            }
            continue;
        }
        if a.address != b.address || a.size != b.size || a.assignments.len() != b.assignments.len()
        {
            return Err(SsaError::Malformed("constant instruction layout"));
        }
        for (index, (left, right)) in a.assignments.iter().zip(&b.assignments).enumerate() {
            let point = points
                .get(&Site {
                    instruction: a.address,
                    assignment: Some(index),
                })
                .ok_or(SsaError::Malformed("constant SSA point"))?;
            let mut cursor = 0;
            match (&left.destination, &right.destination) {
                (Place::Register(a), Place::Register(b)) if a == b => {}
                (
                    Place::Memory {
                        address: a,
                        width: aw,
                    },
                    Place::Memory {
                        address: b,
                        width: bw,
                    },
                ) if aw == bw => {
                    replacements += check_expr(a, b, point, &states, &mut cursor, &mut budget)?;
                }
                _ => return Err(SsaError::Malformed("constant destination")),
            }
            replacements += check_expr(
                &left.value,
                &right.value,
                point,
                &states,
                &mut cursor,
                &mut budget,
            )?;
            if cursor != point.reads.len() {
                return Err(SsaError::Malformed("constant point reads"));
            }
        }
        let expressions = match (&a.control, &b.control) {
            (
                Control::Branch {
                    condition: a,
                    target: at,
                },
                Control::Branch {
                    condition: b,
                    target: bt,
                },
            ) if at == bt => Some((a, b)),
            (Control::Return(a), Control::Return(b)) => Some((a, b)),
            (left, right) if left == right => None,
            _ => return Err(SsaError::Malformed("constant control")),
        };
        if let Some((left, right)) = expressions {
            let point = points
                .get(&Site {
                    instruction: a.address,
                    assignment: None,
                })
                .ok_or(SsaError::Malformed("constant control point"))?;
            let mut cursor = 0;
            replacements += check_expr(left, right, point, &states, &mut cursor, &mut budget)?;
            if cursor != point.reads.len() {
                return Err(SsaError::Malformed("constant control reads"));
            }
        }
    }
    Ok(ConstantEvidence {
        ssa: evidence,
        constant_values: values
            .iter()
            .filter(|v| matches!(v, ConstantValue::Known(_)))
            .count(),
        replacements,
    })
}
fn check_expr(
    source: &Expr,
    candidate: &Expr,
    point: &PointValues,
    states: &[State],
    cursor: &mut usize,
    budget: &mut Budget,
) -> Result<usize, SsaError> {
    budget.spend(1)?;
    if let Expr::Const(n) = candidate {
        let (value, pure) = evaluate(source, point, states, cursor, budget)?;
        if !pure || value != State::Known(*n) {
            return Err(SsaError::Malformed("unproved constant replacement"));
        }
        return Ok(usize::from(source != candidate));
    }
    match (source, candidate) {
        (Expr::Register(a), Expr::Register(b)) if a == b => {
            read(source, point, states, cursor)?;
            Ok(0)
        }
        (Expr::Binary(a, l, r), Expr::Binary(b, x, y)) if a == b => {
            Ok(check_expr(l, x, point, states, cursor, budget)?
                + check_expr(r, y, point, states, cursor, budget)?)
        }
        (
            Expr::Load {
                address: a,
                width: aw,
            },
            Expr::Load {
                address: b,
                width: bw,
            },
        ) if aw == bw => check_expr(a, b, point, states, cursor, budget),
        (
            Expr::Select {
                condition: a,
                taken: b,
                not_taken: c,
            },
            Expr::Select {
                condition: x,
                taken: y,
                not_taken: z,
            },
        ) => Ok(check_expr(a, x, point, states, cursor, budget)?
            + check_expr(b, y, point, states, cursor, budget)?
            + check_expr(c, z, point, states, cursor, budget)?),
        _ => Err(SsaError::Malformed("constant expression shape")),
    }
}
