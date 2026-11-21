//! Source-bound SSA fixed points and independently checked constant rewrites.
//! Domains supply value-set joins and scalar transfer functions; this module
//! owns source sites, phi edges, resource bounds and preservation of effects.
use crate::dataflow::ssa::{
    self, Budget, Definition, PointValues, Site, SsaError, SsaEvidence, SsaFunction, ValueId,
};
use crate::model::ir::{BinaryOp as B, Control, Expr, Place, Program, UnaryOp, Width};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
mod memory;
pub(crate) use memory::LoadInputs;

pub(crate) trait Domain: Copy + Eq {
    fn bottom() -> Self;
    fn unknown() -> Self;
    fn constant(value: u64) -> Self;
    fn number(self) -> Option<u64>;
    fn join(self, other: Self) -> Self;
    fn finish(self) -> Self;
    fn valid(self) -> bool;
    /// The derived set must be contained in the claimed set.
    fn follows_from(self, derived: Self) -> bool;
    fn unary(op: UnaryOp, value: Self) -> Self;
    fn binary(op: B, left: Self, right: Self) -> Self;
    fn select(condition: Self, taken: Self, not_taken: Self) -> Self;
    fn load(_width: Width) -> Self {
        Self::unknown()
    }
    fn binary_cost(_op: B, _left: Self, _right: Self) -> usize {
        0
    }
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct FactEvidence {
    pub ssa: SsaEvidence,
    pub constant_values: usize,
    pub replacements: usize,
}

pub(crate) fn propose<D: Domain>(
    source: &Program,
    graph: &SsaFunction,
    values: &[D],
) -> Option<(Program, FactEvidence)> {
    propose_with_loads(source, graph, values, &LoadInputs::default())
}
pub(crate) fn propose_with_loads<D: Domain>(
    source: &Program,
    graph: &SsaFunction,
    values: &[D],
    loads: &LoadInputs,
) -> Option<(Program, FactEvidence)> {
    let mut budget = Budget::new();
    ssa::preflight(source, &mut budget).ok()?;
    validate_facts_with_loads(source, graph, values, loads).ok()?;
    let points = point_map(graph);
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
                *address = rewrite(address, point, values, &mut cursor, &mut budget)
                    .ok()?
                    .0;
            }
            a.value = rewrite(&a.value, point, values, &mut cursor, &mut budget)
                .ok()?
                .0;
            if cursor != point.reads.len() {
                return None;
            }
        }
        if let Control::Branch { condition, .. } | Control::Return(condition) = &mut ins.control {
            let Some(point) = points.get(&Site {
                instruction: ins.address,
                assignment: None,
            }) else {
                continue;
            };
            let mut cursor = 0;
            *condition = rewrite(condition, point, values, &mut cursor, &mut budget)
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
    let evidence = validate_with_loads(source, graph, values, loads, &candidate).ok()?;
    (evidence.replacements > 0).then_some((candidate, evidence))
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
pub(crate) fn solve<D: Domain>(source: &Program, graph: &SsaFunction) -> Result<Vec<D>, SsaError> {
    solve_with_loads(source, graph, &LoadInputs::default())
}
pub(crate) fn solve_with_loads<D: Domain>(
    source: &Program,
    graph: &SsaFunction,
    loads: &LoadInputs,
) -> Result<Vec<D>, SsaError> {
    let mut budget = Budget::new();
    ssa::preflight(source, &mut budget)?;
    let points = point_map(graph);
    let mut users = vec![Vec::new(); graph.values.len()];
    for (index, definition) in graph.values.iter().enumerate() {
        let mut inputs: Vec<ValueId> = match definition {
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
        if let Definition::Assignment { site, .. } = definition {
            inputs.extend_from_slice(loads.dependencies(*site));
        }
        for id in inputs {
            budget.spend(1)?;
            users
                .get_mut(id.0)
                .ok_or(SsaError::Malformed("SSA input"))?
                .push(index);
        }
    }
    let mut values = vec![D::bottom(); graph.values.len()];
    let mut queued = vec![true; values.len()];
    let mut queue: VecDeque<_> = (0..values.len()).collect();
    while let Some(index) = queue.pop_front() {
        budget.spend(1)?;
        queued[index] = false;
        let value = match &graph.values[index] {
            Definition::Initial { .. } => D::unknown(),
            Definition::Phi { inputs, .. } => inputs.iter().try_fold(D::bottom(), |a, p| {
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
                loads
                    .value(source, *site, &points, &values, &mut budget)?
                    .unwrap_or(value)
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
    Ok(values.into_iter().map(D::finish).collect())
}
/// Closed invariants over arbitrary initial registers. Unknown denotes every
/// u64 value. Every Known claim must follow from actual SSA operands/phi edges;
/// optimistic bottom is never accepted as proof of an incoming value.
pub(crate) fn validate_facts<D: Domain>(
    source: &Program,
    graph: &SsaFunction,
    values: &[D],
) -> Result<SsaEvidence, SsaError> {
    validate_facts_with_loads(source, graph, values, &LoadInputs::default())
}
pub(crate) fn validate_facts_with_loads<D: Domain>(
    source: &Program,
    graph: &SsaFunction,
    values: &[D],
    loads: &LoadInputs,
) -> Result<SsaEvidence, SsaError> {
    let evidence = ssa::validate(source, graph)?;
    if values.len() != graph.values.len() {
        return Err(SsaError::Malformed("constant vector"));
    }
    let mut budget = Budget::new();
    let points = point_map(graph);
    let states = values;
    for (index, definition) in graph.values.iter().enumerate() {
        budget.spend(1)?;
        let claim = values[index];
        if !claim.valid() {
            return Err(SsaError::Malformed("invalid abstract fact"));
        }
        if claim == D::unknown() {
            continue;
        }
        let actual = match definition {
            Definition::Initial { .. } => {
                return Err(SsaError::Malformed("constant initial value"));
            }
            Definition::Phi { inputs, .. } => {
                if inputs.is_empty() {
                    return Err(SsaError::Malformed("empty constant phi"));
                }
                inputs.iter().try_fold(D::bottom(), |a, p| {
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
                    states,
                    &mut cursor,
                    &mut budget,
                )?
                .0;
                if cursor != point.reads.len() {
                    return Err(SsaError::Malformed("constant reads"));
                }
                loads
                    .value(source, *site, &points, states, &mut budget)?
                    .unwrap_or(actual)
            }
        };
        if !claim.follows_from(actual) {
            return Err(SsaError::Malformed("unproved constant invariant"));
        }
    }
    Ok(evidence)
}
fn read<D: Domain>(
    expr: &Expr,
    point: &PointValues,
    states: &[D],
    cursor: &mut usize,
) -> Result<D, SsaError> {
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
fn evaluate<D: Domain>(
    expr: &Expr,
    point: &PointValues,
    states: &[D],
    cursor: &mut usize,
    budget: &mut Budget,
) -> Result<(D, bool), SsaError> {
    budget.spend(1)?;
    Ok(match expr {
        Expr::Unary(op, value) => {
            let (value, pure) = evaluate(value, point, states, cursor, budget)?;
            (D::unary(*op, value), pure)
        }
        Expr::Const(n) => (D::constant(*n), true),
        Expr::Register(_) => (read(expr, point, states, cursor)?, true),
        Expr::Load { address, width } => {
            evaluate(address, point, states, cursor, budget)?;
            (D::load(*width), false)
        }
        Expr::Binary(op, a, b) => {
            let (a, ap) = evaluate(a, point, states, cursor, budget)?;
            let (b, bp) = evaluate(b, point, states, cursor, budget)?;
            {
                budget.spend(D::binary_cost(*op, a, b))?;
                (D::binary(*op, a, b), ap && bp)
            }
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            let (c, cp) = evaluate(condition, point, states, cursor, budget)?;
            let (t, tp) = evaluate(taken, point, states, cursor, budget)?;
            let (n, np) = evaluate(not_taken, point, states, cursor, budget)?;
            (D::select(c, t, n), cp && tp && np)
        }
    })
}
fn rewrite<D: Domain>(
    expr: &Expr,
    point: &PointValues,
    values: &[D],
    cursor: &mut usize,
    budget: &mut Budget,
) -> Result<(Expr, D, bool), SsaError> {
    budget.spend(1)?;
    let (mapped, value, pure) = match expr {
        Expr::Unary(op, value) => {
            let (value, state, pure) = rewrite(value, point, values, cursor, budget)?;
            (Expr::unary(*op, value), D::unary(*op, state), pure)
        }
        Expr::Const(n) => (expr.clone(), D::constant(*n), true),
        Expr::Register(_) => (expr.clone(), read(expr, point, values, cursor)?, true),
        Expr::Load { address, width } => {
            let (a, _, _) = rewrite(address, point, values, cursor, budget)?;
            (Expr::load(a, *width), D::load(*width), false)
        }
        Expr::Binary(op, a, b) => {
            let (a, av, ap) = rewrite(a, point, values, cursor, budget)?;
            let (b, bv, bp) = rewrite(b, point, values, cursor, budget)?;
            {
                budget.spend(D::binary_cost(*op, av, bv))?;
                (Expr::binary(*op, a, b), D::binary(*op, av, bv), ap && bp)
            }
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            let (c, cv, cp) = rewrite(condition, point, values, cursor, budget)?;
            let (t, tv, tp) = rewrite(taken, point, values, cursor, budget)?;
            let (n, nv, np) = rewrite(not_taken, point, values, cursor, budget)?;
            (Expr::select(c, t, n), D::select(cv, tv, nv), cp && tp && np)
        }
    };
    Ok((
        if pure && let Some(n) = value.number() {
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
pub(crate) fn validate<D: Domain>(
    source: &Program,
    graph: &SsaFunction,
    values: &[D],
    candidate: &Program,
) -> Result<FactEvidence, SsaError> {
    validate_with_loads(source, graph, values, &LoadInputs::default(), candidate)
}
pub(crate) fn validate_with_loads<D: Domain>(
    source: &Program,
    graph: &SsaFunction,
    values: &[D],
    loads: &LoadInputs,
    candidate: &Program,
) -> Result<FactEvidence, SsaError> {
    let evidence = validate_facts_with_loads(source, graph, values, loads)?;
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
    let states = values;
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
                    replacements += check_expr(a, b, point, states, &mut cursor, &mut budget)?;
                }
                _ => return Err(SsaError::Malformed("constant destination")),
            }
            replacements += check_expr(
                &left.value,
                &right.value,
                point,
                states,
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
            replacements += check_expr(left, right, point, states, &mut cursor, &mut budget)?;
            if cursor != point.reads.len() {
                return Err(SsaError::Malformed("constant control reads"));
            }
        }
    }
    Ok(FactEvidence {
        ssa: evidence,
        constant_values: values.iter().filter(|v| v.number().is_some()).count(),
        replacements,
    })
}
fn check_expr<D: Domain>(
    source: &Expr,
    candidate: &Expr,
    point: &PointValues,
    states: &[D],
    cursor: &mut usize,
    budget: &mut Budget,
) -> Result<usize, SsaError> {
    budget.spend(1)?;
    if let Expr::Const(n) = candidate {
        let (value, pure) = evaluate(source, point, states, cursor, budget)?;
        if !pure || value.number() != Some(*n) {
            return Err(SsaError::Malformed("unproved constant replacement"));
        }
        return Ok(usize::from(source != candidate));
    }
    match (source, candidate) {
        (Expr::Unary(a, x), Expr::Unary(b, y)) if a == b => {
            check_expr(x, y, point, states, cursor, budget)
        }
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
