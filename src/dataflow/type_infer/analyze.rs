use super::*;
use crate::dataflow::ssa::{Budget, Definition, PointValues};
use crate::model::ir::{BinaryOp as B, Control, Expr, Place};
use std::collections::{BTreeMap, VecDeque};

pub(super) fn analyze(source: &Program) -> Option<TypeAnalysis> {
    let graph = SsaFunction::build(source)?;
    let aliases = aliases(source, &graph)?;
    let bits = bounds(source, &graph)?;
    let bounds_evidence = super::check_bounds(source, &graph, &bits).ok()?;
    let accesses = address::collect_with_bounds(source, &graph, &aliases, &bits)?;
    let layouts = super::layout::collect(&accesses)?;
    let mut facts: Vec<_> = bits
        .into_iter()
        .map(|maximum_bits| ValueFacts {
            maximum_bits,
            ..ValueFacts::default()
        })
        .collect();
    uses(source, &graph, &mut facts)?;
    for access in &accesses {
        if let AddressShape::Base { base, index, .. } = access.address {
            facts[base.0].direct_uses.address_base = true;
            if let Some(index) = index {
                facts[index.value.0].direct_uses.address_index = true;
            }
        }
    }
    flow(source, &graph, &mut facts)?;
    Some(TypeAnalysis {
        graph,
        aliases,
        facts,
        accesses,
        layouts,
        bounds_evidence,
    })
}
fn points(graph: &SsaFunction) -> BTreeMap<Site, &PointValues> {
    graph
        .blocks
        .iter()
        .flat_map(|b| &b.points)
        .map(|p| (p.site, p))
        .collect()
}
fn rhs(source: &Program, site: Site) -> Option<&Expr> {
    let i = source
        .instructions()
        .binary_search_by_key(&site.instruction, |i| i.address)
        .ok()?;
    Some(
        &source.instructions()[i]
            .assignments
            .get(site.assignment?)?
            .value,
    )
}
fn aliases(source: &Program, graph: &SsaFunction) -> Option<Vec<ValueId>> {
    crate::dataflow::address_identity::aliases(source, graph, &std::collections::BTreeSet::new())
}
fn dependencies(source: &Program, graph: &SsaFunction) -> Option<Vec<Vec<usize>>> {
    let mut budget = Budget::new();
    let points = points(graph);
    let mut users = vec![vec![]; graph.values.len()];
    for (i, d) in graph.values.iter().enumerate() {
        budget.spend(1).ok()?;
        match d {
            Definition::Initial { .. } => {}
            Definition::Assignment { site, .. } => {
                let _ = rhs(source, *site)?;
                for read in &points.get(site)?.reads {
                    budget.spend(1).ok()?;
                    users[read.value.0].push(i);
                }
            }
            Definition::Phi { inputs, .. } => {
                for input in inputs {
                    budget.spend(1).ok()?;
                    users[input.value.0].push(i);
                }
            }
        }
    }
    Some(users)
}
fn bounds(source: &Program, graph: &SsaFunction) -> Option<Vec<u8>> {
    let mut budget = Budget::new();
    let points = points(graph);
    let users = dependencies(source, graph)?;
    let mut bits = vec![0u8; graph.values.len()];
    let mut queue: VecDeque<_> = (0..bits.len()).collect();
    let mut queued = vec![true; bits.len()];
    while let Some(i) = queue.pop_front() {
        budget.spend(1).ok()?;
        queued[i] = false;
        let value = match &graph.values[i] {
            Definition::Initial { .. } => 64,
            Definition::Phi { inputs, .. } => {
                let mut value = 0;
                for input in inputs {
                    budget.spend(1).ok()?;
                    value = value.max(bits[input.value.0]);
                }
                value
            }
            Definition::Assignment { site, .. } => {
                let point = points.get(site)?;
                let mut cursor = 0;
                let result =
                    expr_bits(rhs(source, *site)?, point, &bits, &mut cursor, &mut budget)?;
                if cursor != point.reads.len() {
                    return None;
                }
                result
            }
        };
        if value > bits[i] {
            bits[i] = value;
            for &user in &users[i] {
                budget.spend(1).ok()?;
                if !queued[user] {
                    queue.push_back(user);
                    queued[user] = true;
                }
            }
        }
    }
    Some(bits)
}
fn expr_bits(
    expr: &Expr,
    point: &PointValues,
    bits: &[u8],
    cursor: &mut usize,
    budget: &mut Budget,
) -> Option<u8> {
    budget.spend(1).ok()?;
    Some(match expr {
        Expr::Unary(op, value) => {
            let bits = expr_bits(value, point, bits, cursor, budget)?;
            op.result_bits(bits)
        }
        Expr::Const(n) => (64 - n.leading_zeros()) as u8,
        Expr::Register(r) => {
            let entry = point.reads.get(*cursor)?;
            *cursor += 1;
            if entry.register != *r {
                return None;
            }
            *bits.get(entry.value.0)?
        }
        Expr::Load { address, width } => {
            expr_bits(address, point, bits, cursor, budget)?;
            width.bits() as u8
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            expr_bits(condition, point, bits, cursor, budget)?;
            expr_bits(taken, point, bits, cursor, budget)?
                .max(expr_bits(not_taken, point, bits, cursor, budget)?)
        }
        Expr::Binary(op, left, right) => {
            let a = expr_bits(left, point, bits, cursor, budget)?;
            let b = expr_bits(right, point, bits, cursor, budget)?;
            match op {
                B::Insert { .. } => {
                    let maximum = |bits: u8| {
                        u64::MAX
                            .checked_shr(64 - u32::from(bits.min(64)))
                            .unwrap_or(0)
                    };
                    (64 - op.evaluate(maximum(a), maximum(b)).leading_zeros()) as u8
                }
                B::Add => {
                    if a == 0 && b == 0 {
                        0
                    } else {
                        a.max(b).saturating_add(1).min(64)
                    }
                }
                B::Sub => {
                    if b == 0 {
                        a
                    } else {
                        64
                    }
                }
                B::Mul => {
                    if a == 0 || b == 0 {
                        0
                    } else {
                        a.saturating_add(b).min(64)
                    }
                }
                B::And => a.min(b),
                B::Or | B::Xor => a.max(b),
                B::Shl => {
                    if a == 0 {
                        0
                    } else if let Expr::Const(n) = **right {
                        a.saturating_add((n & 63) as u8).min(64)
                    } else {
                        64
                    }
                }
                B::AShr if a == 64 => 64,
                B::Shr | B::AShr => {
                    if let Expr::Const(n) = **right {
                        a.saturating_sub((n & 63) as u8)
                    } else {
                        a
                    }
                }
                B::UMulHigh => a.saturating_add(b).saturating_sub(64),
                B::SMulHigh => 64,
                B::UDiv => crate::dataflow::value_width::quotient_bits(
                    a,
                    crate::dataflow::value_width::constant_divisor(right),
                ),
                B::URem | B::SRem => a,
                B::SDiv => 64,
                B::Eq | B::Ne | B::Ult | B::Ule => 1,
            }
        }
    })
}
fn mark(
    expr: &Expr,
    map: &BTreeMap<usize, ValueId>,
    flag: Uses,
    facts: &mut [ValueFacts],
    budget: &mut Budget,
) -> Option<()> {
    let mut pending = vec![expr];
    while let Some(e) = pending.pop() {
        budget.spend(1).ok()?;
        match e {
            Expr::Register(r) => {
                let id = *map.get(&r.0)?;
                facts[id.0].direct_uses = facts[id.0].direct_uses.union(flag);
            }
            Expr::Unary(_, value) => pending.push(value),
            Expr::Binary(_, a, b) => pending.extend([&**b, &**a]),
            Expr::Load { address, .. } => pending.push(address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**not_taken, &**taken, &**condition]),
            Expr::Const(_) => {}
        }
    }
    Some(())
}
fn walk_uses(
    expr: &Expr,
    map: &BTreeMap<usize, ValueId>,
    facts: &mut [ValueFacts],
    budget: &mut Budget,
) -> Option<()> {
    budget.spend(1).ok()?;
    match expr {
        Expr::Unary(_, value) => walk_uses(value, map, facts, budget)?,
        Expr::Binary(op, a, b) => {
            match op {
                B::Ult | B::Ule => {
                    mark(
                        a,
                        map,
                        Uses {
                            unsigned_compare: true,
                            ..Uses::default()
                        },
                        facts,
                        budget,
                    )?;
                    mark(
                        b,
                        map,
                        Uses {
                            unsigned_compare: true,
                            ..Uses::default()
                        },
                        facts,
                        budget,
                    )?;
                }
                B::Shr => mark(
                    a,
                    map,
                    Uses {
                        logical_shift: true,
                        ..Uses::default()
                    },
                    facts,
                    budget,
                )?,
                B::And | B::Or | B::Xor => {
                    mark(
                        a,
                        map,
                        Uses {
                            bitwise: true,
                            ..Uses::default()
                        },
                        facts,
                        budget,
                    )?;
                    mark(
                        b,
                        map,
                        Uses {
                            bitwise: true,
                            ..Uses::default()
                        },
                        facts,
                        budget,
                    )?;
                }
                _ => {}
            }
            if matches!(op, B::Or | B::Xor) {
                budget.spend(crate::transform::signed_expr::MAX_WORK).ok()?;
                if let Some(view) = crate::transform::signed_expr::recognize(expr) {
                    let flag = Uses {
                        signed_compare: true,
                        ..Uses::default()
                    };
                    mark(view.left, map, flag, facts, budget)?;
                    mark(view.right, map, flag, facts, budget)?;
                }
            }
            walk_uses(a, map, facts, budget)?;
            walk_uses(b, map, facts, budget)?;
        }
        Expr::Load { address, .. } => {
            if matches!(**address, Expr::Register(_)) {
                mark(
                    address,
                    map,
                    Uses {
                        address_base: true,
                        ..Uses::default()
                    },
                    facts,
                    budget,
                )?;
            }
            walk_uses(address, map, facts, budget)?;
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            walk_uses(condition, map, facts, budget)?;
            walk_uses(taken, map, facts, budget)?;
            walk_uses(not_taken, map, facts, budget)?;
        }
        _ => {}
    }
    Some(())
}
fn uses(source: &Program, graph: &SsaFunction, facts: &mut [ValueFacts]) -> Option<()> {
    let mut budget = Budget::new();
    let points = points(graph);
    for ins in source.instructions() {
        for (index, a) in ins.assignments.iter().enumerate() {
            let Some(point) = points.get(&Site {
                instruction: ins.address,
                assignment: Some(index),
            }) else {
                continue;
            };
            let map: BTreeMap<_, _> = point
                .reads
                .iter()
                .map(|r| (r.register.0, r.value))
                .collect();
            if let Place::Memory { address, .. } = &a.destination {
                if matches!(address, Expr::Register(_)) {
                    mark(
                        address,
                        &map,
                        Uses {
                            address_base: true,
                            ..Uses::default()
                        },
                        facts,
                        &mut budget,
                    )?;
                }
                walk_uses(address, &map, facts, &mut budget)?;
                mark(
                    &a.value,
                    &map,
                    Uses {
                        stored: true,
                        ..Uses::default()
                    },
                    facts,
                    &mut budget,
                )?;
            }
            walk_uses(&a.value, &map, facts, &mut budget)?;
        }
        if let Control::Branch { condition, .. } | Control::Return(condition) = &ins.control {
            let Some(point) = points.get(&Site {
                instruction: ins.address,
                assignment: None,
            }) else {
                continue;
            };
            let map: BTreeMap<_, _> = point
                .reads
                .iter()
                .map(|r| (r.register.0, r.value))
                .collect();
            walk_uses(condition, &map, facts, &mut budget)?;
            if matches!(ins.control, Control::Return(_)) {
                mark(
                    condition,
                    &map,
                    Uses {
                        returned: true,
                        ..Uses::default()
                    },
                    facts,
                    &mut budget,
                )?;
            }
        }
    }
    Some(())
}
fn flow(source: &Program, graph: &SsaFunction, facts: &mut [ValueFacts]) -> Option<()> {
    let mut budget = Budget::new();
    let points = points(graph);
    let mut edges = vec![vec![]; facts.len()];
    for (i, d) in graph.values.iter().enumerate() {
        budget.spend(1).ok()?;
        let inputs: Vec<_> = match d {
            Definition::Assignment { site, .. }
                if matches!(rhs(source, *site)?, Expr::Register(_)) =>
            {
                vec![points.get(site)?.reads.first()?.value.0]
            }
            Definition::Phi { inputs, .. } => inputs.iter().map(|p| p.value.0).collect(),
            _ => vec![],
        };
        for input in inputs {
            budget.spend(1).ok()?;
            edges[i].push(input);
            edges[input].push(i);
        }
    }
    let mut queue: VecDeque<_> = (0..facts.len()).collect();
    let mut queued = vec![true; facts.len()];
    for fact in &mut *facts {
        fact.flow_uses = fact.direct_uses;
    }
    while let Some(i) = queue.pop_front() {
        budget.spend(1).ok()?;
        queued[i] = false;
        for &to in &edges[i] {
            budget.spend(1).ok()?;
            let next = facts[to].flow_uses.union(facts[i].flow_uses);
            if next != facts[to].flow_uses {
                facts[to].flow_uses = next;
                if !queued[to] {
                    queue.push_back(to);
                    queued[to] = true;
                }
            }
        }
    }
    Some(())
}
