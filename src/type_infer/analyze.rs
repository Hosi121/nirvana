use super::*;
use crate::ir::{BinaryOp as B, Control, Expr, Place};
use crate::ssa::{self, Budget, Definition, PointValues};
use std::collections::{BTreeMap, VecDeque};

pub(super) fn analyze(source: &Program) -> Option<TypeAnalysis> {
    let graph = SsaFunction::build(source)?;
    let aliases = aliases(source, &graph)?;
    let bits = bounds(source, &graph)?;
    if !validate_bounds(source, &graph, &bits) {
        return None;
    }
    let accesses = address::collect_with_bounds(source, &graph, &aliases, &bits)?;
    let layouts = address::layouts(&accesses)?;
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
fn root(parent: &mut [usize], mut id: usize, budget: &mut Budget) -> Option<usize> {
    while parent[id] != id {
        budget.spend(1).ok()?;
        let next = parent[id];
        parent[id] = parent[next];
        id = next;
    }
    Some(id)
}
fn aliases(source: &Program, graph: &SsaFunction) -> Option<Vec<ValueId>> {
    aliases_except(source, graph, &std::collections::BTreeSet::new())
}

pub(super) fn aliases_except(
    source: &Program,
    graph: &SsaFunction,
    opaque: &std::collections::BTreeSet<Site>,
) -> Option<Vec<ValueId>> {
    let mut budget = Budget::new();
    let points = points(graph);
    let mut parent: Vec<_> = (0..graph.values.len()).collect();
    let mut copies = Vec::new();
    for (index, definition) in graph.values.iter().enumerate() {
        budget.spend(1).ok()?;
        if let Definition::Assignment { site, .. } = definition
            && !opaque.contains(site)
            && matches!(rhs(source, *site)?, Expr::Register(_))
        {
            let input = points.get(site)?.reads.first()?.value.0;
            copies.push((index, input));
        }
    }
    loop {
        let mut changed = false;
        for &(a, b) in &copies {
            budget.spend(1).ok()?;
            let a = root(&mut parent, a, &mut budget)?;
            let b = root(&mut parent, b, &mut budget)?;
            if a != b {
                // Keep the copy input as representative; numeric ID order
                // does not imply availability at the address use site.
                parent[a] = b;
                changed = true;
            }
        }
        for (index, definition) in graph.values.iter().enumerate() {
            budget.spend(1).ok()?;
            if let Definition::Phi { inputs, .. } = definition {
                let own = root(&mut parent, index, &mut budget)?;
                let mut other = None;
                let mut ambiguous = false;
                for input in inputs {
                    budget.spend(1).ok()?;
                    let input = root(&mut parent, input.value.0, &mut budget)?;
                    if input == own {
                        continue;
                    }
                    if other.is_some_and(|old| old != input) {
                        ambiguous = true;
                        break;
                    }
                    other = Some(input);
                }
                if !ambiguous && let Some(other) = other {
                    parent[own] = other;
                    changed = true;
                }
            }
        }
        // Compress toward source inputs rather than later copies/entry phis.
        for i in 0..parent.len() {
            budget.spend(1).ok()?;
            let r = root(&mut parent, i, &mut budget)?;
            parent[i] = r;
        }
        if !changed {
            break;
        }
    }
    Some(parent.into_iter().map(ValueId).collect())
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
pub(super) fn validate_bounds(source: &Program, graph: &SsaFunction, bits: &[u8]) -> bool {
    fn check(source: &Program, graph: &SsaFunction, bits: &[u8]) -> Option<()> {
        ssa::validate(source, graph).ok()?;
        if bits.len() != graph.values.len() || bits.iter().any(|&n| n > 64) {
            return None;
        }
        let mut budget = Budget::new();
        let points = points(graph);
        for (i, d) in graph.values.iter().enumerate() {
            budget.spend(1).ok()?;
            let required = match d {
                Definition::Initial { .. } => 64,
                Definition::Phi { inputs, .. } => {
                    let mut maximum = 0;
                    for input in inputs {
                        budget.spend(1).ok()?;
                        maximum = maximum.max(bits[input.value.0]);
                    }
                    maximum
                }
                Definition::Assignment { site, .. } => {
                    let point = points.get(site)?;
                    let mut cursor = 0;
                    let b = expr_bits(rhs(source, *site)?, point, bits, &mut cursor, &mut budget)?;
                    if cursor != point.reads.len() {
                        return None;
                    }
                    b
                }
            };
            if required > bits[i] {
                return None;
            }
        }
        Some(())
    }
    check(source, graph, bits).is_some()
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
                B::Shr => {
                    if let Expr::Const(n) = **right {
                        a.saturating_sub((n & 63) as u8)
                    } else {
                        a
                    }
                }
                B::UMulHigh => a.saturating_add(b).saturating_sub(64),
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
                budget.spend(crate::signed_expr::MAX_WORK).ok()?;
                if let Some(view) = crate::signed_expr::recognize(expr) {
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
