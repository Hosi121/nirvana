use crate::dataflow::ssa::{Budget, Definition, PointValues, Site, SsaFunction, ValueId};
use crate::model::ir::{Expr, Program};
use std::collections::BTreeMap;
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
pub(super) fn collect(
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
