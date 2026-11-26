//! Anti-unification keeps fixed literals; varying positions share an exact series.
use super::*;

fn unify(
    terms: &[&PatternExpr],
    offsets: &mut Option<Vec<u64>>,
    budget: &mut Budget,
) -> Option<PatternExpr> {
    budget.spend(terms.len() + 1)?;
    budget.node()?;
    Some(match *terms.first()? {
        PatternExpr::Constant(value) => {
            let values: Vec<_> = terms
                .iter()
                .map(|term| {
                    if let PatternExpr::Constant(value) = term {
                        Some(*value)
                    } else {
                        None
                    }
                })
                .collect::<Option<_>>()?;
            if values.iter().all(|next| next == value) {
                PatternExpr::Constant(*value)
            } else {
                if let Some(previous) = offsets {
                    if previous != &values {
                        return None;
                    }
                } else {
                    *offsets = Some(values);
                }
                PatternExpr::Lane
            }
        }
        PatternExpr::Value(value) => {
            if terms
                .iter()
                .any(|term| !matches!(term, PatternExpr::Value(next) if next == value))
            {
                return None;
            }
            PatternExpr::Value(*value)
        }
        PatternExpr::Accumulator => {
            if terms
                .iter()
                .any(|term| !matches!(term, PatternExpr::Accumulator))
            {
                return None;
            }
            PatternExpr::Accumulator
        }
        PatternExpr::Loaded => {
            if terms
                .iter()
                .any(|term| !matches!(term, PatternExpr::Loaded))
            {
                return None;
            }
            PatternExpr::Loaded
        }
        PatternExpr::Unary(op, _) => {
            let values: Vec<_> = terms
                .iter()
                .map(|term| {
                    if let PatternExpr::Unary(next, value) = term {
                        (op == next).then_some(&**value)
                    } else {
                        None
                    }
                })
                .collect::<Option<_>>()?;
            PatternExpr::Unary(*op, Box::new(unify(&values, offsets, budget)?))
        }
        PatternExpr::Binary(op, _, _) => {
            let pairs: Vec<_> = terms
                .iter()
                .map(|term| {
                    if let PatternExpr::Binary(next, a, b) = term {
                        (op == next).then_some((&**a, &**b))
                    } else {
                        None
                    }
                })
                .collect::<Option<_>>()?;
            let left: Vec<_> = pairs.iter().map(|pair| pair.0).collect();
            let right: Vec<_> = pairs.iter().map(|pair| pair.1).collect();
            PatternExpr::Binary(
                *op,
                Box::new(unify(&left, offsets, budget)?),
                Box::new(unify(&right, offsets, budget)?),
            )
        }
        PatternExpr::Select(_, _, _) => {
            let triples: Vec<_> = terms
                .iter()
                .map(|term| {
                    if let PatternExpr::Select(a, b, c) = term {
                        Some((&**a, &**b, &**c))
                    } else {
                        None
                    }
                })
                .collect::<Option<_>>()?;
            PatternExpr::Select(
                Box::new(unify(
                    &triples.iter().map(|v| v.0).collect::<Vec<_>>(),
                    offsets,
                    budget,
                )?),
                Box::new(unify(
                    &triples.iter().map(|v| v.1).collect::<Vec<_>>(),
                    offsets,
                    budget,
                )?),
                Box::new(unify(
                    &triples.iter().map(|v| v.2).collect::<Vec<_>>(),
                    offsets,
                    budget,
                )?),
            )
        }
        PatternExpr::Lane => return None,
    })
}

fn propose(kernels: &[&Kernel], budget: &mut Budget) -> Option<LaneGroup> {
    let first = kernels.first()?;
    if kernels.iter().any(|k| {
        k.accumulator != first.accumulator
            || k.load_width != first.load_width
            || k.store_width != first.store_width
    }) {
        return None;
    }
    let mut offsets = None;
    let load_address = unify(
        &kernels.iter().map(|k| &k.load_address).collect::<Vec<_>>(),
        &mut offsets,
        budget,
    )?;
    let update_expression = unify(
        &kernels
            .iter()
            .map(|k| &k.update_expression)
            .collect::<Vec<_>>(),
        &mut offsets,
        budget,
    )?;
    let store_address = unify(
        &kernels.iter().map(|k| &k.store_address).collect::<Vec<_>>(),
        &mut offsets,
        budget,
    )?;
    let offsets = offsets?;
    let step = offsets[1].wrapping_sub(offsets[0]);
    if step == 0
        || offsets
            .windows(2)
            .any(|values| values[1].wrapping_sub(values[0]) != step)
    {
        return None;
    }
    Some(LaneGroup {
        kernels: kernels.iter().map(|kernel| (*kernel).clone()).collect(),
        offsets,
        step,
        load_address,
        update_expression,
        store_address,
    })
}

pub(super) fn discover(kernels: &[Kernel], budget: &mut Budget) -> Vec<LaneGroup> {
    let mut clusters: Vec<Vec<&Kernel>> = Vec::new();
    for kernel in kernels {
        let mut placed = false;
        for cluster in &mut clusters {
            cluster.push(kernel);
            if propose(cluster, budget).is_some() {
                placed = true;
                break;
            }
            cluster.pop();
        }
        if !placed {
            clusters.push(vec![kernel]);
        }
    }
    clusters
        .into_iter()
        .filter(|group| group.len() >= MIN_LANES)
        .filter_map(|group| propose(&group, budget))
        .collect()
}
