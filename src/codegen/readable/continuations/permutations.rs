//! Bounded adjacent-swap proposals. Effect rules and the continuation checker
//! are separate consumers; this module only builds a candidate order.
use super::*;

pub(super) enum Swap {
    Store,
    Local,
}
#[derive(Default)]
pub(super) struct Counts {
    pub stores: usize,
    pub locals: usize,
}

pub(super) fn propose<T>(
    nodes: &[Node],
    prefix: usize,
    tag: &impl Fn(&Node) -> Option<T>,
    inversion: &impl Fn(&T, &T) -> Option<Swap>,
) -> Option<(Vec<Node>, Counts)> {
    fn sort<T>(
        nodes: &[Node],
        tag: &impl Fn(&Node) -> Option<T>,
        inversion: &impl Fn(&T, &T) -> Option<Swap>,
        budget: &mut usize,
        counts: &mut Counts,
    ) -> Option<Vec<Node>> {
        let mut result = Vec::new();
        for node in nodes {
            *budget = budget.checked_sub(1)?;
            let mut node = node.clone();
            if let Node::If {
                taken, not_taken, ..
            } = &mut node
            {
                *taken = sort(taken, tag, inversion, budget, counts)?;
                *not_taken = sort(not_taken, tag, inversion, budget, counts)?;
            }
            let effect = tag(&node);
            result.push((node, effect));
        }
        for end in (1..result.len()).rev() {
            let mut changed = false;
            for i in 0..end {
                *budget = budget.checked_sub(1)?;
                if let (Some(a), Some(b)) = (&result[i].1, &result[i + 1].1)
                    && let Some(kind) = inversion(a, b)
                {
                    match kind {
                        Swap::Store => counts.stores += 1,
                        Swap::Local => counts.locals += 1,
                    }
                    if counts.stores + counts.locals > MAX_ITEMS {
                        return None;
                    }
                    result.swap(i, i + 1);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        Some(result.into_iter().map(|(node, _)| node).collect())
    }
    let mut result = nodes.get(..prefix)?.to_vec();
    let mut counts = Counts::default();
    let mut budget = MAX_WORK;
    result.extend(sort(
        nodes.get(prefix..)?,
        tag,
        inversion,
        &mut budget,
        &mut counts,
    )?);
    Some((result, counts))
}
