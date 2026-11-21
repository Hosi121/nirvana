//! A reachable block executes at most once exactly when it belongs to no
//! directed cycle. Iterative SCC passes include irreducible and self cycles.
use super::{Budget, Program};
use crate::control_flow::cfg::Target;

pub(super) fn blocks(source: &Program, budget: &mut Budget) -> Option<Vec<bool>> {
    let cfg = source.cfg();
    let mut edges = vec![Vec::new(); cfg.blocks().len()];
    for id in cfg.reachable_blocks() {
        for edge in &cfg.block(id).successors {
            budget.spend(1).ok()?;
            let Target::Block(to) = edge.target else {
                return None;
            };
            edges[id.index()].push(to.index());
        }
    }
    classify(&edges, cfg.entry().index(), budget)
}
fn classify(edges: &[Vec<usize>], entry: usize, budget: &mut Budget) -> Option<Vec<bool>> {
    let mut seen = vec![false; edges.len()];
    let mut reverse = vec![Vec::new(); edges.len()];
    let mut finish = Vec::new();
    let mut pending = vec![(entry, 0)];
    seen[entry] = true;
    while let Some((node, next)) = pending.last_mut() {
        budget.spend(1).ok()?;
        if let Some(&to) = edges[*node].get(*next) {
            *next += 1;
            reverse[to].push(*node);
            if !std::mem::replace(&mut seen[to], true) {
                pending.push((to, 0));
            }
        } else {
            finish.push(*node);
            pending.pop();
        }
    }
    let mut assigned = vec![false; edges.len()];
    let mut result = vec![false; edges.len()];
    for root in finish.into_iter().rev() {
        budget.spend(1).ok()?;
        if assigned[root] {
            continue;
        }
        assigned[root] = true;
        let mut component = vec![root];
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            budget.spend(1).ok()?;
            for &to in &reverse[node] {
                budget.spend(1).ok()?;
                if !std::mem::replace(&mut assigned[to], true) {
                    component.push(to);
                    pending.push(to);
                }
            }
        }
        if component.len() == 1 && !edges[root].contains(&root) {
            result[root] = true;
        }
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn all_four_node_graphs_match_independent_positive_length_reachability() {
        for mask in 0..1u32 << 16 {
            let mut edges = vec![Vec::new(); 4];
            let mut paths = [[false; 4]; 4];
            for (from, row) in paths.iter_mut().enumerate() {
                for (to, path) in row.iter_mut().enumerate() {
                    if mask & (1 << (from * 4 + to)) != 0 {
                        edges[from].push(to);
                        *path = true;
                    }
                }
            }
            for via in 0..4 {
                for from in 0..4 {
                    for to in 0..4 {
                        paths[from][to] |= paths[from][via] && paths[via][to];
                    }
                }
            }
            let actual = classify(&edges, 0, &mut Budget::new()).unwrap();
            for node in 0..4 {
                assert_eq!(
                    actual[node],
                    (node == 0 || paths[0][node]) && !paths[node][node],
                    "graph {mask}, node {node}"
                );
            }
        }
    }
    #[test]
    fn duplicate_edges_and_long_iterative_graphs_preserve_single_visits() {
        let edges = vec![vec![1, 1], vec![2], vec![1, 3, 3], vec![], vec![4]];
        assert_eq!(
            classify(&edges, 0, &mut Budget::new()).unwrap(),
            [true, false, false, true, false]
        );
        let mut edges: Vec<_> = (1..2048).map(|to| vec![to]).collect();
        edges.push(vec![]);
        assert!(
            classify(&edges, 0, &mut Budget::new())
                .unwrap()
                .into_iter()
                .all(|single| single)
        );
        edges[2047].push(0);
        assert!(
            classify(&edges, 0, &mut Budget::new())
                .unwrap()
                .into_iter()
                .all(|single| !single)
        );
    }
}
