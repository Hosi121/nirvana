//! Conservative storage groups for source-bound register SSA values.
//!
//! Only phi operands/results and literal register-copy assignments introduce
//! affinities. Simultaneous live values, dead writes and simultaneous phi
//! definitions remain distinct. Initial values have permanently private locals.
//! The producer stores sparse event memberships instead of a value-pair graph;
//! the checker independently inspects the proposed mapping at each live set.
use crate::dataflow::ssa::{Definition, PointValues, Site, SsaError, SsaFunction, ValueId};
use crate::dataflow::value_liveness;
use crate::model::ir::{Expr, Program};
use std::collections::{BTreeMap, BTreeSet};

pub const MAX_MEMBERSHIPS: usize = 1_000_000;
pub const MAX_WORK: usize = 8_000_000;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Plan {
    pub by_value: Vec<usize>,
    pub local_count: usize,
}

struct Budget {
    work: usize,
    members: usize,
}
impl Budget {
    fn new() -> Self {
        Self {
            work: MAX_WORK,
            members: 0,
        }
    }
    fn spend(&mut self, amount: usize) -> Result<(), SsaError> {
        self.work = self
            .work
            .checked_sub(amount)
            .ok_or(SsaError::Unavailable("local grouping work"))?;
        Ok(())
    }
    fn reserve(&mut self, amount: usize) -> Result<(), SsaError> {
        self.members = self
            .members
            .checked_add(amount)
            .filter(|&n| n <= MAX_MEMBERSHIPS)
            .ok_or(SsaError::Unavailable("local grouping memberships"))?;
        Ok(())
    }
}
fn tree_work(length: usize) -> usize {
    length.checked_ilog2().unwrap_or(0) as usize + 1
}

struct Groups {
    parent: Vec<usize>,
    events: Vec<BTreeSet<usize>>,
    next_event: usize,
}
impl Groups {
    fn new(count: usize, budget: &mut Budget) -> Result<Self, SsaError> {
        budget.spend(count)?;
        Ok(Self {
            parent: (0..count).collect(),
            events: (0..count).map(|_| BTreeSet::new()).collect(),
            next_event: 0,
        })
    }
    fn event(&mut self, budget: &mut Budget) -> Result<usize, SsaError> {
        budget.spend(1)?;
        let event = self.next_event;
        self.next_event += 1;
        Ok(event)
    }
    // Each value is listed at most once per event by the caller. Membership
    // accounting and insertion work are checked before allocating a tree node.
    fn member(
        &mut self,
        event: usize,
        value: ValueId,
        budget: &mut Budget,
    ) -> Result<(), SsaError> {
        budget.spend(tree_work(self.events[value.0].len()))?;
        budget.reserve(1)?;
        self.events[value.0].insert(event);
        Ok(())
    }
    fn live_event(&mut self, live: &[ValueId], budget: &mut Budget) -> Result<usize, SsaError> {
        let event = self.event(budget)?;
        for &value in live {
            self.member(event, value, budget)?;
        }
        Ok(event)
    }
    fn root(&mut self, mut value: usize, budget: &mut Budget) -> Result<usize, SsaError> {
        let mut root = value;
        while self.parent[root] != root {
            budget.spend(1)?;
            root = self.parent[root];
        }
        while self.parent[value] != root {
            budget.spend(1)?;
            let next = self.parent[value];
            self.parent[value] = root;
            value = next;
        }
        Ok(root)
    }
    fn merge(&mut self, a: usize, b: usize, budget: &mut Budget) -> Result<(), SsaError> {
        budget.spend(1)?;
        let mut a = self.root(a, budget)?;
        let mut b = self.root(b, budget)?;
        if a == b {
            return Ok(());
        }
        // Move smaller memberships into larger memberships; an event is never
        // copied and no successful union increases retained memberships.
        if (self.events[a].len(), std::cmp::Reverse(a))
            < (self.events[b].len(), std::cmp::Reverse(b))
        {
            std::mem::swap(&mut a, &mut b);
        }
        // A collision often ends the read-only search immediately. Charge
        // each actual lookup; reserve mutation work separately below.
        for token in &self.events[b] {
            budget.spend(tree_work(self.events[a].len()))?;
            if self.events[a].contains(token) {
                return Ok(());
            }
        }
        // Charge all insertion work before moving any memberships.
        budget.spend(
            self.events[b]
                .len()
                .checked_mul(tree_work(self.events[a].len() + self.events[b].len()))
                .ok_or(SsaError::Unavailable("local grouping work"))?,
        )?;
        let moved = std::mem::take(&mut self.events[b]);
        self.events[a].extend(moved);
        self.parent[b] = a;
        Ok(())
    }
}

/// Produce deterministic dense locals, with IDs ordered by first ValueId.
/// Validation and checked liveness precede all value-indexed allocations.
pub fn analyze(
    source: &Program,
    graph: &SsaFunction,
    excluded_copies: &BTreeSet<Site>,
) -> Result<Plan, SsaError> {
    let live = value_liveness::analyze(source, graph)?;
    let mut budget = Budget::new();
    let mut groups = Groups::new(graph.values.len(), &mut budget)?;
    budget.spend(graph.blocks.len() * tree_work(graph.blocks.len()))?;
    let blocks: BTreeMap<_, _> = graph.blocks.iter().map(|b| (b.start, b)).collect();
    budget.spend(graph.values.len())?;
    let mut points: Vec<Option<&PointValues>> = vec![None; graph.values.len()];
    for block in &live.blocks {
        let raw = blocks[&block.start];
        // All phis are real, simultaneous writes, including unused phis.
        let event = groups.live_event(&block.live_in, &mut budget)?;
        for &phi in &raw.phis {
            budget.spend(tree_work(block.live_in.len()))?;
            if block.live_in.binary_search(&phi).is_err() {
                groups.member(event, phi, &mut budget)?;
            }
        }
        groups.live_event(&block.live_out, &mut budget)?;
        for (point, raw_point) in block.points.iter().zip(&raw.points) {
            budget.spend(1)?;
            groups.live_event(&point.before, &mut budget)?;
            let event = groups.live_event(&point.after, &mut budget)?;
            if let Some(value) = raw_point.definition {
                points[value.0] = Some(raw_point);
                budget.spend(tree_work(point.after.len()))?;
                if point.after.binary_search(&value).is_err() {
                    groups.member(event, value, &mut budget)?;
                }
            }
        }
    }
    for edge in &live.edges {
        groups.live_event(&edge.live, &mut budget)?;
    }
    // Definition order is stable under block/phi/input-list permutations.
    for register_copies in [true, false] {
        for (index, definition) in graph.values.iter().enumerate() {
            budget.spend(1)?;
            match definition {
                Definition::Phi { inputs, .. } if !register_copies => {
                    budget.spend(inputs.len() * tree_work(inputs.len()))?;
                    let mut ordered: Vec<_> = inputs.iter().collect();
                    ordered.sort_unstable_by_key(|input| input.predecessor);
                    for input in ordered {
                        budget.spend(1)?;
                        if !matches!(graph.values[input.value.0], Definition::Initial { .. }) {
                            groups.merge(index, input.value.0, &mut budget)?;
                        }
                    }
                }
                Definition::Assignment { site, .. } if register_copies => {
                    budget.spend(tree_work(excluded_copies.len()))?;
                    if excluded_copies.contains(site) {
                        continue;
                    }
                    budget.spend(tree_work(source.instructions().len()))?;
                    let instruction = source
                        .instructions()
                        .binary_search_by_key(&site.instruction, |i| i.address)
                        .expect("SSA checked source site");
                    let assignment = &source.instructions()[instruction].assignments
                        [site.assignment.expect("SSA assignment site")];
                    if let Expr::Register(_) = assignment.value {
                        let read = points[index].expect("SSA assignment point").reads[0].value;
                        if !matches!(graph.values[read.0], Definition::Initial { .. }) {
                            groups.merge(index, read.0, &mut budget)?;
                        }
                    }
                }
                _ => {}
            }
        }
    }
    budget.spend(graph.values.len() * 2)?;
    let mut locals = vec![None; graph.values.len()];
    let mut plan = Plan {
        by_value: Vec::with_capacity(graph.values.len()),
        local_count: 0,
    };
    for value in 0..graph.values.len() {
        let root = groups.root(value, &mut budget)?;
        let local = *locals[root].get_or_insert_with(|| {
            let local = plan.local_count;
            plan.local_count += 1;
            local
        });
        plan.by_value.push(local);
    }
    // Release producer memberships before recomputing the checking evidence.
    drop(groups);
    drop(points);
    drop(blocks);
    drop(live);
    // The independent public checker is also the final acceptance boundary.
    validate(source, graph, &plan)?;
    Ok(plan)
}

struct LocalMarks {
    seen: Vec<usize>,
    generation: usize,
}
impl LocalMarks {
    fn new(count: usize) -> Self {
        Self {
            seen: vec![0; count],
            generation: 0,
        }
    }
    fn begin(&mut self) {
        // At most two events per checked source point plus bounded blocks/edges.
        self.generation += 1;
    }
    fn insert(&mut self, local: usize, budget: &mut Budget) -> Result<(), SsaError> {
        budget.spend(1)?;
        if self.seen[local] == self.generation {
            return Err(SsaError::Malformed("local live-value collision"));
        }
        self.seen[local] = self.generation;
        Ok(())
    }
    fn check_set(
        &mut self,
        values: &[ValueId],
        plan: &Plan,
        budget: &mut Budget,
    ) -> Result<(), SsaError> {
        self.begin();
        for value in values {
            self.insert(plan.by_value[value.0], budget)?;
        }
        Ok(())
    }
}

/// Check a supplied dense mapping independently of affinity/group production.
/// Other safe groupings are accepted, but every Initial remains private.
pub fn validate(source: &Program, graph: &SsaFunction, candidate: &Plan) -> Result<(), SsaError> {
    let live = value_liveness::analyze(source, graph)?;
    if candidate.by_value.len() != graph.values.len()
        || candidate.local_count > graph.values.len()
        || (candidate.local_count == 0 && !graph.values.is_empty())
    {
        return Err(SsaError::Malformed("local map shape"));
    }
    let mut budget = Budget::new();
    budget.spend(graph.values.len() + candidate.local_count)?;
    let mut counts = vec![0usize; candidate.local_count];
    for &local in &candidate.by_value {
        budget.spend(1)?;
        let count = counts
            .get_mut(local)
            .ok_or(SsaError::Malformed("local index"))?;
        *count += 1;
    }
    if counts.contains(&0) {
        return Err(SsaError::Malformed("non-dense local map"));
    }
    for (value, definition) in graph.values.iter().enumerate() {
        budget.spend(1)?;
        if matches!(definition, Definition::Initial { .. })
            && counts[candidate.by_value[value]] != 1
        {
            return Err(SsaError::Malformed("initial local is not private"));
        }
    }
    budget.spend(graph.blocks.len() * tree_work(graph.blocks.len()) + candidate.local_count)?;
    let blocks: BTreeMap<_, _> = graph.blocks.iter().map(|b| (b.start, b)).collect();
    let mut marks = LocalMarks::new(candidate.local_count);
    for block in &live.blocks {
        let raw = blocks[&block.start];
        marks.check_set(&block.live_in, candidate, &mut budget)?;
        marks.check_set(&block.live_out, candidate, &mut budget)?;
        // Directly check simultaneous writes, even if neither phi is live.
        marks.begin();
        for phi in &raw.phis {
            marks.insert(candidate.by_value[phi.0], &mut budget)?;
        }
        for value in &block.live_in {
            budget.spend(1)?;
            if !matches!(graph.values[value.0], Definition::Phi { block: owner, .. } if owner == block.start)
            {
                marks.insert(candidate.by_value[value.0], &mut budget)?;
            }
        }
        for (point, raw_point) in block.points.iter().zip(&raw.points) {
            marks.check_set(&point.before, candidate, &mut budget)?;
            marks.check_set(&point.after, candidate, &mut budget)?;
            if let Some(definition) = raw_point.definition {
                for &value in &point.after {
                    budget.spend(1)?;
                    if value != definition
                        && candidate.by_value[value.0] == candidate.by_value[definition.0]
                    {
                        return Err(SsaError::Malformed("local definition clobbers live value"));
                    }
                }
            }
        }
    }
    for edge in &live.edges {
        marks.check_set(&edge.live, candidate, &mut budget)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn membership_and_union_budgets_precede_mutation() {
        let mut budget = Budget::new();
        let mut groups = Groups::new(2, &mut budget).unwrap();
        budget.members = MAX_MEMBERSHIPS;
        assert!(groups.member(0, ValueId(0), &mut budget).is_err());
        assert!(groups.events[0].is_empty());
        budget.members = 0;
        groups.member(0, ValueId(0), &mut budget).unwrap();
        groups.member(1, ValueId(1), &mut budget).unwrap();
        budget.work = 1;
        assert!(groups.merge(0, 1, &mut budget).is_err());
        assert_eq!(groups.parent, [0, 1]);
        assert_eq!(groups.events[0], BTreeSet::from([0]));
        assert_eq!(groups.events[1], BTreeSet::from([1]));
    }
}
