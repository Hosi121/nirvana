//! Reuse local storage for nonoverlapping lifetimes.
//!
//! Copy/phi groups are kept intact. Their live events are enclosed in intervals
//! in a stable block order, so holes and mutually exclusive paths can only
//! make allocation more conservative. A separate source-based checker accepts
//! the resulting mapping; interval allocation alone supplies no certificate.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap};

use crate::dataflow::ssa::{Definition, SsaError, SsaFunction, ValueId};
use crate::dataflow::ssa_locals::{self, Plan};
use crate::dataflow::value_liveness;
use crate::model::ir::Program;

const MAX_WORK: usize = 8_000_000;

struct Intervals<'a> {
    plan: &'a Plan,
    spans: Vec<Option<(usize, usize)>>,
    event: usize,
    remaining: usize,
}

impl Intervals<'_> {
    fn spend(&mut self, work: usize) -> Result<(), SsaError> {
        self.remaining = self
            .remaining
            .checked_sub(work)
            .ok_or(SsaError::Unavailable("storage reuse work"))?;
        Ok(())
    }

    fn touch(&mut self, value: ValueId) -> Result<(), SsaError> {
        self.spend(1)?;
        let span = &mut self.spans[self.plan.by_value[value.0]];
        match span {
            Some((_, end)) => *end = self.event,
            None => *span = Some((self.event, self.event)),
        }
        Ok(())
    }

    fn set(&mut self, values: &[ValueId]) -> Result<(), SsaError> {
        for &value in values {
            self.touch(value)?;
        }
        Ok(())
    }

    fn next(&mut self) -> Result<(), SsaError> {
        self.spend(1)?;
        self.event += 1;
        Ok(())
    }
}

/// Compact a checked grouping while retaining private initial values.
/// Exceeding a bound returns an error and leaves the input mapping untouched.
pub fn reuse(source: &Program, graph: &SsaFunction, groups: &Plan) -> Result<Plan, SsaError> {
    // Validate before following any supplied indices or allocating by them.
    ssa_locals::validate(source, graph, groups)?;
    let live = value_liveness::analyze(source, graph)?;
    let mut intervals = Intervals {
        plan: groups,
        spans: vec![None; groups.local_count],
        event: 0,
        remaining: MAX_WORK,
    };
    intervals.spend(graph.values.len() + groups.local_count)?;
    let mut private = vec![false; groups.local_count];
    for (id, definition) in graph.values.iter().enumerate() {
        if matches!(definition, Definition::Initial { .. }) {
            private[groups.by_value[id]] = true;
            intervals.touch(ValueId(id))?;
        }
    }
    let blocks: BTreeMap<_, _> = graph.blocks.iter().map(|b| (b.start, b)).collect();
    let mut outgoing: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for edge in &live.edges {
        intervals.spend(1)?;
        if let Some(from) = edge.from {
            outgoing.entry(from).or_default().push(&edge.live);
        } else {
            intervals.set(&edge.live)?;
        }
    }
    // Liveness is ordered by block address, independently of candidate order.
    for block in &live.blocks {
        let raw = blocks[&block.start];
        intervals.next()?;
        intervals.set(&block.live_in)?;
        // Dead phis are still simultaneous definitions.
        intervals.set(&raw.phis)?;
        for (point, definition) in block.points.iter().zip(&raw.points) {
            intervals.next()?;
            intervals.set(&point.before)?;
            intervals.next()?;
            intervals.set(&point.after)?;
            // A dead write still interferes with every live value after it.
            if let Some(value) = definition.definition {
                intervals.touch(value)?;
            }
        }
        intervals.next()?;
        intervals.set(&block.live_out)?;
        if let Some(edges) = outgoing.get(&block.start) {
            for edge in edges {
                intervals.set(edge)?;
            }
        }
    }
    let mut by_group = vec![usize::MAX; groups.local_count];
    let mut local_count = 0;
    for (group, &private) in private.iter().enumerate() {
        if private {
            by_group[group] = local_count;
            local_count += 1;
        }
    }
    let mut ordered = Vec::with_capacity(groups.local_count - local_count);
    for (group, span) in intervals.spans.iter().enumerate() {
        if !private[group] {
            let (start, end) = span.ok_or(SsaError::Malformed("storage group without an event"))?;
            ordered.push((start, end, group));
        }
    }
    let tree_work = groups.local_count.checked_ilog2().unwrap_or(0) as usize + 1;
    intervals.spend(groups.local_count * tree_work * 4)?;
    ordered.sort_unstable();
    let mut active = BinaryHeap::new();
    let mut free = BTreeSet::new();
    for (start, end, group) in ordered {
        while let Some(&Reverse((last, local))) = active.peek() {
            // Values in the same event remain distinct, including dead writes.
            if last >= start {
                break;
            }
            active.pop();
            free.insert(local);
        }
        let local = free.pop_first().unwrap_or_else(|| {
            let local = local_count;
            local_count += 1;
            local
        });
        by_group[group] = local;
        active.push(Reverse((end, local)));
    }
    intervals.spend(graph.values.len())?;
    let candidate = Plan {
        by_value: groups.by_value.iter().map(|&g| by_group[g]).collect(),
        local_count,
    };
    if candidate.local_count > groups.local_count {
        return Err(SsaError::Malformed("storage reuse increased local count"));
    }
    // Recompute real live sets from the source and check the supplied colors.
    // This also checks initial privacy, dense IDs, edge operands and phis.
    ssa_locals::validate(source, graph, &candidate)?;
    Ok(candidate)
}
