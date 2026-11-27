//! Lane cuts and candidate relations; the independent composition gate accepts.
use super::*;
use crate::dataflow::{
    ssa::{Definition, SsaFunction},
    value_liveness,
};
use region::composition::{Cut, Problem};

fn live_inputs(source: &Program, pc: u64) -> Result<BTreeSet<usize>, Error> {
    let reentered = Program::new(pc, source.register_count(), source.instructions().to_vec())
        .map_err(|_| Error::Source)?;
    let graph = SsaFunction::build(&reentered).ok_or(Error::Limit)?;
    let live = value_liveness::analyze(&reentered, &graph).map_err(|_| Error::Limit)?;
    let inputs = live
        .edges
        .iter()
        .find(|e| e.from.is_none() && e.to == pc)
        .ok_or(Error::Source)?;
    Ok(inputs
        .live
        .iter()
        .map(|id| match graph.values[id.0] {
            Definition::Initial { register }
            | Definition::Assignment { register, .. }
            | Definition::Phi { register, .. } => register.0,
        })
        .collect())
}

fn dependencies(expression: &Expr) -> Option<BTreeSet<usize>> {
    let mut pending = vec![expression];
    let mut read = BTreeSet::new();
    let mut nodes = 0usize;
    while let Some(value) = pending.pop() {
        nodes += 1;
        if nodes > 32 {
            return None;
        }
        match value {
            Expr::Register(Reg(id)) => {
                read.insert(*id);
            }
            Expr::Load { .. } => return None,
            Expr::Unary(_, value) => pending.push(value),
            Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            Expr::Const(_) => {}
        }
    }
    Some(read)
}

// Expand source SSA definitions only while their storage still denotes entry
// values. These are proposals: false equations fail the incoming postconditions.
fn equations(discovery: &Discovery, entry: u64, counter: Reg) -> Vec<Assignment> {
    let Some(block) = discovery.ssa().blocks.iter().find(|b| b.start == entry) else {
        return vec![];
    };
    let mut written = BTreeSet::new();
    let mut candidates = BTreeMap::new();
    for point in &block.points {
        for read in &point.reads {
            if written.contains(&read.register.0) {
                continue;
            }
            let Some(pattern) = discovery.register_expression(point.site, read.register) else {
                continue;
            };
            let Ok(value) = expressions::instantiate(&pattern, discovery, &[point.site], counter)
            else {
                continue;
            };
            let Some(uses) = dependencies(&value) else {
                continue;
            };
            if uses.contains(&read.register.0) || !uses.is_disjoint(&written) {
                continue;
            }
            candidates.entry(read.register.0).or_insert(value);
        }
        if let Some(id) = point.definition
            && let Definition::Assignment { register, .. } = discovery.ssa().values[id.0]
        {
            written.insert(register.0);
        }
    }
    candidates
        .into_iter()
        .take(8)
        .map(|(id, value)| Assignment {
            destination: Reg(id).into(),
            value,
        })
        .collect()
}

fn range(register: Reg, bits: u8, low: u64) -> Assignment {
    let masked = Expr::binary(
        BinaryOp::And,
        Expr::Register(register),
        Expr::Const((1u64 << bits) - 1),
    );
    Assignment {
        destination: register.into(),
        value: Expr::select(
            Expr::binary(BinaryOp::Ult, masked.clone(), Expr::Const(low)),
            Expr::Const(low),
            masked,
        ),
    }
}

pub(super) fn problem(
    proposal: &Proposal,
    prefixed: &extraction::repeat::Prefixed,
    query: &region::Query,
) -> Result<Problem, Error> {
    let discovery = lane_patterns::discover(&proposal.source).map_err(|_| Error::Pattern)?;
    let group = discovery
        .groups()
        .iter()
        .find(|group| {
            envelope::locate(&proposal.source, group).is_ok_and(|e| e == proposal.envelope)
        })
        .ok_or(Error::Pattern)?;
    // Consecutive counter values let the source equality exits establish the
    // lower bound at the next lane. Broader shapes retain the whole-query gate.
    if group.step != 1 || group.offsets.first() != Some(&1) {
        return Err(Error::Pattern);
    }
    let &(bound, bits) = proposal.selectors.first().ok_or(Error::Pattern)?;
    if !(1..=4).contains(&bits) || group.offsets.iter().any(|&n| n >= 1u64 << bits) {
        return Err(Error::Pattern);
    }
    let after = prefixed.round_entries();
    if after.len() != proposal.envelope.lane_entries.len() || after.len() != group.offsets.len() {
        return Err(Error::Projection);
    }
    let mut cuts = vec![Cut {
        before: proposal
            .before
            .program()
            .cfg()
            .block(proposal.before.program().cfg().entry())
            .start,
        after: prefixed
            .program()
            .cfg()
            .block(prefixed.program().cfg().entry())
            .start,
        shared: query.shared_inputs().to_vec(),
        before_invariants: vec![],
        after_invariants: vec![],
    }];
    for ((&pc, after), &offset) in proposal
        .envelope
        .lane_entries
        .iter()
        .zip(after)
        .zip(&group.offsets)
    {
        let mut shared = live_inputs(&proposal.source, pc)?;
        shared.extend(live_inputs(&proposal.program, proposal.feedback)?);
        shared.remove(&proposal.counter.0);
        shared.insert(proposal.before.return_register().0);
        let mut before_invariants = equations(&discovery, pc, proposal.counter);
        before_invariants.push(range(bound, bits, offset));
        let mut after_invariants = before_invariants.clone();
        after_invariants.push(Assignment {
            destination: proposal.counter.into(),
            value: Expr::Const(offset),
        });
        cuts.push(Cut {
            before: *proposal
                .before
                .source_to_region()
                .get(&pc)
                .ok_or(Error::Projection)?,
            after,
            shared: shared.into_iter().map(Reg).collect(),
            before_invariants,
            after_invariants,
        });
    }
    Problem::new(query, &cuts).map_err(|error| match error {
        region::composition::BuildError::Limit
        | region::composition::BuildError::Region(region::Error::Limit) => Error::Limit,
        _ => Error::Projection,
    })
}
