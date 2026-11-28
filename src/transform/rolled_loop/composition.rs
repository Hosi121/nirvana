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

// A two-trip loop may use a truth test rather than an integer trip register.
// Preserve the rest of the tested word when proposing its branch fact. The
// incoming cut obligations prove the fact before either side may assume it.
fn truth_relation(condition: &Expr, truth: bool) -> Option<Assignment> {
    let (register, value) = match condition {
        Expr::Register(register) => {
            let value = if truth {
                Expr::select(
                    Expr::binary(BinaryOp::Eq, condition.clone(), Expr::Const(0)),
                    Expr::Const(1),
                    condition.clone(),
                )
            } else {
                Expr::Const(0)
            };
            (*register, value)
        }
        Expr::Binary(BinaryOp::And, a, b) => {
            let (Expr::Register(register), Expr::Const(mask)) = (&**a, &**b) else {
                return None;
            };
            if !mask.is_power_of_two() {
                return None;
            }
            (
                *register,
                Expr::binary(
                    if truth { BinaryOp::Or } else { BinaryOp::And },
                    Expr::Register(*register),
                    Expr::Const(if truth { *mask } else { !mask }),
                ),
            )
        }
        _ => return None,
    };
    Some(Assignment {
        destination: register.into(),
        value,
    })
}

fn trip_invariants(proposal: &Proposal, offset: u64) -> Result<Vec<Assignment>, Error> {
    let group = proposal.lane_group();
    if let Expr::Register(bound) = proposal.trip_limit {
        let &(_, bits) = proposal
            .selectors
            .iter()
            .find(|(reg, _)| *reg == bound)
            .ok_or(Error::Pattern)?;
        if !(1..=4).contains(&bits) || group.offsets.iter().any(|&n| n >= 1u64 << bits) {
            return Err(Error::Pattern);
        }
        return Ok(vec![range(bound, bits, offset)]);
    }
    if group.offsets.len() != 2 || group.offsets != [0, 1] {
        return Err(Error::Pattern);
    }
    if offset == 0 {
        return Ok(vec![]);
    }
    let relation = match &proposal.trip_limit {
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => match (&**taken, &**not_taken) {
            (Expr::Const(1), Expr::Const(0)) => truth_relation(condition, true),
            (Expr::Const(0), Expr::Const(1)) => truth_relation(condition, false),
            _ => None,
        },
        condition => truth_relation(condition, true),
    };
    Ok(vec![relation.ok_or(Error::Pattern)?])
}

pub(super) fn problem(
    proposal: &Proposal,
    prefixed: &extraction::repeat::Prefixed,
    query: &region::Query,
) -> Result<Problem, Error> {
    let discovery = proposal.discovery();
    let group = proposal.lane_group();
    if !discovery.belongs_to(&proposal.source)
        || envelope::locate(&proposal.source, group)? != proposal.envelope
    {
        return Err(Error::Source);
    }
    // Consecutive counter values let the source equality exits establish the
    // lower bound at the next lane. Broader shapes retain the whole-query gate.
    if group.step != 1 || group.offsets.first().is_none_or(|&offset| offset > 1) {
        return Err(Error::Pattern);
    }
    let mut inherited_caps = Vec::new();
    if let Some(invariants) = proposal.before.entry_invariants() {
        let caps = invariants
            .bit_caps(&proposal.padded, proposal.envelope.header)
            .map_err(|_| Error::Source)?;
        let written: BTreeSet<_> = proposal
            .padded
            .instructions()
            .iter()
            .filter(|i| proposal.before.source_to_region().contains_key(&i.address))
            .flat_map(|i| &i.assignments)
            .filter_map(|a| match a.destination {
                Place::Register(reg) => Some(reg.0),
                _ => None,
            })
            .collect();
        inherited_caps = caps
            .into_iter()
            .enumerate()
            .filter(|(reg, bits)| *bits < 64 && !written.contains(reg))
            .map(|(reg, bits)| Assignment {
                destination: Reg(reg).into(),
                value: Expr::binary(
                    BinaryOp::And,
                    Expr::Register(Reg(reg)),
                    Expr::Const((1u64 << bits) - 1),
                ),
            })
            .collect();
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
        // Normalize inherited bounds before dependent SSA equations. Every
        // incoming postcondition still proves these proposed cut relations.
        let mut before_invariants = inherited_caps.clone();
        before_invariants.extend(equations(discovery, pc, proposal.counter));
        before_invariants.extend(trip_invariants(proposal, offset)?);
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
