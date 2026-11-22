//! Saved-word equalities across register copies, extractions and phi edges.
//!
//! Pending is only a solver state. Published claims are closed invariants:
//! every incoming value must already name the same saved slice. The checker
//! reads the original definitions and never trusts a partially solved join.
use super::analyze::Context;
use super::*;
#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Eq, PartialEq)]
enum Fact {
    Pending,
    Slice(Key),
    Unknown,
}
impl Fact {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Pending, value) | (value, Self::Pending) => value,
            (a, b) if a == b => a,
            _ => Self::Unknown,
        }
    }
}
enum Transfer {
    Unknown,
    Seed(Key),
    Inputs(Vec<ValueId>),
    Extract(ValueId, u8, Width),
}
fn project(key: Key, start: u8, width: Width) -> Option<Key> {
    if start == 0 && width.bits() >= key.width.bits() {
        // The input already has zeros above its observed slice.
        return Some(key);
    }
    (u32::from(start) + width.bits() <= key.width.bits()).then_some(Key {
        value: key.value,
        start: key.start.checked_add(start)?,
        width,
    })
}
fn invalid(message: &'static str) -> SsaError {
    SsaError::Malformed(message)
}
fn reloads(
    context: &Context<'_>,
    proofs: &[LoadProof],
) -> Result<BTreeMap<ValueId, Key>, SsaError> {
    let mut seeds = BTreeMap::new();
    for proof in proofs {
        let value = context
            .point(proof.site)
            .and_then(|point| point.definition)
            .ok_or(invalid("saved slice seed definition"))?;
        if seeds.insert(value, proof.key).is_some() {
            return Err(invalid("saved slice duplicate seed"));
        }
    }
    Ok(seeds)
}
fn seeds(context: &Context<'_>, proofs: &[LoadProof]) -> Result<BTreeMap<ValueId, Key>, SsaError> {
    let mut seeds = reloads(context, proofs)?;
    for proof in proofs {
        if let SavedValue::Register(value) = proof.key.value
            && !matches!(
                context.graph.values.get(value.0),
                Some(Definition::Phi { .. })
            )
            && context.capture(proof.key.value).is_some()
        {
            // Name the captured source word itself. This identity is not a
            // constant claim about its arbitrary bits or an optimistic phi.
            seeds.entry(value).or_insert(Key {
                value: proof.key.value,
                start: 0,
                width: Width::U64,
            });
        }
    }
    Ok(seeds)
}
pub(super) fn solve(
    context: &Context<'_>,
    proofs: &[LoadProof],
) -> Result<Vec<Option<Key>>, SsaError> {
    let seeds = seeds(context, proofs)?;
    let mut budget = Budget::new();
    let mut transfers = Vec::with_capacity(context.graph.values.len());
    let mut users = vec![Vec::new(); context.graph.values.len()];
    for (id, definition) in context.graph.values.iter().enumerate() {
        budget.spend(1)?;
        let transfer = if let Some(&key) = seeds.get(&ValueId(id)) {
            Transfer::Seed(key)
        } else {
            match definition {
                Definition::Phi { inputs, .. } => {
                    Transfer::Inputs(inputs.iter().map(|input| input.value).collect())
                }
                Definition::Assignment { site, .. }
                    if matches!(
                        context.assignment(*site).map(|a| &a.value),
                        Some(Expr::Register(_))
                    ) =>
                {
                    let point = context
                        .point(*site)
                        .ok_or(invalid("saved slice copy point"))?;
                    Transfer::Inputs(point.reads.iter().map(|read| read.value).collect())
                }
                Definition::Assignment { site, .. } => {
                    match context.assignment(*site).map(|a| &a.value) {
                        Some(Expr::Unary(UnaryOp::Extract { start, width }, value))
                            if matches!(&**value, Expr::Register(_)) =>
                        {
                            let point = context
                                .point(*site)
                                .ok_or(invalid("saved slice extraction point"))?;
                            Transfer::Extract(
                                point
                                    .reads
                                    .first()
                                    .ok_or(invalid("saved slice extraction input"))?
                                    .value,
                                *start,
                                *width,
                            )
                        }
                        _ => Transfer::Unknown,
                    }
                }
                _ => Transfer::Unknown,
            }
        };
        if let Transfer::Inputs(inputs) = &transfer {
            for input in inputs {
                budget.spend(1)?;
                users[input.0].push(id);
            }
        }
        if let Transfer::Extract(input, ..) = &transfer {
            budget.spend(1)?;
            users[input.0].push(id);
        }
        transfers.push(transfer);
    }
    let mut states = vec![Fact::Pending; transfers.len()];
    let mut queued = vec![true; states.len()];
    let mut pending: VecDeque<_> = (0..states.len()).collect();
    while let Some(id) = pending.pop_front() {
        budget.spend(1)?;
        queued[id] = false;
        let derived = match &transfers[id] {
            Transfer::Unknown => Fact::Unknown,
            Transfer::Seed(key) => Fact::Slice(*key),
            Transfer::Inputs(inputs) if !inputs.is_empty() => {
                let mut value = Fact::Pending;
                for input in inputs {
                    budget.spend(1)?;
                    value = value.join(states[input.0]);
                }
                value
            }
            Transfer::Extract(input, start, width) => match states[input.0] {
                Fact::Pending => Fact::Pending,
                Fact::Slice(key) => project(key, *start, *width).map_or(Fact::Unknown, Fact::Slice),
                Fact::Unknown => Fact::Unknown,
            },
            _ => Fact::Unknown,
        };
        let next = states[id].join(derived);
        if next != states[id] {
            states[id] = next;
            for &user in &users[id] {
                budget.spend(1)?;
                if !queued[user] {
                    queued[user] = true;
                    pending.push_back(user);
                }
            }
        }
    }
    let facts = states
        .into_iter()
        .map(|value| match value {
            Fact::Slice(key) => Some(key),
            Fact::Unknown | Fact::Pending => None,
        })
        .collect::<Vec<_>>();
    validate(context, proofs, &facts)?;
    Ok(facts)
}

/// Check local invariants on the source SSA, including every virtual-entry
/// and backedge input. This is induction over actual definition executions,
/// not equality between different visits to a mutable SSA phi.
pub(super) fn validate(
    context: &Context<'_>,
    proofs: &[LoadProof],
    facts: &[Option<Key>],
) -> Result<(), SsaError> {
    if facts.len() != context.graph.values.len() {
        return Err(invalid("saved slice fact dimensions"));
    }
    let seeds = reloads(context, proofs)?;
    let roots = proofs
        .iter()
        .map(|proof| proof.key.value)
        .collect::<BTreeSet<_>>();
    let mut budget = Budget::new();
    for (id, definition) in context.graph.values.iter().enumerate() {
        budget.spend(1)?;
        let Some(key) = facts[id] else { continue };
        if u32::from(key.start) + key.width.bits() > 64 {
            return Err(invalid("saved slice bounds"));
        }
        if let Some(seed) = seeds.get(&ValueId(id)) {
            if *seed != key {
                return Err(invalid("saved slice changed seed"));
            }
            continue;
        }
        if key
            == (Key {
                value: SavedValue::Register(ValueId(id)),
                start: 0,
                width: Width::U64,
            })
            && roots.contains(&key.value)
            && !matches!(definition, Definition::Phi { .. })
            && context.capture(key.value).is_some()
        {
            continue;
        }
        match definition {
            Definition::Phi { inputs, .. } if !inputs.is_empty() => {
                for input in inputs {
                    budget.spend(1)?;
                    if facts[input.value.0] != Some(key) {
                        return Err(invalid("saved slice phi input"));
                    }
                }
            }
            Definition::Assignment { site, .. } => {
                let assignment = context
                    .assignment(*site)
                    .ok_or(invalid("saved slice source"))?;
                let point = context.point(*site).ok_or(invalid("saved slice point"))?;
                match (&assignment.value, &*point.reads) {
                    (Expr::Register(register), [read])
                        if *register == read.register && facts[read.value.0] == Some(key) => {}
                    (Expr::Unary(UnaryOp::Extract { start, width }, value), [read]) if matches!(&**value, Expr::Register(r) if *r == read.register) =>
                    {
                        let input = facts[read.value.0]
                            .ok_or(invalid("saved slice extraction unknown input"))?;
                        // Check the complete result: the selected low bits
                        // come from the same root, and all remaining bits are zero.
                        let contained = u32::from(*start) + width.bits() <= input.width.bits();
                        let wider = *start == 0 && width.bits() >= input.width.bits();
                        let expected = if wider {
                            input
                        } else {
                            Key {
                                value: input.value,
                                start: input
                                    .start
                                    .checked_add(*start)
                                    .ok_or(invalid("saved slice extraction bounds"))?,
                                width: *width,
                            }
                        };
                        if !(contained || wider) || key != expected {
                            return Err(invalid("saved slice extraction identity"));
                        }
                    }
                    _ => return Err(invalid("saved slice copy input")),
                }
            }
            _ => return Err(invalid("saved slice arbitrary initial value")),
        }
    }
    Ok(())
}
