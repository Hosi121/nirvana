use super::*;

#[derive(Clone, Debug)]
pub(super) struct Limit {
    pub site: u64,
    pub lhs: Expr,
    pub equal: bool,
}
pub(super) struct Controls {
    pub first: Region,
    pub limit: Limit,
    pub load_address: Expr,
    pub break_update: Option<(Site, Reg, Expr)>,
    pub staging: Option<(Site, Reg, Reg)>,
}

use super::expressions::{at_offset, index, instantiate};

pub(super) fn exits(
    source: &Program,
    selected: &BTreeSet<u64>,
    stops: &[u64],
    entry: u64,
) -> Result<BTreeSet<u64>, Error> {
    let instructions: BTreeMap<_, _> = source
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let mut pending = vec![entry];
    let mut seen = BTreeSet::new();
    let mut result = BTreeSet::new();
    while let Some(pc) = pending.pop() {
        if stops.contains(&pc) {
            result.insert(pc);
            continue;
        }
        if !seen.insert(pc) {
            continue;
        }
        if !selected.contains(&pc) {
            return Err(Error::Controls);
        }
        let i = instructions[&pc];
        let fall = pc + u64::from(i.size);
        match &i.control {
            Control::Next => pending.push(fall),
            Control::Jump(to) => pending.push(*to),
            Control::Branch { target, .. } => pending.extend([*target, fall]),
            Control::Return(_) => return Err(Error::Controls),
        }
    }
    Ok(result)
}
fn comparison(condition: &Expr, offset: u64) -> Option<(Expr, bool)> {
    let Expr::Binary(op, a, b) = condition else {
        return None;
    };
    let equal = match op {
        BinaryOp::Eq => true,
        BinaryOp::Ne => false,
        _ => return None,
    };
    if **b == Expr::Const(offset) {
        return Some(((**a).clone(), equal));
    }
    if **a == Expr::Const(offset) {
        return Some(((**b).clone(), equal));
    }
    let mut value = if **b == Expr::Const(0) {
        &**a
    } else if **a == Expr::Const(0) {
        &**b
    } else {
        return None;
    };
    while let Expr::Unary(_, inner) = value {
        value = inner;
    }
    let Expr::Binary(BinaryOp::Sub, lhs, rhs) = value else {
        return None;
    };
    (**rhs == Expr::Const(offset)).then(|| ((**lhs).clone(), equal))
}
fn limit(
    source: &Program,
    slice: &Region,
    next: u64,
    latch: u64,
    offset: u64,
) -> Result<(Limit, bool), Error> {
    let selected = slice.source_to_region().keys().copied().collect();
    let mut found = None;
    for i in source
        .instructions()
        .iter()
        .filter(|i| slice.source_to_region().contains_key(&i.address))
    {
        let Control::Branch { condition, target } = &i.control else {
            continue;
        };
        let taken = exits(source, &selected, slice.continuations(), *target)?;
        let fall = exits(
            source,
            &selected,
            slice.continuations(),
            i.address + u64::from(i.size),
        )?;
        let continues = if taken == BTreeSet::from([next]) && fall == BTreeSet::from([latch]) {
            true
        } else if fall == BTreeSet::from([next]) && taken == BTreeSet::from([latch]) {
            false
        } else {
            continue;
        };
        let (lhs, equal) = comparison(condition, offset).ok_or(Error::Controls)?;
        if found.is_some() {
            return Err(Error::Controls);
        }
        found = Some((
            Limit {
                site: i.address,
                lhs,
                equal,
            },
            if equal { continues } else { !continues },
        ));
    }
    found.ok_or(Error::Controls)
}
pub(super) fn single_register(expression: &Expr) -> Option<Reg> {
    if let Expr::Register(reg) = expression {
        Some(*reg)
    } else {
        None
    }
}
pub(super) fn analyze(
    source: &Program,
    discovery: &Discovery,
    group: &LaneGroup,
    envelope: &Envelope,
    counter: Reg,
) -> Result<Controls, Error> {
    let sites: Vec<_> = group.kernels.iter().map(|kernel| kernel.load).collect();
    let load_address = instantiate(&group.load_address, discovery, &sites, counter)?;
    let index = index(&group.load_address).ok_or(Error::Pattern)?;
    let param_index = instantiate(index, discovery, &sites, counter)?;
    let mut slices = Vec::new();
    let mut breaks = Vec::new();
    for (lane, &site) in sites.iter().enumerate() {
        let mut stops = BTreeSet::from([envelope.latch]);
        stops.extend(envelope.abrupt.iter().copied());
        if let Some(&next) = envelope.lane_entries.get(lane + 1) {
            stops.insert(next);
        }
        let slice = extraction::extract(
            source,
            envelope.lane_entries[lane],
            &stops.into_iter().collect::<Vec<_>>(),
            None,
        )
        .map_err(|_| Error::Boundary)?;
        let expected = at_offset(index, group.offsets[lane]);
        let read = discovery.ssa().point(site).ok_or(Error::Pattern)?;
        let registers: BTreeSet<_> = read.reads.iter().map(|read| read.register.0).collect();
        let index_reg = registers
            .into_iter()
            .map(Reg)
            .find(|&reg| {
                discovery
                    .register_expression(site, reg)
                    .is_some_and(|actual| discovery.proposal_match(&actual, &expected))
            })
            .ok_or(Error::Pattern)?;
        let local = lane_patterns::discover(slice.program()).map_err(|_| Error::Pattern)?;
        let local_site = |site: Site| -> Result<Site, Error> {
            Ok(Site {
                instruction: *slice
                    .source_to_region()
                    .get(&site.instruction)
                    .ok_or(Error::Projection)?,
                assignment: site.assignment,
            })
        };
        let index_value = local
            .read_identity(local_site(site)?, index_reg)
            .ok_or(Error::Pattern)?;
        let mut updates = Vec::new();
        for i in source
            .instructions()
            .iter()
            .filter(|i| slice.source_to_region().contains_key(&i.address))
        {
            for (assignment, a) in i.assignments.iter().enumerate() {
                let Place::Register(dest) = a.destination else {
                    continue;
                };
                let Expr::Binary(BinaryOp::Xor, x, y) = &a.value else {
                    continue;
                };
                let site = Site {
                    instruction: i.address,
                    assignment: Some(assignment),
                };
                let other = if **x == Expr::Register(dest) {
                    &**y
                } else if **y == Expr::Register(dest) {
                    &**x
                } else {
                    continue;
                };
                let Expr::Register(other) = other else {
                    continue;
                };
                if dest != group.kernels[lane].accumulator
                    && dest != index_reg
                    && local.read_identity(local_site(site)?, *other) == Some(index_value)
                {
                    updates.push((site, dest));
                }
            }
        }
        if updates.len() > 1 {
            return Err(Error::Controls);
        }
        breaks.push(updates.first().copied());
        slices.push(slice);
    }
    if breaks
        .iter()
        .any(|entry| entry.map(|(_, reg)| reg) != breaks[0].map(|(_, reg)| reg))
    {
        return Err(Error::Controls);
    }
    let (first, sense) = limit(
        source,
        &slices[0],
        envelope.lane_entries[1],
        envelope.latch,
        group.offsets[0],
    )?;
    let (second, other_sense) = limit(
        source,
        &slices[1],
        envelope.lane_entries[2],
        envelope.latch,
        group.offsets[1],
    )?;
    if first.lhs != second.lhs || sense != other_sense || sense {
        return Err(Error::Controls);
    }
    let staging = breaks[0].and_then(|(_, mark)| {
        super::storage::staging(source, &slices[0], &first, mark, envelope.latch)
    });
    Ok(Controls {
        first: slices.remove(0),
        limit: first,
        load_address,
        break_update: breaks[0].map(|(site, reg)| (site, reg, param_index)),
        staging,
    })
}
