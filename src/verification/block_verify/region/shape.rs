//! Bound source traversal before recursive cloning, then certify a closed DAG.
use super::*;

pub(super) fn inspect(program: &Program) -> Result<Vec<u64>, Error> {
    let successors = bounded_successors(program)?;
    let entry = program.cfg().block(program.cfg().entry()).start;
    let mut reachable = BTreeSet::new();
    let mut pending = vec![entry];
    while let Some(pc) = pending.pop() {
        if reachable.insert(pc) {
            pending.extend(successors[&pc].iter().copied());
        }
    }
    let mut degree: BTreeMap<_, usize> = reachable.iter().map(|&pc| (pc, 0)).collect();
    for &pc in &reachable {
        for to in &successors[&pc] {
            *degree.get_mut(to).ok_or(Error::OpenEdge)? += 1;
        }
    }
    let mut ready: BTreeSet<_> = degree
        .iter()
        .filter_map(|(&pc, &n)| (n == 0).then_some(pc))
        .collect();
    let mut order = Vec::new();
    while let Some(pc) = ready.pop_first() {
        order.push(pc);
        for to in &successors[&pc] {
            let count = degree.get_mut(to).ok_or(Error::OpenEdge)?;
            *count -= 1;
            if *count == 0 {
                ready.insert(*to);
            }
        }
    }
    if order.len() != reachable.len() {
        return Err(Error::Cycle);
    }
    Ok(order)
}

/// The same source/expression preflight also permits a cyclic source before
/// extraction. No recursive source clone happens until this check succeeds.
pub(super) fn bounded_successors(program: &Program) -> Result<BTreeMap<u64, Vec<u64>>, Error> {
    if program.register_count() > MAX_REGISTERS || program.instructions().len() > MAX_INSTRUCTIONS {
        return Err(Error::Limit);
    }
    let mut expressions = Vec::new();
    let mut remaining = MAX_EXPRESSIONS;
    let instructions: BTreeMap<_, _> = program
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let mut successors = BTreeMap::new();
    for (&pc, instruction) in &instructions {
        if instruction.assignments.len() > remaining {
            return Err(Error::Limit);
        }
        remaining -= instruction.assignments.len();
        for assignment in &instruction.assignments {
            if let Place::Memory { address, .. } = &assignment.destination {
                expressions.push((address, 0));
            }
            expressions.push((&assignment.value, 0));
        }
        let fallthrough = || {
            pc.checked_add(u64::from(instruction.size))
                .ok_or(Error::OpenEdge)
        };
        let targets = match &instruction.control {
            Control::Next => vec![fallthrough()?],
            Control::Jump(to) => vec![*to],
            Control::Branch { condition, target } => {
                expressions.push((condition, 0));
                let fall = fallthrough()?;
                if *target == fall {
                    vec![fall]
                } else {
                    vec![*target, fall]
                }
            }
            Control::Return(value) => {
                expressions.push((value, 0));
                vec![]
            }
        };
        if targets.iter().any(|to| !instructions.contains_key(to)) {
            return Err(Error::OpenEdge);
        }
        successors.insert(pc, targets);
        if expressions.len() > remaining {
            return Err(Error::Limit);
        }
        while let Some((expression, depth)) = expressions.pop() {
            if remaining == 0 || depth > MAX_DEPTH {
                return Err(Error::Limit);
            }
            remaining -= 1;
            match expression {
                Expr::Unary(_, value) | Expr::Load { address: value, .. } => {
                    expressions.push((value, depth + 1))
                }
                Expr::Binary(_, a, b) => expressions.extend([(&**a, depth + 1), (&**b, depth + 1)]),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => expressions.extend([
                    (&**condition, depth + 1),
                    (&**taken, depth + 1),
                    (&**not_taken, depth + 1),
                ]),
                _ => {}
            }
        }
    }
    Ok(successors)
}
