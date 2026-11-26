//! Independently check every copied region edge and the single exhaustion mark.
use super::*;

pub(super) fn validate(unfolding: &Unfolding) -> Result<(), ExtractionError> {
    let bad = || ExtractionError::Projection;
    let original = &unfolding.region;
    original.validate()?;
    shape::inspect(&unfolding.program)?;
    if !original.stops.contains(&original.entry)
        || unfolding.copies.len() != unfolding.rounds
        || unfolding.flag != Reg(original.program.register_count())
        || unfolding.program.register_count() != unfolding.flag.0 + 1
        || unfolding
            .program
            .cfg()
            .block(unfolding.program.cfg().entry())
            .start
            != 0
    {
        return Err(bad());
    }
    let actual: BTreeMap<_, _> = unfolding
        .program
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let prefix = actual.get(&0).copied().ok_or_else(bad)?;
    let mut consumed = BTreeSet::from([0]);
    let body: BTreeMap<_, _> = original
        .program
        .instructions()
        .iter()
        .filter(|i| i.address != 0)
        .map(|i| (i.address, i))
        .collect();
    let feedback = original.terminals[&original.entry];
    let root = original.body[&original.entry];
    let tag = original
        .stops
        .iter()
        .position(|&pc| pc == original.entry)
        .ok_or_else(bad)? as u64;
    let mut expected_prefix = original.program.instructions()[0].assignments.clone();
    expected_prefix.push(Assignment {
        destination: unfolding.flag.into(),
        value: Expr::Const(0),
    });
    let expected_control = if unfolding.rounds == 0 {
        expected_prefix.push(Assignment {
            destination: unfolding.flag.into(),
            value: Expr::Const(1),
        });
        if unfolding.exhaustion != 0 {
            return Err(bad());
        }
        Control::Return(Expr::Const(tag))
    } else {
        Control::Jump(*unfolding.copies[0].get(&root).ok_or_else(bad)?)
    };
    if prefix.size != 1
        || prefix.assignments != expected_prefix
        || prefix.control != expected_control
    {
        return Err(bad());
    }
    for (round, copy) in unfolding.copies.iter().enumerate() {
        if copy.keys().ne(body.keys()) {
            return Err(bad());
        }
        for (&pc, instruction) in &body {
            let location = copy[&pc];
            if !consumed.insert(location) {
                return Err(bad());
            }
            let copied = actual.get(&location).copied().ok_or_else(bad)?;
            if copied.size != 2 {
                return Err(bad());
            }
            if pc == feedback {
                if round + 1 == unfolding.rounds {
                    let expected = Assignment {
                        destination: unfolding.flag.into(),
                        value: Expr::Const(1),
                    };
                    if unfolding.exhaustion != location
                        || copied.assignments.len() != 1
                        || copied.assignments[0] != expected
                        || copied.control != instruction.control
                    {
                        return Err(bad());
                    }
                } else if !copied.assignments.is_empty()
                    || copied.control
                        != Control::Jump(*unfolding.copies[round + 1].get(&root).ok_or_else(bad)?)
                {
                    return Err(bad());
                }
                continue;
            }
            if copied.assignments != instruction.assignments {
                return Err(bad());
            }
            let matches = match (&instruction.control, &copied.control) {
                (Control::Jump(from), Control::Jump(to)) => copy.get(from).copied() == Some(*to),
                (
                    Control::Branch {
                        condition: a,
                        target: from,
                    },
                    Control::Branch {
                        condition: b,
                        target: to,
                    },
                ) => {
                    a == b
                        && copy.get(from).copied() == Some(*to)
                        && copy.get(&(pc + u64::from(instruction.size))).copied()
                            == Some(location + u64::from(copied.size))
                }
                (Control::Return(a), Control::Return(b)) => a == b,
                _ => false,
            };
            if !matches {
                return Err(bad());
            }
        }
    }
    if consumed.len() != actual.len() {
        return Err(bad());
    }
    Ok(())
}
