//! Check the projection against source blocks rather than the emitter's walk.
use super::*;
use crate::control_flow::cfg::Target;

pub(super) fn validate(region: &Region) -> Result<(), ExtractionError> {
    shape::bounded_successors(&region.source)?;
    shape::inspect(&region.program)?;
    let bad = || ExtractionError::Projection;
    let cfg = region.source.cfg();
    let entry = cfg.block_at(region.entry).ok_or_else(bad)?;
    if region.program.register_count() != region.source.register_count() + 1
        || region
            .program
            .cfg()
            .block(region.program.cfg().entry())
            .start
            != 0
        || region.stops.windows(2).any(|p| p[0] >= p[1])
        || region.stops.iter().any(|&pc| cfg.block_at(pc).is_none())
    {
        return Err(bad());
    }
    let caps = match &region.widths {
        None => vec![64; region.source.register_count()],
        Some(facts) => {
            let widths = facts.widths().ok_or(ExtractionError::EntryFacts)?;
            let rows = facts.incoming().ok_or(ExtractionError::EntryFacts)?;
            value_width::validate(&region.source, widths, rows)
                .map_err(|_| ExtractionError::EntryFacts)?;
            rows[entry.index()]
                .clone()
                .ok_or(ExtractionError::EntryFacts)?
        }
    };
    if region.caps != caps || caps.iter().any(|&bits| bits > 64) {
        return Err(ExtractionError::EntryFacts);
    }
    let mut blocks = BTreeSet::new();
    let mut pending = vec![entry];
    let mut selected = BTreeSet::new();
    while let Some(id) = pending.pop() {
        if !blocks.insert(id) {
            continue;
        }
        let block = cfg.block(id);
        selected.extend(
            region.source.instructions()[block.instructions.clone()]
                .iter()
                .map(|i| i.address),
        );
        for edge in &block.successors {
            let Target::Block(to) = edge.target else {
                return Err(bad());
            };
            if !region.stops.contains(&cfg.block(to).start) {
                pending.push(to);
            }
        }
    }
    if region.body.keys().copied().collect::<BTreeSet<_>>() != selected
        || region.terminals.keys().copied().collect::<Vec<_>>() != region.stops
    {
        return Err(bad());
    }
    let actual: BTreeMap<_, _> = region
        .program
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let mut consumed = BTreeSet::new();
    let mut take = |pc: u64| {
        if !consumed.insert(pc) {
            return Err(bad());
        }
        actual.get(&pc).copied().ok_or_else(bad)
    };
    let prefix = take(0)?;
    let mut expected_prefix = vec![Assignment {
        destination: region.return_register().into(),
        value: Expr::Const(0),
    }];
    for (reg, &bits) in caps.iter().enumerate().filter(|(_, bits)| **bits < 64) {
        expected_prefix.push(Assignment {
            destination: Reg(reg).into(),
            value: Expr::binary(
                BinaryOp::And,
                Expr::Register(Reg(reg)),
                Expr::Const((1u64 << bits) - 1),
            ),
        });
    }
    if prefix.size != 1
        || prefix.assignments != expected_prefix
        || prefix.control != Control::Jump(region.body[&region.entry])
    {
        return Err(bad());
    }
    let target_matches = |source_pc: u64, actual_pc: u64| {
        region
            .terminals
            .get(&source_pc)
            .or_else(|| region.body.get(&source_pc))
            .copied()
            == Some(actual_pc)
    };
    for original in region
        .source
        .instructions()
        .iter()
        .filter(|i| selected.contains(&i.address))
    {
        let instruction = take(region.body[&original.address])?;
        if instruction.size != 1 {
            return Err(bad());
        }
        let original_count = original.assignments.len();
        let is_return = matches!(original.control, Control::Return(_));
        if instruction.assignments.len() != original_count + usize::from(is_return)
            || instruction.assignments[..original_count] != original.assignments
        {
            return Err(bad());
        }
        let fall = original.address + u64::from(original.size);
        let control_ok = match (&original.control, &instruction.control) {
            (Control::Next, Control::Jump(to)) => target_matches(fall, *to),
            (Control::Jump(from), Control::Jump(to)) => target_matches(*from, *to),
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
                let routing = take(instruction.address + u64::from(instruction.size))?;
                a == b
                    && target_matches(*from, *to)
                    && routing.size == 1
                    && routing.assignments.is_empty()
                    && matches!(routing.control, Control::Jump(to) if target_matches(fall, to))
            }
            (Control::Return(value), Control::Return(Expr::Const(tag))) => {
                *tag == region.stops.len() as u64
                    && instruction.assignments.last()
                        == Some(&Assignment {
                            destination: region.return_register().into(),
                            value: value.clone(),
                        })
            }
            _ => false,
        };
        if !control_ok {
            return Err(bad());
        }
    }
    for (tag, stop) in region.stops.iter().enumerate() {
        let terminal = take(region.terminals[stop])?;
        if terminal.size != 1
            || !terminal.assignments.is_empty()
            || terminal.control != Control::Return(Expr::Const(tag as u64))
        {
            return Err(bad());
        }
    }
    if consumed.len() != actual.len() {
        return Err(bad());
    }
    Ok(())
}
