//! Source-correspondence check independent from prefix emission.
use super::*;
pub(super) fn validate(context: &Prefixed) -> Result<(), ExtractionError> {
    context.prefix.validate()?;
    context.repeated.validate()?;
    shape::inspect(&context.program)?;
    let bad = || ExtractionError::Projection;
    let source = &context.prefix;
    if !source.belongs_to(&context.repeated.region.source)
        || source.stops != context.repeated.region.stops
        || source.entry == context.repeated.region.entry
        || context.repeated.region.caps.iter().any(|&b| b != 64)
        || context.program.register_count() != context.repeated.program.register_count()
        || context
            .program
            .cfg()
            .block(context.program.cfg().entry())
            .start
            != 0
    {
        return Err(bad());
    }
    let is: BTreeMap<_, _> = context
        .program
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let first = is.get(&0).ok_or_else(bad)?;
    if first.size != 1
        || first.assignments
            != [Assignment {
                destination: context.repeated.flag.into(),
                value: Expr::Const(0),
            }]
        || first.control != Control::Jump(context.prefix_offset)
    {
        return Err(bad());
    }
    let feedback = context.prefix.terminals[&context.repeated.region.entry];
    let mut consumed = BTreeSet::from([0]);
    for (program, offset, is_prefix) in [
        (&context.prefix.program, context.prefix_offset, true),
        (&context.repeated.program, context.loop_offset, false),
    ] {
        for original in program.instructions() {
            let pc = original.address.checked_add(offset).ok_or_else(bad)?;
            if !consumed.insert(pc) {
                return Err(bad());
            }
            let copied = is.get(&pc).ok_or_else(bad)?;
            if copied.size != original.size || copied.assignments != original.assignments {
                return Err(bad());
            }
            if is_prefix && original.address == feedback {
                if copied.control != Control::Jump(context.loop_offset) {
                    return Err(bad());
                }
                continue;
            }
            let equal = match (&original.control, &copied.control) {
                (Control::Next, Control::Next) => true,
                (Control::Jump(a), Control::Jump(b)) => a.checked_add(offset) == Some(*b),
                (
                    Control::Branch {
                        condition: a,
                        target: x,
                    },
                    Control::Branch {
                        condition: b,
                        target: y,
                    },
                ) => a == b && x.checked_add(offset) == Some(*y),
                (Control::Return(a), Control::Return(b)) => a == b,
                _ => false,
            };
            if !equal {
                return Err(bad());
            }
        }
    }
    if consumed.len() != is.len() {
        return Err(bad());
    }
    Ok(())
}
