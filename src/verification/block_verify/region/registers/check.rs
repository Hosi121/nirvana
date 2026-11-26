//! Iterative paired-tree check independent from the register-use collector.
use super::*;

pub(super) fn validate(compact: &Compact) -> Result<(), Error> {
    shape::bounded_source(&compact.source, MAX_SOURCE_REGISTERS)?;
    shape::bounded_successors(&compact.program)?;
    let bad = || Error::BoundaryMapping;
    if compact.source.instructions().len() != compact.program.instructions().len()
        || compact.program.register_count() != compact.registers.len()
        || compact.registers.windows(2).any(|p| p[0].0 >= p[1].0)
        || compact
            .registers
            .iter()
            .any(|r| r.0 >= compact.source.register_count())
        || compact
            .source
            .cfg()
            .block(compact.source.cfg().entry())
            .start
            != compact
                .program
                .cfg()
                .block(compact.program.cfg().entry())
                .start
    {
        return Err(bad());
    }
    let register_matches = |source: Reg, candidate: Reg| {
        if compact.registers.get(candidate.0).copied() != Some(source) {
            return false;
        }
        true
    };
    for (source, candidate) in compact
        .source
        .instructions()
        .iter()
        .zip(compact.program.instructions())
    {
        if source.address != candidate.address
            || source.size != candidate.size
            || source.assignments.len() != candidate.assignments.len()
        {
            return Err(bad());
        }
        let mut expressions = Vec::new();
        for (source, candidate) in source.assignments.iter().zip(&candidate.assignments) {
            expressions.push((&source.value, &candidate.value));
            match (&source.destination, &candidate.destination) {
                (Place::Register(a), Place::Register(b)) if register_matches(*a, *b) => {}
                (
                    Place::Memory {
                        address: a,
                        width: x,
                    },
                    Place::Memory {
                        address: b,
                        width: y,
                    },
                ) if x == y => expressions.push((a, b)),
                _ => return Err(bad()),
            }
        }
        match (&source.control, &candidate.control) {
            (Control::Next, Control::Next) => {}
            (Control::Jump(a), Control::Jump(b)) if a == b => {}
            (
                Control::Branch {
                    condition: a,
                    target: x,
                },
                Control::Branch {
                    condition: b,
                    target: y,
                },
            ) if x == y => expressions.push((a, b)),
            (Control::Return(a), Control::Return(b)) => expressions.push((a, b)),
            _ => return Err(bad()),
        }
        while let Some((source, candidate)) = expressions.pop() {
            match (source, candidate) {
                (Expr::Const(a), Expr::Const(b)) if a == b => {}
                (Expr::Register(a), Expr::Register(b)) if register_matches(*a, *b) => {}
                (Expr::Unary(a, x), Expr::Unary(b, y)) if a == b => expressions.push((x, y)),
                (Expr::Binary(a, x, y), Expr::Binary(b, u, v)) if a == b => {
                    expressions.extend([(&**x, &**u), (&**y, &**v)])
                }
                (
                    Expr::Load {
                        address: a,
                        width: x,
                    },
                    Expr::Load {
                        address: b,
                        width: y,
                    },
                ) if x == y => expressions.push((a, b)),
                (
                    Expr::Select {
                        condition: a,
                        taken: b,
                        not_taken: c,
                    },
                    Expr::Select {
                        condition: x,
                        taken: y,
                        not_taken: z,
                    },
                ) => expressions.extend([(&**a, &**x), (&**b, &**y), (&**c, &**z)]),
                _ => return Err(bad()),
            }
        }
    }
    Ok(())
}
