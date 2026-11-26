//! Internal register relabeling and an independent paired-tree correspondence.
//! Callers establish source bounds before recursive emission and authorize any
//! aliasing separately. The iterative checker only verifies the emitted rename.
use super::*;
use std::collections::BTreeMap;

#[derive(Clone, Copy)]
pub(crate) enum Unmapped {
    Identity,
    Reject,
}
fn name(reg: Reg, names: &BTreeMap<usize, Reg>, unmapped: Unmapped) -> Option<Reg> {
    names
        .get(&reg.0)
        .copied()
        .or_else(|| matches!(unmapped, Unmapped::Identity).then_some(reg))
}
fn expression(source: &Expr, names: &BTreeMap<usize, Reg>, unmapped: Unmapped) -> Option<Expr> {
    let e = |value| expression(value, names, unmapped);
    Some(match source {
        Expr::Const(v) => Expr::Const(*v),
        Expr::Register(r) => Expr::Register(name(*r, names, unmapped)?),
        Expr::Unary(op, x) => Expr::unary(*op, e(x)?),
        Expr::Binary(op, a, b) => Expr::binary(*op, e(a)?, e(b)?),
        Expr::Load { address, width } => Expr::load(e(address)?, *width),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(e(condition)?, e(taken)?, e(not_taken)?),
    })
}
pub(crate) fn relabel(
    source: &Program,
    count: usize,
    names: &BTreeMap<usize, Reg>,
    unmapped: Unmapped,
) -> Option<Program> {
    let e = |value| expression(value, names, unmapped);
    let mut instructions = Vec::new();
    for i in source.instructions() {
        let mut assignments = Vec::new();
        for a in &i.assignments {
            assignments.push(Assignment {
                destination: match &a.destination {
                    Place::Register(r) => name(*r, names, unmapped)?.into(),
                    Place::Memory { address, width } => Place::Memory {
                        address: e(address)?,
                        width: *width,
                    },
                },
                value: e(&a.value)?,
            });
        }
        let control = match &i.control {
            Control::Next => Control::Next,
            Control::Jump(to) => Control::Jump(*to),
            Control::Branch { condition, target } => Control::Branch {
                condition: e(condition)?,
                target: *target,
            },
            Control::Return(v) => Control::Return(e(v)?),
        };
        instructions.push(IrInstruction {
            address: i.address,
            size: i.size,
            assignments,
            control,
        });
    }
    Program::new(
        source.cfg().block(source.cfg().entry()).start,
        count,
        instructions,
    )
    .ok()
}
pub(crate) fn validate(
    source: &Program,
    candidate: &Program,
    count: usize,
    names: &BTreeMap<usize, Reg>,
    unmapped: Unmapped,
) -> bool {
    if candidate.register_count() != count
        || source.instructions().len() != candidate.instructions().len()
        || source.cfg().block(source.cfg().entry()).start
            != candidate.cfg().block(candidate.cfg().entry()).start
    {
        return false;
    }
    for (source, candidate) in source.instructions().iter().zip(candidate.instructions()) {
        if source.address != candidate.address
            || source.size != candidate.size
            || source.assignments.len() != candidate.assignments.len()
        {
            return false;
        }
        let mut expressions = Vec::new();
        for (a, b) in source.assignments.iter().zip(&candidate.assignments) {
            expressions.push((&a.value, &b.value));
            match (&a.destination, &b.destination) {
                (Place::Register(a), Place::Register(b))
                    if name(*a, names, unmapped) == Some(*b) => {}
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
                _ => return false,
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
            _ => return false,
        }
        while let Some((a, b)) = expressions.pop() {
            match (a, b) {
                (Expr::Const(a), Expr::Const(b)) if a == b => {}
                (Expr::Register(a), Expr::Register(b)) if name(*a, names, unmapped) == Some(*b) => {
                }
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
                _ => return false,
            }
        }
    }
    true
}
