//! Propose a source-register slice for one stored byte. The independent
//! verifier evaluates bit origins for the entire RHS instead of this path.
use super::analyze::Context;
use super::*;
use crate::model::ir::{BinaryOp as B, Place};
fn reads(e: &Expr, budget: &mut Budget) -> Option<usize> {
    let mut pending = vec![e];
    let mut count = 0usize;
    while let Some(e) = pending.pop() {
        budget.spend(1).ok()?;
        match e {
            Expr::Register(_) => count = count.checked_add(1)?,
            Expr::Unary(_, v) => pending.push(v),
            Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
            Expr::Load { address, .. } => pending.push(address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            Expr::Const(_) => {}
        }
    }
    Some(count)
}
pub(super) fn stored_byte(
    context: &Context<'_>,
    site: Site,
    byte: usize,
    expand: bool,
    budget: &mut Budget,
) -> Option<(ValueId, u8)> {
    let a = context.assignment(site)?;
    let point = context.point(site)?;
    let Place::Memory { address, .. } = &a.destination else {
        return None;
    };
    let ordinal = reads(address, budget)?;
    Tracer {
        context,
        expand,
        seen: BTreeSet::new(),
        budget,
    }
    .project(&a.value, point, ordinal, (byte * 8) as u8, 0)
}
struct Tracer<'a, 'b, 's> {
    context: &'a Context<'s>,
    expand: bool,
    seen: BTreeSet<ValueId>,
    budget: &'b mut Budget,
}
impl Tracer<'_, '_, '_> {
    fn project(
        &mut self,
        mut e: &Expr,
        point: &PointValues,
        mut ordinal: usize,
        mut start: u8,
        depth: usize,
    ) -> Option<(ValueId, u8)> {
        let context = self.context;
        loop {
            self.budget.spend(1).ok()?;
            if u32::from(start) + 8 > 64 {
                return None;
            }
            let mask = 255u64 << start;
            e = match e {
                Expr::Register(register) => {
                    let read = point.reads.get(ordinal)?;
                    if read.register != *register {
                        return None;
                    }
                    let value = *context.aliases.get(read.value.0)?;
                    if self.expand && depth < 16 && self.seen.insert(value) {
                        let origin = if let Some(Definition::Assignment { site, .. }) =
                            context.graph.values.get(value.0)
                        {
                            context
                                .assignment(*site)
                                .filter(|a| matches!(a.destination, Place::Register(_)))
                                .and_then(|a| {
                                    self.project(
                                        &a.value,
                                        context.point(*site)?,
                                        0,
                                        start,
                                        depth + 1,
                                    )
                                })
                        } else {
                            None
                        };
                        self.seen.remove(&value);
                        if let Some(origin) = origin {
                            return Some(origin);
                        }
                    }
                    return Some((value, start));
                }
                Expr::Unary(UnaryOp::SignExtend(width), value)
                    if u32::from(start) + 8 <= width.bits() =>
                {
                    value
                }
                Expr::Unary(UnaryOp::Extract { start: from, width }, value)
                    if u32::from(start) + 8 <= width.bits() =>
                {
                    start = start.checked_add(*from)?;
                    value
                }
                Expr::Binary(B::And, a, b) => match (&**a, &**b) {
                    (value, Expr::Const(n)) if n & mask == mask => value,
                    (Expr::Const(n), value) if n & mask == mask => {
                        ordinal = ordinal.checked_add(reads(a, self.budget)?)?;
                        value
                    }
                    _ => return None,
                },
                Expr::Binary(B::Or | B::Xor, a, b) => match (&**a, &**b) {
                    (value, Expr::Const(n)) if n & mask == 0 => value,
                    (Expr::Const(n), value) if n & mask == 0 => {
                        ordinal = ordinal.checked_add(reads(a, self.budget)?)?;
                        value
                    }
                    _ => return None,
                },
                Expr::Binary(B::Shr | B::AShr, value, count)
                    if matches!(&**count, Expr::Const(_)) =>
                {
                    let Expr::Const(count) = **count else {
                        unreachable!()
                    };
                    start = start.checked_add((count & 63) as u8)?;
                    value
                }
                Expr::Binary(B::Shl, value, count) if matches!(&**count, Expr::Const(_)) => {
                    let Expr::Const(count) = **count else {
                        unreachable!()
                    };
                    start = start.checked_sub((count & 63) as u8)?;
                    value
                }
                Expr::Binary(B::Insert { start: from, width }, base, value) => {
                    let from = u32::from(*from);
                    let lo = u32::from(start);
                    let end = lo + 8;
                    let inserted = from + width.bits();
                    if lo >= from && end <= inserted {
                        ordinal = ordinal.checked_add(reads(base, self.budget)?)?;
                        start = (lo - from) as u8;
                        value
                    } else if end <= from || lo >= inserted {
                        base
                    } else {
                        return None;
                    }
                }
                _ => return None,
            };
        }
    }
}
