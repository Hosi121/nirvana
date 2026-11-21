//! Pure snapshots, rewriting, and independent tree correspondence.
use super::*;
use crate::dataflow::value_graph::ValueNode;

pub(super) fn snapshot(
    block: &BlockValues,
    id: ValueId,
    point: Point,
    count: usize,
    work: &mut Work,
) -> Option<Expr> {
    let mut registers = BTreeMap::new();
    for i in 0..count {
        work.spend(1)?;
        registers
            .entry(block.value_before(Reg(i), point)?)
            .or_insert(Reg(i));
    }
    fn build(
        block: &BlockValues,
        id: ValueId,
        regs: &BTreeMap<ValueId, Reg>,
        depth: usize,
        work: &mut Work,
    ) -> Option<Expr> {
        work.spend(1)?;
        if depth > value_graph::MAX_DEPTH {
            return None;
        }
        if let Some(reg) = regs.get(&id) {
            return Some(Expr::Register(*reg));
        }
        Some(match block.node(id)? {
            ValueNode::Constant(n) => Expr::Const(n),
            ValueNode::Unary(op, value) => {
                Expr::unary(op, build(block, value, regs, depth + 1, work)?)
            }
            ValueNode::Binary(op, a, b) => Expr::binary(
                op,
                build(block, a, regs, depth + 1, work)?,
                build(block, b, regs, depth + 1, work)?,
            ),
            ValueNode::Select(c, t, n) => Expr::select(
                build(block, c, regs, depth + 1, work)?,
                build(block, t, regs, depth + 1, work)?,
                build(block, n, regs, depth + 1, work)?,
            ),
            // Historical loads require a live register; addresses are not replayed.
            ValueNode::Initial(_) | ValueNode::CapturedLoad(_) => return None,
        })
    }
    build(block, id, &registers, 0, work)
}

fn replacement<'a>(
    e: &Expr,
    block: Option<&BlockValues>,
    point: Point,
    plan: &'a SemanticPlan,
    work: &mut Work,
) -> Option<Option<&'a Capture>> {
    let Some(block) = block else {
        return Some(None);
    };
    let Some(id) = block.value_of(e, point, work)? else {
        return Some(None);
    };
    work.spend(plan.captures.len())?;
    Some(
        plan.captures
            .iter()
            .filter(|c| c.value == id && available(block, c, point))
            .min_by_key(|c| c.point),
    )
}

pub(super) fn rewrite(
    e: &Expr,
    block: Option<&BlockValues>,
    point: Point,
    plan: &SemanticPlan,
    work: &mut Work,
    replaced: &mut usize,
) -> Option<Expr> {
    work.spend(1)?;
    if let Some(capture) = replacement(e, block, point, plan, work)? {
        *replaced = replaced.checked_add(1)?;
        return Some(Expr::Register(capture.storage));
    }
    Some(match e {
        Expr::Const(n) => Expr::Const(*n),
        Expr::Register(reg) => Expr::Register(*reg),
        Expr::Unary(op, value) => {
            Expr::unary(*op, rewrite(value, block, point, plan, work, replaced)?)
        }
        Expr::Binary(op, a, b) => Expr::binary(
            *op,
            rewrite(a, block, point, plan, work, replaced)?,
            rewrite(b, block, point, plan, work, replaced)?,
        ),
        Expr::Load { address, width } => Expr::load(
            rewrite(address, block, point, plan, work, replaced)?,
            *width,
        ),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(
            rewrite(condition, block, point, plan, work, replaced)?,
            rewrite(taken, block, point, plan, work, replaced)?,
            rewrite(not_taken, block, point, plan, work, replaced)?,
        ),
    })
}

/// A changed subtree must be a pure source value equal to an available capture.
/// Every remaining operator, load, lazy arm and child order is compared directly.
pub(super) fn verify(
    source: &Expr,
    target: &Expr,
    block: Option<&BlockValues>,
    point: Point,
    plan: &SemanticPlan,
    work: &mut Work,
    replaced: &mut usize,
) -> Option<()> {
    work.spend(1)?;
    if let Expr::Register(reg) = target {
        work.spend(plan.captures.len())?;
        if let Some(capture) = plan.captures.iter().find(|c| c.storage == *reg) {
            let block = block?;
            if !available(block, capture, point)
                || block.value_of(source, point, work)? != Some(capture.value)
            {
                return None;
            }
            *replaced = replaced.checked_add(1)?;
            return Some(());
        }
    }
    match (source, target) {
        (Expr::Const(a), Expr::Const(b)) if a == b => {}
        (Expr::Register(a), Expr::Register(b)) if a == b => {}
        (Expr::Unary(a, x), Expr::Unary(b, y)) if a == b => {
            verify(x, y, block, point, plan, work, replaced)?
        }
        (Expr::Binary(a, al, ar), Expr::Binary(b, bl, br)) if a == b => {
            verify(al, bl, block, point, plan, work, replaced)?;
            verify(ar, br, block, point, plan, work, replaced)?;
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
        ) if x == y => verify(a, b, block, point, plan, work, replaced)?,
        (
            Expr::Select {
                condition: a,
                taken: at,
                not_taken: an,
            },
            Expr::Select {
                condition: b,
                taken: bt,
                not_taken: bn,
            },
        ) => {
            verify(a, b, block, point, plan, work, replaced)?;
            verify(at, bt, block, point, plan, work, replaced)?;
            verify(an, bn, block, point, plan, work, replaced)?;
        }
        _ => return None,
    }
    Some(())
}
