//! Effect-preserving identity checks over original SSA reads.
use super::*;

pub(super) fn consume_reads<D: Domain>(
    source: &Expr,
    point: &PointValues,
    states: &[D],
    cursor: &mut usize,
    budget: &mut Budget,
) -> Result<(), SsaError> {
    let mut pending = vec![source];
    while let Some(expression) = pending.pop() {
        budget.spend(1)?;
        match expression {
            Expr::Const(_) => {}
            Expr::Register(_) => {
                read(expression, point, states, cursor)?;
            }
            Expr::Unary(_, x) | Expr::Load { address: x, .. } => pending.push(x),
            Expr::Binary(_, a, b) => {
                pending.push(b);
                pending.push(a);
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push(not_taken);
                pending.push(taken);
                pending.push(condition);
            }
        }
    }
    Ok(())
}

// Check a removed operation against source facts and the actual retained
// operand. Candidate reads never supply the premise. Only a pure discarded
// operand can disappear; the kept subtree retains its loads and lazy arms.
pub(super) fn check<D: Domain>(
    source: &Expr,
    candidate: &Expr,
    point: &PointValues,
    states: &[D],
    cursor: &mut usize,
    budget: &mut Budget,
) -> Result<Option<usize>, SsaError> {
    let start = *cursor;
    let mut alternatives = Vec::new();
    match source {
        Expr::Unary(op, value) => {
            let mut end = start;
            let (state, _) = evaluate(value, point, states, &mut end, budget)?;
            if !D::unary_identity(*op, state) {
                return Ok(None);
            }
            alternatives.push((&**value, start, end, end));
        }
        Expr::Binary(op, left, right) => {
            let mut middle = start;
            let (a, pure_a) = evaluate(left, point, states, &mut middle, budget)?;
            let mut end = middle;
            let (b, pure_b) = evaluate(right, point, states, &mut end, budget)?;
            if pure_b && D::binary_identity(*op, a, b, Operand::Left) {
                alternatives.push((&**left, start, middle, end));
            }
            if pure_a && D::binary_identity(*op, a, b, Operand::Right) {
                alternatives.push((&**right, middle, end, end));
            }
        }
        _ => return Ok(None),
    }
    for (kept, first, last, end) in alternatives {
        let mut read = first;
        match check_expr(kept, candidate, point, states, &mut read, budget) {
            Ok(replacements) if read == last => {
                *cursor = end;
                return Ok(Some(replacements + 1));
            }
            Err(error @ SsaError::Unavailable(_)) => return Err(error),
            _ => {}
        }
    }
    Ok(None)
}
