//! Nonexpanding, width-aware expression presentation.
//!
//! This does not rewrite executable IR. Callers must supply unsigned storage
//! widths which fit every value a register can hold at this presentation site.
//! Arithmetic remains modulo 2^64. No load is discarded, duplicated, reordered,
//! or moved across a lazy select, even when its successful value is known zero.

use crate::model::ir::{BinaryOp as B, Expr, Reg, Width};

const MAX_NODES: usize = 65_536;
const MAX_DEPTH: usize = 128;

/// Normalize using honest bounds on register values. Oversized/deep inputs are
/// returned unchanged. Validation and fallback copying are iterative; recursive
/// normalization runs only after its depth and node count have been checked.
pub fn normalize(expression: &Expr, width: impl Fn(Reg) -> Width) -> Expr {
    if !bounded(expression) {
        return copy_iterative(expression);
    }
    visit(expression, &width).expression
}

fn bounded(expression: &Expr) -> bool {
    let mut pending = vec![(expression, 0usize)];
    let mut nodes = 0usize;
    while let Some((expression, depth)) = pending.pop() {
        nodes += 1;
        if nodes > MAX_NODES || depth > MAX_DEPTH {
            return false;
        }
        match expression {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Binary(_, left, right) => {
                pending.push((right, depth + 1));
                pending.push((left, depth + 1));
            }
            Expr::Load { address, .. } => pending.push((address, depth + 1)),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push((not_taken, depth + 1));
                pending.push((taken, depth + 1));
                pending.push((condition, depth + 1));
            }
        }
    }
    true
}

struct Value {
    expression: Expr,
    possible: u64,
    pure: bool,
}

impl Value {
    fn constant(value: u64) -> Self {
        Self {
            expression: Expr::Const(value),
            possible: value,
            pure: true,
        }
    }

    fn number(&self) -> Option<u64> {
        if let Expr::Const(value) = self.expression {
            Some(value)
        } else {
            None
        }
    }
}

fn visit(expression: &Expr, width: &impl Fn(Reg) -> Width) -> Value {
    match expression {
        Expr::Const(value) => Value::constant(*value),
        Expr::Register(reg) => Value {
            expression: Expr::Register(*reg),
            possible: width(*reg).mask(),
            pure: true,
        },
        Expr::Load {
            address,
            width: load_width,
        } => Value {
            expression: Expr::load(visit(address, width).expression, *load_width),
            possible: load_width.mask(),
            pure: false,
        },
        Expr::Binary(op, left, right) => binary(*op, visit(left, width), visit(right, width)),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            let condition = visit(condition, width);
            let taken = visit(taken, width);
            let not_taken = visit(not_taken, width);
            let pure = condition.pure && taken.pure && not_taken.pure;
            let possible = taken.possible | not_taken.possible;
            if pure {
                if let Some(condition) = condition.number() {
                    return if condition != 0 { taken } else { not_taken };
                }
                if possible == 0 {
                    return Value::constant(0);
                }
                if taken.expression == not_taken.expression {
                    return taken;
                }
            }
            Value {
                expression: Expr::select(
                    condition.expression,
                    taken.expression,
                    not_taken.expression,
                ),
                possible,
                pure,
            }
        }
    }
}

fn binary(op: B, left: Value, right: Value) -> Value {
    let a = left.number();
    let b = right.number();
    if let (Some(a), Some(b)) = (a, b) {
        return Value::constant(fold(op, a, b));
    }
    let pure = left.pure && right.pure;
    let possible = possible(op, left.possible, right.possible, b);
    // Width normalization can expose identities which were hidden behind a
    // mask. Fold before dependency collection (and before C can diagnose a
    // tautological self-comparison). Equal loads still execute independently.
    if pure && left.expression == right.expression {
        match op {
            B::Sub | B::Xor | B::Ne | B::Ult => return Value::constant(0),
            B::Eq | B::Ule => return Value::constant(1),
            B::And | B::Or => return left,
            _ => {}
        }
    }
    if possible == 0 && pure {
        return Value::constant(0);
    }
    // Masks can expose an adjacent scale after executable-IR simplification.
    // An outer power of two preserves the existing possible-bit bound; checked
    // constants keep this one-pass rewrite nonexpanding and idempotent.
    if op == B::Mul
        && let Some(scale) = b
        && scale > 1
        && scale.is_power_of_two()
        && let Expr::Binary(B::Mul, _, factor) = &left.expression
        && let Expr::Const(factor) = **factor
        && let Some(combined) = factor.checked_mul(scale)
    {
        let Expr::Binary(_, value, _) = left.expression else {
            unreachable!()
        };
        return Value {
            expression: Expr::binary(B::Mul, *value, Expr::Const(combined)),
            possible,
            pure,
        };
    }
    match op {
        B::And => {
            if let Some(mask) = b {
                if left.possible & !mask == 0 {
                    return left;
                }
                return Value {
                    expression: Expr::binary(
                        op,
                        left.expression,
                        Expr::Const(mask & left.possible),
                    ),
                    possible,
                    pure,
                };
            }
            if let Some(mask) = a {
                if right.possible & !mask == 0 {
                    return right;
                }
                return Value {
                    expression: Expr::binary(
                        op,
                        Expr::Const(mask & right.possible),
                        right.expression,
                    ),
                    possible,
                    pure,
                };
            }
        }
        B::Add | B::Or | B::Xor if a == Some(0) => return right,
        B::Add | B::Sub | B::Or | B::Xor if b == Some(0) => return left,
        B::Mul if a == Some(1) => return right,
        B::Mul if b == Some(1) => return left,
        B::Or if a == Some(u64::MAX) && right.pure => return left,
        B::Or if b == Some(u64::MAX) && left.pure => return right,
        B::Shl | B::Shr => {
            if let Some(count) = b {
                if count & 63 == 0 {
                    return left;
                }
                return Value {
                    expression: Expr::binary(op, left.expression, Expr::Const(count & 63)),
                    possible,
                    pure,
                };
            }
        }
        _ => {}
    }
    let expression = Expr::binary(op, left.expression, right.expression);
    // The certificate covers this raw pure tree, independently of storage
    // widths. A numeric remainder bound needs its complete low-bit hull:
    // values <= 9 can contain bits 0..3, rather than only the bits in 9.
    let possible = if pure && op == B::Sub {
        crate::transform::remainder_expr::recognize(&expression)
            .map_or(possible, |view| possible & low_mask(view.maximum_remainder))
    } else {
        possible
    };
    Value {
        expression,
        possible,
        pure,
    }
}

fn low_mask(maximum: u64) -> u64 {
    if maximum == 0 {
        0
    } else {
        u64::MAX >> maximum.leading_zeros()
    }
}

fn possible(op: B, left: u64, right: u64, count: Option<u64>) -> u64 {
    match op {
        B::And => left & right,
        B::Or | B::Xor => left | right,
        B::Eq | B::Ne | B::Ult | B::Ule => 1,
        B::Add if left == 0 => right,
        B::Add | B::Sub if right == 0 => left,
        B::Add => left.checked_add(right).map_or(u64::MAX, low_mask),
        B::Sub => u64::MAX,
        B::Mul => left.checked_mul(right).map_or(u64::MAX, low_mask),
        B::UMulHigh => low_mask(((u128::from(left) * u128::from(right)) >> 64) as u64),
        B::Shl => count.map_or(if left == 0 { 0 } else { u64::MAX }, |count| {
            left.wrapping_shl((count & 63) as u32)
        }),
        B::Shr => count.map_or(low_mask(left), |count| {
            left.wrapping_shr((count & 63) as u32)
        }),
    }
}

fn fold(op: B, left: u64, right: u64) -> u64 {
    match op {
        B::Add => left.wrapping_add(right),
        B::Sub => left.wrapping_sub(right),
        B::Mul => left.wrapping_mul(right),
        B::And => left & right,
        B::Or => left | right,
        B::Xor => left ^ right,
        B::Shl => left.wrapping_shl((right & 63) as u32),
        B::Shr => left.wrapping_shr((right & 63) as u32),
        B::Eq => u64::from(left == right),
        B::Ne => u64::from(left != right),
        B::Ult => u64::from(left < right),
        B::Ule => u64::from(left <= right),
        B::UMulHigh => ((u128::from(left) * u128::from(right)) >> 64) as u64,
    }
}

// Expr's derived Clone is recursive. A rejected input may be deeper than the
// normalization limit, so reconstruct its unchanged shape with explicit stacks.
fn copy_iterative(expression: &Expr) -> Expr {
    enum Task<'a> {
        Visit(&'a Expr),
        Binary(B),
        Load(Width),
        Select,
    }
    let mut pending = vec![Task::Visit(expression)];
    let mut built = Vec::new();
    while let Some(task) = pending.pop() {
        match task {
            Task::Visit(expression) => match expression {
                Expr::Const(value) => built.push(Expr::Const(*value)),
                Expr::Register(reg) => built.push(Expr::Register(*reg)),
                Expr::Binary(op, left, right) => {
                    pending.push(Task::Binary(*op));
                    pending.push(Task::Visit(right));
                    pending.push(Task::Visit(left));
                }
                Expr::Load { address, width } => {
                    pending.push(Task::Load(*width));
                    pending.push(Task::Visit(address));
                }
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => {
                    pending.push(Task::Select);
                    pending.push(Task::Visit(not_taken));
                    pending.push(Task::Visit(taken));
                    pending.push(Task::Visit(condition));
                }
            },
            Task::Binary(op) => {
                let right = built.pop().expect("visited right operand");
                let left = built.pop().expect("visited left operand");
                built.push(Expr::binary(op, left, right));
            }
            Task::Load(width) => {
                let address = built.pop().expect("visited load address");
                built.push(Expr::load(address, width));
            }
            Task::Select => {
                let not_taken = built.pop().expect("visited not-taken arm");
                let taken = built.pop().expect("visited taken arm");
                let condition = built.pop().expect("visited select condition");
                built.push(Expr::select(condition, taken, not_taken));
            }
        }
    }
    built.pop().expect("visited root")
}
