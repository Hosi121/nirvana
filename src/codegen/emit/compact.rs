//! C expression rendering with precedence and explicit unsigned word types.
//!
//! Registers, literals, checked loads and helper results already have uint64_t
//! type. Arithmetic therefore wraps without another cast at each AST node.
//! Comparisons need a cast because C otherwise produces a signed int; nested
//! subtraction, multiplication and shifts must still use unsigned 64-bit math.

use crate::model::ir::{BinaryOp as B, Expr, Reg};

struct Rendered {
    code: String,
    precedence: u8,
}

impl Rendered {
    fn atom(code: String) -> Self {
        Self {
            code,
            precedence: 13,
        }
    }

    fn operand(self, parent: u8, right: bool) -> String {
        if self.precedence < parent || (right && self.precedence == parent) {
            format!("({})", self.code)
        } else {
            self.code
        }
    }

    fn binary_operand(self, op: B, parent: u8, right: bool) -> String {
        // GCC's -Wparentheses also asks for grouping in mixed bit arithmetic,
        // even when precedence determines a unique parse.
        if matches!(op, B::And | B::Or | B::Xor | B::Shl | B::Shr)
            && self.precedence > parent
            && self.precedence < 13
        {
            format!("({})", self.code)
        } else {
            self.operand(parent, right)
        }
    }
}

pub(super) fn expression(root: &Expr, register: impl Fn(Reg) -> String) -> String {
    render(root, &register).code
}

fn render(expr: &Expr, register: &impl Fn(Reg) -> String) -> Rendered {
    match expr {
        Expr::Const(value) => Rendered::atom(format!("UINT64_C({value})")),
        Expr::Register(reg) => Rendered::atom(register(*reg)),
        Expr::Unary(op, value) => Rendered::atom(format!(
            "{}({})",
            super::integer::unary_helper_name(*op),
            render(value, register).code
        )),
        Expr::Load { address, width } => Rendered::atom(format!(
            "nirvana_load(&m, {}, {})",
            render(address, register).code,
            width.bytes()
        )),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Rendered {
            code: format!(
                "{} ? {} : {}",
                if matches!(
                    **condition,
                    Expr::Binary(B::Mul | B::Shl, ..) | Expr::Select { .. }
                ) {
                    format!(
                        "{} != UINT64_C(0)",
                        render(condition, register).operand(6, false)
                    )
                } else {
                    render(condition, register).operand(2, false)
                },
                render(taken, register).code,
                render(not_taken, register).code
            ),
            precedence: 1,
        },
        Expr::Binary(op, left, right) if super::integer::helper_name(*op).is_some() => {
            Rendered::atom(format!(
                "{}({}, {})",
                super::integer::helper_name(*op).unwrap(),
                render(left, register).code,
                render(right, register).code
            ))
        }
        Expr::Binary(op, left, right) => {
            let (operator, precedence) = match op {
                B::Or => ("|", 3),
                B::Xor => ("^", 4),
                B::And => ("&", 5),
                B::Eq => ("==", 6),
                B::Ne => ("!=", 6),
                B::Ult => ("<", 7),
                B::Ule => ("<=", 7),
                B::Shl => ("<<", 8),
                B::Shr => (">>", 8),
                B::Add => ("+", 9),
                B::Sub => ("-", 9),
                B::Mul => ("*", 10),
                B::UMulHigh | B::SMulHigh | B::AShr => unreachable!(),
            };
            let left = render(left, register).binary_operand(*op, precedence, false);
            let right = if matches!(op, B::Shl | B::Shr) {
                match &**right {
                    Expr::Const(value) => (value & 63).to_string(),
                    _ => {
                        let count = render(right, register).binary_operand(B::And, 5, false);
                        format!("({count} & UINT64_C(63))")
                    }
                }
            } else {
                render(right, register).binary_operand(*op, precedence, true)
            };
            let code = format!("{left} {operator} {right}");
            if matches!(op, B::Eq | B::Ne | B::Ult | B::Ule) {
                Rendered::atom(format!("((uint64_t)({code}))"))
            } else {
                Rendered { code, precedence }
            }
        }
    }
}

#[cfg(test)]
#[path = "compact_tests.rs"]
mod tests;
