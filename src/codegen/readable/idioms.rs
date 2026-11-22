//! Pure expression views and definitions for the selected C layout.
use crate::codegen::emit::integer;
use crate::model::ir::{BinaryOp as B, Expr};
use crate::transform::add_division_expr;
use crate::transform::bit_expr::{self, BitKind};
use crate::transform::division_expr;
use crate::transform::narrow_division_expr;
use crate::transform::narrow_rotate::{self, Direction, NarrowRotate, NarrowWidth};
use crate::transform::remainder_expr;
use crate::transform::signed_division_expr;
use crate::transform::signed_expr::{self, SignedKind};
use crate::transform::word_signed_division::{self, Operation};

pub(super) enum View<'a> {
    WordSignedExtended {
        operation: Operation,
        value: &'a Expr,
        divisor: i64,
        bits: u32,
    },
    WordSigned {
        name: &'static str,
        value: &'a Expr,
        divisor: i64,
        bits: u32,
    },
    Signed {
        name: &'static str,
        value: &'a Expr,
        divisor: i64,
    },
    Call {
        name: &'static str,
        arguments: Vec<&'a Expr>,
    },
    Divide {
        value: &'a Expr,
        divisor: u64,
    },
    Remainder {
        value: &'a Expr,
        divisor: u64,
    },
}

pub(super) fn recognize(expression: &Expr) -> Option<View<'_>> {
    if let Some(view) = word_primitive(expression) {
        return Some(view);
    }
    if let Expr::Binary(op, value, divisor) = expression
        && let Expr::Const(d) = **divisor
    {
        match op {
            B::UDiv if d != 0 => return Some(View::Divide { value, divisor: d }),
            B::URem if d != 0 => return Some(View::Remainder { value, divisor: d }),
            B::SDiv | B::SRem => {
                if let Expr::Unary(crate::model::ir::UnaryOp::SignExtend(width), input) = &**value
                    && *width != crate::model::ir::Width::U64
                    && (d as i64).unsigned_abs() >= 2
                    && (d as i64).unsigned_abs() < (1 << (width.bits() - 1))
                {
                    return Some(View::WordSignedExtended {
                        operation: if *op == B::SDiv {
                            Operation::Quotient
                        } else {
                            Operation::Remainder
                        },
                        value: input,
                        divisor: d as i64,
                        bits: width.bits(),
                    });
                }
                return Some(View::Signed {
                    name: if *op == B::SDiv {
                        "nirvana_sdiv64"
                    } else {
                        "nirvana_srem64"
                    },
                    value,
                    divisor: d as i64,
                });
            }
            _ => {}
        }
    }
    if let Some(view) = word_signed_division::recognize(expression) {
        return Some(View::WordSigned {
            name: match view.operation {
                Operation::Quotient => "nirvana_sdiv_word",
                Operation::Remainder => "nirvana_srem_word",
            },
            value: view.value,
            divisor: view.divisor,
            bits: view.width.bits(),
        });
    }
    if let Some(view) = signed_division_expr::recognize_remainder(expression) {
        return Some(View::Signed {
            name: "nirvana_srem64",
            value: view.value,
            divisor: view.divisor,
        });
    }
    if let Some(view) = signed_division_expr::recognize(expression) {
        return Some(View::Signed {
            name: "nirvana_sdiv64",
            value: view.value,
            divisor: view.divisor,
        });
    }
    if let Some(view) = remainder_expr::recognize(expression) {
        return Some(View::Remainder {
            value: view.value,
            divisor: view.divisor,
        });
    }
    if let Some(view) = division_expr::recognize(expression) {
        return Some(View::Divide {
            value: view.value,
            divisor: view.divisor,
        });
    }
    if let Some(view) = narrow_division_expr::recognize(expression) {
        return Some(View::Divide {
            value: view.value,
            divisor: view.divisor,
        });
    }
    if let Some(view) = add_division_expr::recognize(expression) {
        return Some(View::Divide {
            value: view.value,
            divisor: view.divisor,
        });
    }
    if let Some(view) = signed_expr::recognize(expression) {
        return Some(View::Call {
            name: view.kind.helper_name(),
            arguments: vec![view.left, view.right],
        });
    }
    if let Some(view) = narrow_rotate::recognize_masked(expression) {
        return Some(View::Call {
            name: view.helper_name(),
            arguments: vec![view.value, view.count],
        });
    }
    let view = bit_expr::recognize(expression)?;
    let mut arguments = vec![view.value];
    arguments.extend(view.count);
    Some(View::Call {
        name: view.kind.helper_name(),
        arguments,
    })
}

pub(super) fn preserve_mask(expression: &Expr) -> bool {
    narrow_rotate::recognize_masked(expression).is_some()
        || word_signed_division::recognize(expression).is_some()
        || word_primitive(expression).is_some()
}

fn word_primitive(expression: &Expr) -> Option<View<'_>> {
    let Expr::Binary(B::And, a, b) = expression else {
        return None;
    };
    for (low, mask) in [(&**a, &**b), (&**b, &**a)] {
        let Expr::Const(mask) = mask else { continue };
        let width = [
            crate::model::ir::Width::U8,
            crate::model::ir::Width::U16,
            crate::model::ir::Width::U32,
        ]
        .into_iter()
        .find(|w| w.mask() == *mask)?;
        let Expr::Binary(op @ (B::SDiv | B::SRem), input, divisor) = low else {
            continue;
        };
        let Expr::Const(d) = **divisor else { continue };
        let Expr::Unary(crate::model::ir::UnaryOp::SignExtend(w), value) = &**input else {
            continue;
        };
        if *w != width {
            continue;
        }
        return Some(View::WordSigned {
            name: if *op == B::SDiv {
                "nirvana_sdiv_word"
            } else {
                "nirvana_srem_word"
            },
            value,
            divisor: d as i64,
            bits: width.bits(),
        });
    }
    None
}

pub(super) fn definitions(code: &str) -> String {
    let mut definitions = integer::selected_helpers(code);
    if code.contains("nirvana_sdiv_word(") || code.contains("nirvana_srem_word(") {
        definitions.push_str(word_signed_division::DIVIDE_HELPER);
    }
    if code.contains("nirvana_srem_word(") {
        definitions.push_str(word_signed_division::REMAINDER_HELPER);
    }
    let mut include = |name: &str, definition: &str| {
        if code.contains(&format!("{name}(")) {
            definitions.push_str(definition);
        }
    };
    for kind in [
        BitKind::Rol64,
        BitKind::Ror64,
        BitKind::Bswap32,
        BitKind::Bswap64,
    ] {
        include(kind.helper_name(), kind.c_helper());
    }
    for kind in [SignedKind::Slt64, SignedKind::Sle64] {
        include(kind.helper_name(), kind.c_helper());
    }
    let placeholder = Expr::Const(0);
    for width in [NarrowWidth::U8, NarrowWidth::U16, NarrowWidth::U32] {
        for direction in [Direction::Left, Direction::Right] {
            let view = NarrowRotate {
                width,
                direction,
                value: &placeholder,
                count: &placeholder,
            };
            include(view.helper_name(), view.c_helper());
        }
    }
    definitions
}
