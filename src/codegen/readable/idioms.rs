//! Pure expression views and definitions for the selected C layout.
use crate::codegen::emit::MULTIPLY_HELPER;
use crate::model::ir::Expr;
use crate::transform::add_division_expr;
use crate::transform::bit_expr::{self, BitKind};
use crate::transform::division_expr;
use crate::transform::narrow_division_expr;
use crate::transform::narrow_rotate::{self, Direction, NarrowRotate, NarrowWidth};
use crate::transform::remainder_expr;
use crate::transform::signed_expr::{self, SignedKind};

pub(super) enum View<'a> {
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
}

pub(super) fn definitions(code: &str) -> String {
    let mut definitions = String::new();
    let mut include = |name: &str, definition: &str| {
        if code.contains(&format!("{name}(")) {
            definitions.push_str(definition);
        }
    };
    include("nirvana_umul_high", MULTIPLY_HELPER);
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
