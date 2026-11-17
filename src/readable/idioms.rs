//! Pure expression calls and definitions for the selected C layout.
use crate::bit_expr::{self, BitKind};
use crate::ir::Expr;
use crate::narrow_rotate::{self, Direction, NarrowRotate, NarrowWidth};

pub(super) struct Call<'a> {
    pub name: &'static str,
    pub arguments: Vec<&'a Expr>,
}

pub(super) fn recognize(expression: &Expr) -> Option<Call<'_>> {
    if let Some(view) = narrow_rotate::recognize_masked(expression) {
        return Some(Call {
            name: view.helper_name(),
            arguments: vec![view.value, view.count],
        });
    }
    let view = bit_expr::recognize(expression)?;
    let mut arguments = vec![view.value];
    arguments.extend(view.count);
    Some(Call {
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
    for kind in [
        BitKind::Rol64,
        BitKind::Ror64,
        BitKind::Bswap32,
        BitKind::Bswap64,
    ] {
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
