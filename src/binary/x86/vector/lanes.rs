//! Pure SSE2 lane expressions. The decoder owns operands and immediates;
//! the caller snapshots both results before committing any XMM lane.
use super::{BinaryOp, Expr, lane, r};

fn shift(value: Expr, count: u64, left: bool) -> Expr {
    if count == 0 {
        value
    } else {
        Expr::binary(
            if left { BinaryOp::Shl } else { BinaryOp::Shr },
            value,
            Expr::Const(count),
        )
    }
}

pub(super) fn shift_quadwords(register: u8, count: u8) -> (Expr, Expr) {
    if count >= 64 {
        return (Expr::Const(0), Expr::Const(0));
    }
    (
        shift(r(lane(register, false)), u64::from(count), false),
        shift(r(lane(register, true)), u64::from(count), false),
    )
}

pub(super) fn shift_bytes(register: u8, count: u8) -> (Expr, Expr) {
    let low = r(lane(register, false));
    let high = r(lane(register, true));
    match count {
        0 => (low, high),
        1..=7 => (
            Expr::binary(
                BinaryOp::Or,
                shift(low, u64::from(count) * 8, false),
                shift(high.clone(), 64 - u64::from(count) * 8, true),
            ),
            shift(high, u64::from(count) * 8, false),
        ),
        8..=15 => (shift(high, u64::from(count - 8) * 8, false), Expr::Const(0)),
        _ => (Expr::Const(0), Expr::Const(0)),
    }
}

pub(super) fn shuffle_dwords(register: u8, order: u8) -> (Expr, Expr) {
    let dword = |index: u8| {
        Expr::binary(
            BinaryOp::And,
            shift(
                r(lane(register, index >= 2)),
                u64::from(index & 1) * 32,
                false,
            ),
            Expr::Const(u64::from(u32::MAX)),
        )
    };
    let pair = |part: u8| {
        Expr::binary(
            BinaryOp::Or,
            dword((order >> part) & 3),
            shift(dword((order >> (part + 2)) & 3), 32, true),
        )
    };
    (pair(0), pair(4))
}
