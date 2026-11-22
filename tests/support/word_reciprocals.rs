use nirvana::ir::{BinaryOp as B, Expr, Reg, UnaryOp as U, Width};

pub const CASES: [(i64, u32); 10] = [
    (3, 0),
    (5, 1),
    (7, 2),
    (10, 2),
    (11, 1),
    (13, 2),
    (15, 3),
    (17, 3),
    (19, 3),
    (31, 4),
];
pub const WIDTHS: [Width; 3] = [Width::U8, Width::U16, Width::U32];
pub fn cases(width: Width) -> Vec<(i64, u32)> {
    if width == Width::U32 {
        return CASES.to_vec();
    }
    CASES
        .into_iter()
        .map(|(d, _)| (d, d.unsigned_abs().ilog2()))
        .chain([(3, 0), (5, 1)])
        .collect()
}
pub fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
pub fn word(value: Expr, width: Width) -> Expr {
    b(B::And, value, Expr::Const(width.mask()))
}
pub fn sext(value: Expr, width: Width) -> Expr {
    Expr::unary(U::SignExtend(width), value)
}
pub fn magic(width: Width, divisor: i64, shift: u32) -> u64 {
    (1u64 << (width.bits() + shift)).div_ceil(divisor.unsigned_abs())
}
pub fn kernel(width: Width, divisor: i64, shift: u32, split: bool, commute: bool) -> Expr {
    let value = word(Expr::Register(Reg(0)), width);
    let m = magic(width, divisor, shift);
    // Independent signed conversion, rather than UnaryOp::evaluate.
    let encoded = match width {
        Width::U8 => m as i8 as i64 as u64,
        Width::U16 => m as i16 as i64 as u64,
        Width::U32 => m as i32 as i64 as u64,
        Width::U64 => unreachable!(),
    };
    let product = if commute {
        b(B::Mul, Expr::Const(encoded), sext(value.clone(), width))
    } else {
        b(B::Mul, sext(value.clone(), width), Expr::Const(encoded))
    };
    let bits = width.bits();
    let add = m >> (bits - 1) != 0;
    let estimate = if !add && !split {
        b(
            if shift == 0 { B::Shr } else { B::AShr },
            product,
            Expr::Const(u64::from(bits + shift)),
        )
    } else {
        let high = word(b(B::Shr, product, Expr::Const(u64::from(bits))), width);
        let high = if add {
            if commute {
                b(B::Add, value.clone(), high)
            } else {
                b(B::Add, high, value.clone())
            }
        } else {
            high
        };
        if shift == 0 {
            high
        } else {
            b(
                B::AShr,
                sext(word(high, width), width),
                Expr::Const(u64::from(shift)),
            )
        }
    };
    let sign = word(
        b(
            B::AShr,
            sext(value, width),
            Expr::Const(u64::from(bits - 1)),
        ),
        width,
    );
    word(
        if divisor < 0 {
            b(B::Sub, sign, estimate)
        } else {
            b(B::Sub, estimate, sign)
        },
        width,
    )
}

/// Independent fixture for a logical sign correction on the estimate. Bias
/// distribution exercises word equality without changing the full product.
pub fn corrected_kernel(
    width: Width,
    divisor: i64,
    shift: u32,
    sign_before: bool,
    distributed: bool,
) -> Expr {
    let bits = width.bits();
    let base = 1u64 << bits;
    let magnitude = magic(width, divisor, shift);
    let multiplier = if divisor < 0 {
        base.wrapping_sub(magnitude)
    } else {
        magnitude
    };
    let encoded = match width {
        Width::U8 => multiplier as i8 as i64,
        Width::U16 => multiplier as i16 as i64,
        Width::U32 => multiplier as i32 as i64,
        Width::U64 => unreachable!(),
    };
    let input = word(b(B::Add, Expr::Register(Reg(0)), Expr::Const(13)), width);
    let product = b(
        B::Mul,
        sext(input.clone(), width),
        Expr::Const(encoded as u64),
    );
    let high = word(b(B::Shr, product, Expr::Const(u64::from(bits))), width);
    let core = if divisor > 0 && encoded < 0 {
        if distributed {
            b(
                B::Add,
                b(B::Add, high, Expr::Register(Reg(0))),
                Expr::Const(13),
            )
        } else {
            b(B::Add, high, input)
        }
    } else if divisor < 0 && encoded > 0 {
        if distributed {
            b(
                B::Sub,
                b(B::Sub, high, Expr::Const(13)),
                Expr::Register(Reg(0)),
            )
        } else {
            b(B::Sub, high, input)
        }
    } else {
        high
    };
    let estimate = b(
        B::AShr,
        sext(word(core.clone(), width), width),
        Expr::Const(u64::from(shift)),
    );
    let sign = b(
        B::Shr,
        word(if sign_before { core } else { estimate.clone() }, width),
        Expr::Const(u64::from(bits - 1)),
    );
    word(b(B::Add, estimate, sign), width)
}
