//! Signed reciprocal kernels projected onto an explicit 8/16/32-bit word.
//!
//! Projection commutes with ring operations, masks retaining all word bits and
//! extension from at least that width. It does not commute with right shifts.
//! The latter require an explicit signed input and a full signed product.
use super::pure_expression::Work;
use super::reciprocal_bounds::SignedReciprocal;
use crate::model::ir::{BinaryOp as B, Expr, UnaryOp as U, Width};

pub use super::pure_expression::{MAX_DEPTH, MAX_NODES, MAX_WORK};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Operation {
    Quotient,
    Remainder,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Evidence {
    pub multiplier: u64,
    pub shift: u32,
    pub excess: u64,
    pub positive_bound: u128,
    pub negative_bound: u128,
}

#[derive(Clone, Copy, Debug)]
pub struct View<'a> {
    /// Actual source subtree; the helper projects its low word on entry.
    pub value: &'a Expr,
    pub width: Width,
    pub divisor: i64,
    pub operation: Operation,
    pub evidence: Evidence,
}

#[derive(Clone, Copy)]
struct Kernel<'a> {
    value: &'a Expr,
    multiplier: u64,
    shift: u32,
    negate: bool,
}

/// Output is a zero-extended word, as with an x86-64 EAX write. An enclosing
/// sign extension, if present, remains a separate executable operation.
pub fn recognize(expression: &Expr) -> Option<View<'_>> {
    let (width, low) = root(expression)?;
    let mut work = Work::new();
    work.pure(expression)?;
    candidates(low, width, &mut work)?
        .into_iter()
        .find(|view| validate(expression, view))
}

/// Rebind the numerator to the source, reparse every shift/correction and
/// recompute the numerical certificate. Cloned trees do not bind evidence.
pub fn validate(expression: &Expr, view: &View<'_>) -> bool {
    let Some((width, low)) = root(expression) else {
        return false;
    };
    if width != view.width {
        return false;
    }
    let mut work = Work::new();
    if work.pure(expression).is_none() {
        return false;
    }
    candidates(low, width, &mut work).is_some_and(|candidates| {
        candidates.into_iter().any(|v| {
            std::ptr::eq(v.value, view.value)
                && v.divisor == view.divisor
                && v.operation == view.operation
                && v.evidence == view.evidence
        })
    })
}

fn root(e: &Expr) -> Option<(Width, &Expr)> {
    let (a, b) = binary(e, B::And)?;
    for (low, mask) in [(a, b), (b, a)] {
        for width in [Width::U8, Width::U16, Width::U32] {
            if matches!(mask, Expr::Const(m) if *m == width.mask()) {
                return Some((width, low));
            }
        }
    }
    None
}

fn certified(kernel: Kernel<'_>, width: Width) -> Option<View<'_>> {
    let proof = SignedReciprocal::infer(kernel.multiplier, width.bits(), kernel.shift)?;
    let divisor = i64::try_from(proof.divisor).ok()?;
    Some(View {
        value: kernel.value,
        width,
        divisor: if kernel.negate { -divisor } else { divisor },
        operation: Operation::Quotient,
        evidence: Evidence {
            multiplier: kernel.multiplier,
            shift: kernel.shift,
            excess: proof.excess,
            positive_bound: proof.positive_bound,
            negative_bound: proof.negative_bound,
        },
    })
}

fn candidates<'a>(low: &'a Expr, width: Width, work: &mut Work) -> Option<Vec<View<'a>>> {
    let mut result = Vec::new();
    for kernel in quotients(low, width, work)? {
        result.extend(certified(kernel, width));
    }
    let Some((value, product)) = binary(project(low, width, work)?, B::Sub) else {
        return Some(result);
    };
    // A homogeneous ring expression handles q*D, shifts and LEA-style sums.
    // Right shifts, selects and unrelated leaves supply no coefficient.
    let mut pending = vec![product];
    while let Some(e) = pending.pop() {
        work.spend()?;
        for kernel in quotients(e, width, work)? {
            let Some(mut view) = certified(kernel, width) else {
                continue;
            };
            if same_word(value, view.value, width, work)?
                && coefficient(product, e, width, work)? == Some(view.divisor as u64 & width.mask())
            {
                view.value = value;
                view.operation = Operation::Remainder;
                result.push(view);
            }
        }
        match e {
            Expr::Unary(_, v) => pending.push(v),
            Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
            _ => {}
        }
    }
    Some(result)
}

fn quotients<'a>(e: &'a Expr, width: Width, work: &mut Work) -> Option<Vec<Kernel<'a>>> {
    work.spend()?;
    let Some((a, b)) = binary(project(e, width, work)?, B::Sub) else {
        return Some(Vec::new());
    };
    let mut result = Vec::new();
    for (estimate, sign, negate) in [(a, b, false), (b, a, true)] {
        let Some((signed, count)) = binary(project(sign, width, work)?, B::AShr) else {
            continue;
        };
        if !matches!(count, Expr::Const(n) if *n == u64::from(width.bits()-1) || *n == 63) {
            continue;
        }
        let Some(sign_value) = signed_input(signed, width, work)? else {
            continue;
        };
        for mut kernel in estimates(estimate, width, work)? {
            if same_word(kernel.value, sign_value, width, work)? {
                kernel.negate = negate;
                result.push(kernel);
            }
        }
    }
    Some(result)
}

fn estimates<'a>(e: &'a Expr, width: Width, work: &mut Work) -> Option<Vec<Kernel<'a>>> {
    let e = project(e, width, work)?;
    let mut result = Vec::new();
    // Fused arithmetic shift of the full 2w-bit signed product.
    if let Some(kernel) = high_product(e, width, work)?
        && kernel.multiplier >> (width.bits() - 1) == 0
    {
        result.push(kernel);
    }
    let (core, shift) = match binary(e, B::AShr) {
        Some((signed, Expr::Const(n))) if *n < u64::from(width.bits()) => {
            let Some(core) = signed_input(signed, width, work)? else {
                return Some(result);
            };
            (core, *n as u32)
        }
        _ => (e, 0),
    };
    let core = project(core, width, work)?;
    let terms = match binary(core, B::Add) {
        Some((a, b)) => vec![(a, Some(b)), (b, Some(a))],
        None => vec![(core, None)],
    };
    for (high, add) in terms {
        let Some(mut kernel) = high_product(project(high, width, work)?, width, work)? else {
            continue;
        };
        if kernel.shift != 0 || (kernel.multiplier >> (width.bits() - 1) != 0) != add.is_some() {
            continue;
        }
        if let Some(add) = add
            && !same_word(add, kernel.value, width, work)?
        {
            continue;
        }
        kernel.shift = shift;
        result.push(kernel);
    }
    Some(result)
}

fn high_product<'a>(e: &'a Expr, width: Width, work: &mut Work) -> Option<Option<Kernel<'a>>> {
    work.spend()?;
    let (product, shift) = match e {
        Expr::Binary(op @ (B::Shr | B::AShr), product, count) => {
            let Expr::Const(n) = **count else {
                return Some(None);
            };
            let bits = u64::from(width.bits());
            // A logical 64-bit shift is also valid while its missing sign
            // fill stays entirely above the observed low word.
            if n < bits || n >= 2 * bits || (*op == B::Shr && n > 64 - bits) {
                return Some(None);
            }
            (&**product, (n - bits) as u32)
        }
        _ => return Some(None),
    };
    let Some((a, b)) = binary(product, B::Mul) else {
        return Some(None);
    };
    for (value, factor) in [(a, b), (b, a)] {
        let Expr::Const(factor) = factor else {
            continue;
        };
        let m = factor & width.mask();
        if U::SignExtend(width).evaluate(m) != *factor {
            continue;
        }
        let Some(value) = signed_input(value, width, work)? else {
            continue;
        };
        let value = project(value, width, work)?;
        return Some(Some(Kernel {
            value,
            multiplier: m,
            shift,
            negate: false,
        }));
    }
    Some(None)
}

fn signed_input<'a>(e: &'a Expr, width: Width, work: &mut Work) -> Option<Option<&'a Expr>> {
    work.spend()?;
    // Outer all-one masks are full-width identities, unlike a low-word mask.
    let mut e = e;
    while let Some((a, b)) = binary(e, B::And) {
        e = match (a, b) {
            (v, Expr::Const(u64::MAX)) | (Expr::Const(u64::MAX), v) => v,
            _ => break,
        };
        work.spend()?;
    }
    Some(match e {
        Expr::Unary(U::SignExtend(w), value) if *w == width => Some(&**value),
        _ => None,
    })
}

fn project<'a>(mut e: &'a Expr, width: Width, work: &mut Work) -> Option<&'a Expr> {
    loop {
        work.spend()?;
        e = match e {
            Expr::Unary(U::SignExtend(w), v) if w.bits() >= width.bits() => v,
            Expr::Binary(B::And, a, b) => match (&**a, &**b) {
                (v, Expr::Const(m)) | (Expr::Const(m), v) if m & width.mask() == width.mask() => v,
                _ => return Some(e),
            },
            _ => return Some(e),
        };
    }
}

fn same_word(a: &Expr, b: &Expr, width: Width, work: &mut Work) -> Option<bool> {
    let a = project(a, width, work)?;
    let b = project(b, width, work)?;
    work.same(a, b)
}

fn coefficient(e: &Expr, q: &Expr, width: Width, work: &mut Work) -> Option<Option<u64>> {
    let e = project(e, width, work)?;
    if same_word(e, q, width, work)? {
        return Some(Some(1));
    }
    let value = match e {
        Expr::Const(0) => Some(0),
        Expr::Binary(op @ (B::Add | B::Sub), a, b) => {
            match (
                coefficient(a, q, width, work)?,
                coefficient(b, q, width, work)?,
            ) {
                (Some(a), Some(b)) => Some(op.evaluate(a, b)),
                _ => None,
            }
        }
        Expr::Binary(B::Mul, a, b) => match (&**a, &**b) {
            (v, Expr::Const(n)) | (Expr::Const(n), v) => {
                coefficient(v, q, width, work)?.map(|v| v.wrapping_mul(*n))
            }
            _ => None,
        },
        Expr::Binary(B::And, a, b) => match (&**a, &**b) {
            (v, Expr::Const(mask)) | (Expr::Const(mask), v) => coefficient(v, q, width, work)?
                .filter(|n| {
                    let zeros = if *n == 0 {
                        width.mask()
                    } else {
                        (1u64 << n.trailing_zeros()) - 1
                    };
                    ((!mask) & width.mask() & !zeros) == 0
                }),
            _ => None,
        },
        Expr::Binary(B::Shl, v, n) => match &**n {
            Expr::Const(n) if *n < 64 => {
                coefficient(v, q, width, work)?.map(|v| v.wrapping_shl(*n as u32))
            }
            _ => None,
        },
        _ => None,
    };
    Some(value.map(|n| n & width.mask()))
}

fn binary(e: &Expr, expected: B) -> Option<(&Expr, &Expr)> {
    match e {
        Expr::Binary(op, a, b) if *op == expected => Some((a, b)),
        _ => None,
    }
}

pub const DIVIDE_HELPER: &str = r#"
static inline uint64_t nirvana_sdiv_word(uint64_t value, int64_t divisor, unsigned bits) {
    uint64_t mask = (UINT64_C(1) << bits) - UINT64_C(1);
    uint64_t sign = (value >> (bits - 1)) & UINT64_C(1);
    uint64_t d = (uint64_t)divisor;
    uint64_t magnitude = (sign ? UINT64_C(0) - value : value) & mask;
    uint64_t denominator = divisor < 0 ? UINT64_C(0) - d : d;
    uint64_t q = magnitude / denominator;
    return ((sign ^ (d >> 63)) ? UINT64_C(0) - q : q) & mask;
}
"#;
pub const REMAINDER_HELPER: &str = r#"
static inline uint64_t nirvana_srem_word(uint64_t value, int64_t divisor, unsigned bits) {
    return (value - nirvana_sdiv_word(value, divisor, bits) * (uint64_t)divisor) & ((UINT64_C(1) << bits) - UINT64_C(1));
}
"#;
