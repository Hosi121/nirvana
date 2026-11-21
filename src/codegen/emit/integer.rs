//! Portable C11 implementations of total 64-bit bit-vector operations.
use crate::model::ir::{BinaryOp, Program};

pub(crate) const MULTIPLY_HELPER: &str = r#"
static inline uint64_t nirvana_umul_high(uint64_t a, uint64_t b) {
    uint64_t a0 = a & UINT64_C(0xffffffff), a1 = a >> 32;
    uint64_t b0 = b & UINT64_C(0xffffffff), b1 = b >> 32;
    uint64_t low = a0 * b0;
    uint64_t t = a1 * b0 + (low >> 32);
    uint64_t middle = (t & UINT64_C(0xffffffff)) + a0 * b1;
    return a1 * b1 + (t >> 32) + (middle >> 32);
}
"#;

const SIGNED_MULTIPLY_HELPER: &str = r#"
static inline uint64_t nirvana_smul_high(uint64_t a, uint64_t b) {
    return nirvana_umul_high(a,b) - (a >> 63) * b - (b >> 63) * a;
}
"#;

const SHIFT_HELPER: &str = r#"
static inline uint64_t nirvana_ashr64(uint64_t value, uint64_t count) {
    unsigned n = (unsigned)(count & UINT64_C(63));
    if (n == 0) return value;
    return (value >> n) | ((UINT64_C(0) - (value >> 63)) << (64 - n));
}
"#;

pub(crate) fn helper_name(op: BinaryOp) -> Option<&'static str> {
    match op {
        BinaryOp::UMulHigh => Some("nirvana_umul_high"),
        BinaryOp::SMulHigh => Some("nirvana_smul_high"),
        BinaryOp::AShr => Some("nirvana_ashr64"),
        _ => None,
    }
}

fn definitions(used: impl Fn(BinaryOp) -> bool) -> String {
    let mut out = String::new();
    let signed = used(BinaryOp::SMulHigh);
    if signed || used(BinaryOp::UMulHigh) {
        out.push_str(MULTIPLY_HELPER);
    }
    if signed {
        out.push_str(SIGNED_MULTIPLY_HELPER);
    }
    if used(BinaryOp::AShr) {
        out.push_str(SHIFT_HELPER);
    }
    out
}

pub(crate) fn append_helpers(program: &Program, code: &mut String) {
    code.push_str(&definitions(|op| program.uses_operator(op)));
}

/// Module effects can carry expressions outside their scalar shape metadata.
pub(crate) fn append_module_helpers(code: &mut String) {
    code.push_str(&definitions(|_| true));
}

/// Readable expression selection can eliminate an operation's last use.
pub(crate) fn selected_helpers(code: &str) -> String {
    definitions(|op| code.contains(&format!("{}(", helper_name(op).unwrap())))
}
