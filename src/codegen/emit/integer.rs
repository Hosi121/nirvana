//! Portable C11 implementations of total 64-bit bit-vector operations.
use crate::model::ir::{BinaryOp, Program, UnaryOp, Width};

const EXTEND_HELPERS: [(Width, &str, &str); 4] = [
    (
        Width::U8,
        "nirvana_sext8",
        "\nstatic inline uint64_t nirvana_sext8(uint64_t value) { return ((value & UINT64_C(255)) ^ UINT64_C(128)) - UINT64_C(128); }\n",
    ),
    (
        Width::U16,
        "nirvana_sext16",
        "\nstatic inline uint64_t nirvana_sext16(uint64_t value) { return ((value & UINT64_C(65535)) ^ UINT64_C(32768)) - UINT64_C(32768); }\n",
    ),
    (
        Width::U32,
        "nirvana_sext32",
        "\nstatic inline uint64_t nirvana_sext32(uint64_t value) { return ((value & UINT64_C(4294967295)) ^ UINT64_C(2147483648)) - UINT64_C(2147483648); }\n",
    ),
    (
        Width::U64,
        "nirvana_sext64",
        "\nstatic inline uint64_t nirvana_sext64(uint64_t value) { return value; }\n",
    ),
];

pub(crate) fn unary_helper_name(op: UnaryOp) -> &'static str {
    let UnaryOp::SignExtend(width) = op;
    EXTEND_HELPERS
        .iter()
        .find(|(w, _, _)| *w == width)
        .unwrap()
        .1
}

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

const UNSIGNED_DIVIDE_HELPER: &str = r#"
static inline uint64_t nirvana_udiv64(uint64_t value, uint64_t divisor) {
    return divisor == UINT64_C(0) ? UINT64_MAX : value / divisor;
}
"#;
const UNSIGNED_REMAINDER_HELPER: &str = r#"
static inline uint64_t nirvana_urem64(uint64_t value, uint64_t divisor) {
    return divisor == UINT64_C(0) ? value : value % divisor;
}
"#;
pub const SIGNED_DIVIDE_HELPER: &str = r#"
static inline uint64_t nirvana_sdiv64(uint64_t value, uint64_t divisor) {
    uint64_t magnitude = (value >> 63) ? UINT64_C(0) - value : value;
    uint64_t denominator = (divisor >> 63) ? UINT64_C(0) - divisor : divisor;
    uint64_t q = denominator == UINT64_C(0) ? UINT64_MAX : magnitude / denominator;
    return ((value ^ divisor) >> 63) ? UINT64_C(0) - q : q;
}
"#;
pub const SIGNED_REMAINDER_HELPER: &str = r#"
static inline uint64_t nirvana_srem64(uint64_t value, uint64_t divisor) {
    return value - nirvana_sdiv64(value,divisor) * divisor;
}
"#;

pub(crate) fn helper_name(op: BinaryOp) -> Option<&'static str> {
    match op {
        BinaryOp::UMulHigh => Some("nirvana_umul_high"),
        BinaryOp::SMulHigh => Some("nirvana_smul_high"),
        BinaryOp::AShr => Some("nirvana_ashr64"),
        BinaryOp::UDiv => Some("nirvana_udiv64"),
        BinaryOp::URem => Some("nirvana_urem64"),
        BinaryOp::SDiv => Some("nirvana_sdiv64"),
        BinaryOp::SRem => Some("nirvana_srem64"),
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
    if used(BinaryOp::UDiv) {
        out.push_str(UNSIGNED_DIVIDE_HELPER);
    }
    if used(BinaryOp::URem) {
        out.push_str(UNSIGNED_REMAINDER_HELPER);
    }
    if used(BinaryOp::SDiv) || used(BinaryOp::SRem) {
        out.push_str(SIGNED_DIVIDE_HELPER);
    }
    if used(BinaryOp::SRem) {
        out.push_str(SIGNED_REMAINDER_HELPER);
    }
    out
}

pub(crate) fn append_helpers(program: &Program, code: &mut String) {
    code.push_str(&definitions(|op| program.uses_operator(op)));
    for (width, _, definition) in EXTEND_HELPERS {
        if program.uses_unary_operator(UnaryOp::SignExtend(width)) {
            code.push_str(definition);
        }
    }
}

/// Module effects can carry expressions outside their scalar shape metadata.
pub(crate) fn append_module_helpers(code: &mut String) {
    code.push_str(&definitions(|_| true));
    for (_, _, definition) in EXTEND_HELPERS {
        code.push_str(definition);
    }
}

/// Readable expression selection can eliminate an operation's last use.
pub(crate) fn selected_helpers(code: &str) -> String {
    let mut out = definitions(|op| code.contains(&format!("{}(", helper_name(op).unwrap())));
    for (_, name, definition) in EXTEND_HELPERS {
        if code.contains(&format!("{name}(")) {
            out.push_str(definition);
        }
    }
    out
}
