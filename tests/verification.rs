//! verification integration suite.
#[path = "support"]
mod support {
    pub mod ir;
    pub mod rewrite_cases;
    pub mod signed_reciprocals;
    pub mod word_reciprocals;
}

#[path = "verification/block_verification.rs"]
mod block_verification;
#[path = "verification/division_ops.rs"]
mod division_ops;
#[path = "verification/exhaustive.rs"]
mod exhaustive;
#[path = "verification/integer_ops.rs"]
mod integer_ops;
#[path = "verification/known_bits.rs"]
mod known_bits;
#[path = "verification/memory_bits.rs"]
mod memory_bits;
#[path = "verification/memory_values.rs"]
mod memory_values;
#[path = "verification/recovery_verification.rs"]
mod recovery_verification;
#[path = "verification/unary_ops.rs"]
mod unary_ops;
#[path = "verification/verification.rs"]
mod verification;

#[path = "verification/word_signed.rs"]
mod word_signed;
