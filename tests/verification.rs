//! verification integration suite.
#[path = "support"]
mod support {
    pub mod bit_insert;
    #[allow(dead_code)]
    pub mod byte_values;
    pub mod ir;
    pub mod projections;
    pub mod pure_prefix;
    pub mod rewrite_cases;
    pub mod signed_reciprocals;
    pub mod word_reciprocals;
}

#[path = "verification/bit_insert.rs"]
mod bit_insert;
#[path = "verification/block_verification.rs"]
mod block_verification;
#[path = "verification/byte_memory.rs"]
mod byte_memory;
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
#[path = "verification/path_inputs.rs"]
mod path_inputs;
#[path = "verification/predicates.rs"]
mod predicates;
#[path = "verification/recovery_verification.rs"]
mod recovery_verification;
#[path = "verification/store_order.rs"]
mod store_order;
#[path = "verification/unary_ops.rs"]
mod unary_ops;
#[path = "verification/vector_lanes.rs"]
mod vector_lanes;
#[path = "verification/verification.rs"]
mod verification;

#[path = "verification/word_correction.rs"]
mod word_correction;
#[path = "verification/word_signed.rs"]
mod word_signed;
