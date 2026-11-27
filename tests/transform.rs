//! transform integration suite.
#[path = "support"]
mod support {
    #[allow(dead_code)]
    pub mod checked_c;
    pub mod ir;
    pub mod native;
    #[path = "../../examples/programs/mod.rs"]
    pub mod programs;
    pub mod projections;
    pub mod signed_reciprocals;
    pub mod word_reciprocals;
}

#[path = "transform/access_expr.rs"]
mod access_expr;
#[path = "transform/add_division_expr.rs"]
mod add_division_expr;
#[path = "transform/affine_region.rs"]
mod affine_region;
#[path = "transform/arithmetic_graph.rs"]
mod arithmetic_graph;
#[path = "transform/bit_expr.rs"]
mod bit_expr;
#[path = "transform/context_remainder.rs"]
mod context_remainder;
#[path = "transform/display_dce.rs"]
mod display_dce;
#[path = "transform/division_expr.rs"]
mod division_expr;
#[path = "transform/finite_region.rs"]
mod finite_region;
#[path = "transform/for_loop.rs"]
mod for_loop;
#[path = "transform/guarded_loop.rs"]
mod guarded_loop;
#[path = "transform/indexed.rs"]
mod indexed;
#[path = "transform/load_consumer.rs"]
mod load_consumer;
#[path = "transform/load_mask.rs"]
mod load_mask;
#[path = "transform/narrow_division_expr.rs"]
mod narrow_division_expr;
#[path = "transform/narrow_rotate.rs"]
mod narrow_rotate;
#[path = "transform/reduction.rs"]
mod reduction;
#[path = "transform/remainder_expr.rs"]
mod remainder_expr;
#[path = "transform/remainder_graph.rs"]
mod remainder_graph;
#[path = "transform/self_update.rs"]
mod self_update;
#[path = "transform/sequence.rs"]
mod sequence;
#[path = "transform/signed_division_expr.rs"]
mod signed_division_expr;
#[path = "transform/signed_expr.rs"]
mod signed_expr;
#[path = "transform/simplify.rs"]
mod simplify;
#[path = "transform/unary_guards.rs"]
mod unary_guards;
#[path = "transform/word_signed_division.rs"]
mod word_signed_division;
