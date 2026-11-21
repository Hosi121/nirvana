//! codegen integration suite.
#[path = "support"]
mod support {
    pub mod checked_c;
    pub mod ir;
    pub mod loop_headers;
    pub mod native;
    #[path = "../../examples/programs/mod.rs"]
    pub mod programs;
}

#[path = "codegen/address_types.rs"]
mod address_types;
#[path = "codegen/affine_backend.rs"]
mod affine_backend;
#[path = "codegen/bit_expr_backend.rs"]
mod bit_expr_backend;
#[path = "codegen/c_evaluation.rs"]
mod c_evaluation;
#[path = "codegen/context_render.rs"]
mod context_render;
#[path = "codegen/declaration_backend.rs"]
mod declaration_backend;
#[path = "codegen/division_backend.rs"]
mod division_backend;
#[path = "codegen/division_render.rs"]
mod division_render;
#[path = "codegen/effects_backend.rs"]
mod effects_backend;
#[path = "codegen/effects_readable.rs"]
mod effects_readable;
#[path = "codegen/emit_sequence.rs"]
mod emit_sequence;
#[path = "codegen/goto_layout.rs"]
mod goto_layout;
#[path = "codegen/indexed_views.rs"]
mod indexed_views;
#[path = "codegen/known_bits_backend.rs"]
mod known_bits_backend;
#[path = "codegen/loop_backend.rs"]
mod loop_backend;
#[path = "codegen/loop_exit_backend.rs"]
mod loop_exit_backend;
#[path = "codegen/loop_header_backend.rs"]
mod loop_header_backend;
#[path = "codegen/loop_labels.rs"]
mod loop_labels;
#[path = "codegen/modulo_backend.rs"]
mod modulo_backend;
#[path = "codegen/nested_for_backend.rs"]
mod nested_for_backend;
#[path = "codegen/nonlocal_backend.rs"]
mod nonlocal_backend;
#[path = "codegen/object_views.rs"]
mod object_views;
#[path = "codegen/presentation.rs"]
mod presentation;
#[path = "codegen/readable.rs"]
mod readable;
#[path = "codegen/signed_division_backend.rs"]
mod signed_division_backend;
#[path = "codegen/signed_expr_backend.rs"]
mod signed_expr_backend;
#[path = "codegen/source_alias_compare.rs"]
mod source_alias_compare;
#[path = "codegen/ssa_backend.rs"]
mod ssa_backend;
#[path = "codegen/stack_views.rs"]
mod stack_views;
#[path = "codegen/typed_address_backend.rs"]
mod typed_address_backend;
#[path = "codegen/typed_locals.rs"]
mod typed_locals;
#[path = "codegen/word_signed_backend.rs"]
mod word_signed_backend;
