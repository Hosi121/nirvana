//! Shared fixture construction, native transport and observation helpers.
pub mod checked_c;
pub mod dispatch_oracle;
pub mod ir;
pub mod loop_headers;
pub mod memory_trace;
pub mod module_fixture;
pub mod native;
#[path = "../../examples/programs/mod.rs"]
pub mod programs;
pub mod rewrite_cases;
