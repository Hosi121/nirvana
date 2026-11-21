//! Reduced C with value parameters and locals, observing return and guest memory.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use std::rc::Rc;

use crate::codegen::emit::MEMORY_HELPERS;
use crate::codegen::goto_layout::GotoLayout;
use crate::codegen::loop_labels::LoopLabels;
use crate::control_flow::structure::{Node, StructureError, StructureStats};
use crate::control_flow::structure_verify::StructureEvidence;
use crate::dataflow::value_role::ValueRole;
use crate::model::hir::ViewPath;
use crate::model::ir::{Assignment, BinaryOp, Control, Expr, Place, Program, Reg, Width};
use crate::transform::reduce::{
    ReducedFunction, ReductionError, ReductionStats, reduce, reduce_checked,
};
use crate::transform::sequence::{Evaluation, SequenceError, sequence};
use crate::verification::block_verify::Validation;
use crate::verification::verify::Solver;

mod declarations;
mod idioms;
mod locals;
mod loops;
mod pipeline;
mod prepare;
mod printer;
mod syntax;
mod views;
mod webs;
use declarations::DeclarationPlan;
use locals::LocalPlan;
pub use pipeline::{
    emit_readable_c, emit_readable_c_with_checked_reduction,
    emit_readable_c_with_checked_reduction_and_options, emit_readable_c_with_options,
};
use prepare::{PreparedFunction, is_break, is_continue};
use printer::Printer;
use views::{MemoryViews, VIEW_HELPERS, address_registers, rendered_reads};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReadableError {
    Reduction(ReductionError),
    Sequencing(SequenceError),
    LoopLabelsUnavailable,
}
impl std::fmt::Display for ReadableError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Reduction(error) => error.fmt(f),
            Self::Sequencing(error) => error.fmt(f),
            Self::LoopLabelsUnavailable => {
                f.write_str("loop transfer labels exceed display limits")
            }
        }
    }
}
impl std::error::Error for ReadableError {}
impl From<ReductionError> for ReadableError {
    fn from(error: ReductionError) -> Self {
        Self::Reduction(error)
    }
}
impl From<SequenceError> for ReadableError {
    fn from(error: SequenceError) -> Self {
        Self::Sequencing(error)
    }
}
pub use views::{IndexedView, ObjectField, ObjectView, StackView};

#[derive(Clone, Debug)]
pub struct ReadableC {
    pub code: String,
    /// Input machine-register indices in the emitted argument order.
    pub parameters: Vec<Reg>,
    pub uses_memory: bool,
    pub reduction_stats: ReductionStats,
    pub fallback_reason: Option<StructureError>,
    pub structure_stats: Option<StructureStats>,
    /// Correspondence for the original reduced IR and its Node AST, before
    /// definition-web renaming or any C presentation transforms.
    pub structure_evidence: Option<StructureEvidence>,
    /// Structural correspondence for the selected display IR after validated
    /// web/load-mask/SSA/arithmetic selection, before final C layout.
    /// The original reduced-IR certificate is retained separately above.
    pub display_structure_evidence: Option<StructureEvidence>,
    /// Validated paired display rewrites with unchanged load sites and effects.
    /// The unique-use intermediate receives its mask at the original load site.
    pub load_mask_evidence: Option<crate::transform::load_mask::LoadMaskEvidence>,
    /// Source-bound arithmetic selected before reads, widths and C allocation.
    pub expression_evidence: Option<crate::model::expression_ir::ExpressionEvidence>,
    /// Certified semantic values, captured and substituted before allocation.
    pub semantic_evidence: Option<crate::model::semantic_ir::SemanticEvidence>,
    /// Source-bound constants proved across SSA predecessor and loop phi edges.
    pub ssa_constants: Option<crate::dataflow::ssa_constants::ConstantEvidence>,
    pub web_recovery: WebRecovery,
    /// Named guest-memory locations, not recovered source variables or types.
    pub stack_views: Vec<StackView>,
    pub object_views: Vec<ObjectView>,
    /// Storage widths of named local values; parameters remain uint64_t.
    pub locals: Vec<LocalValue>,
    /// Number of local registers in the selected display IR before C allocation.
    pub local_value_count: usize,
    /// Storage reuse and the finer local identities selected for C naming.
    pub local_plan: LocalPlanStats,
    /// Candidate stack spill/reload lineages in the selected display IR.
    /// These are naming/allocation preferences, not original source identities.
    pub stack_roles: Option<crate::dataflow::stack_role::StackRoles>,
    /// Exact load locations, independent of uncertainty about reaching stores.
    /// Location evidence does not authorize caching or removing a load.
    pub stack_cells: Option<crate::dataflow::stack_cells::CellBindings>,
    /// Exhaustive correspondence for adopted pure finite display regions.
    /// This does not replace either original-IR structure certificate.
    pub finite_regions: Vec<crate::transform::finite_region::FiniteEvidence>,
    /// Correspondence for finite-control regions with one arbitrary u64 input.
    /// Exact affine arithmetic replaces enumeration of that symbolic input.
    pub affine_regions: Vec<crate::transform::affine_region::AffineEvidence>,
}

/// Outcome of the optional definition-web pass. Invalid or unavailable
/// candidates retain the original reduced IR and its rendering path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WebRecovery {
    Unchanged,
    Unavailable,
    Rejected(crate::dataflow::web_verify::WebError),
    StructureFallback(StructureError),
    RenderingFallback(ReadableError),
    Applied {
        stats: crate::dataflow::web::WebStats,
        evidence: crate::dataflow::web_verify::WebEvidence,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LocalValue {
    /// First member in the selected display IR, which may use renamed web IDs.
    pub register: Reg,
    pub registers: Vec<Reg>,
    pub name: String,
    pub width: Width,
    /// Uniform observed guest access width. Storage remains an unsigned u64
    /// address; this hint carries no host pointer or object-size assumption.
    pub address_width: Option<Width>,
    /// A conservative generated storage role, not an original source name.
    pub role: Option<ValueRole>,
}

/// Counts describe generated C locals, not recovered source variables.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct LocalPlanStats {
    /// Slots from the width-partitioned interference allocator.
    pub storage_slots: usize,
    /// Connected identity components, before selecting useful role splits.
    /// None means disabled or the bounded candidate was unavailable.
    pub identity_groups: Option<usize>,
    pub local_variables: usize,
    pub split_storage_groups: usize,
    /// Width pools whose chosen storage map passed independent correspondence.
    pub verified_storage_pools: usize,
    /// Pools whose first allocation/check was unavailable or rejected.
    pub storage_verification_fallbacks: usize,
    /// Heuristic improvement and independent correspondence for an accepted
    /// source-lineage candidate, before optional copy refinement.
    pub source_allocation: Option<crate::dataflow::source_locals::SourceStats>,
    /// Separate heuristic scores for checked direct-copy sharing preferences.
    /// These classes describe copy hints rather than source-variable identities.
    pub copy_allocation: Option<crate::dataflow::source_locals::SourceStats>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct ReadableOptions {
    /// The input register holding the entry stack address. No architecture is
    /// assumed by default; the x86 frontend supplies RSP explicitly.
    pub stack_register: Option<Reg>,
    /// Name proven constant byte offsets from input-register pointer bases.
    /// This does not infer source types or assume that input bases are disjoint.
    pub recover_objects: bool,
    /// Reuse storage across noninterfering local values. Parameters stay fixed.
    pub coalesce_locals: bool,
    /// Compact C11 checked-memory accessors and descriptive input names.
    pub compact_memory: bool,
}

struct Render {
    text: String,
    precedence: u8,
    unsigned: bool,
}
impl Render {
    fn child(&self, precedence: u8) -> String {
        if self.precedence < precedence {
            format!("({})", self.text)
        } else {
            self.text.clone()
        }
    }
    fn u64(&self) -> String {
        if self.unsigned {
            self.child(12)
        } else {
            format!("(uint64_t){}", self.child(12))
        }
    }
}

fn local_type(width: Width, address_width: Option<Width>) -> String {
    match address_width {
        Some(element) if width == Width::U64 => format!("nirvana_u{}_address", element.bits()),
        _ => format!("uint{}_t", width.bits()),
    }
}

fn needs_sequence(expression: &Expr) -> bool {
    let mut pending = vec![expression];
    let mut loads = 0;
    while let Some(expr) = pending.pop() {
        match expr {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Load { address, .. } => {
                loads += 1;
                if loads > 1 {
                    return true;
                }
                pending.push(address);
            }
            Expr::Binary(_, a, b) => {
                pending.push(b);
                pending.push(a);
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push(not_taken);
                pending.push(taken);
                pending.push(condition);
            }
        }
    }
    false
}

fn bounded_shift(expression: &Expr) -> bool {
    match expression {
        Expr::Const(value) => *value <= 63,
        Expr::Binary(BinaryOp::And, left, right) => bounded_shift(left) || bounded_shift(right),
        _ => false,
    }
}

// Stores and unsigned C assignments already truncate. Removing an outer
// constant mask here retains every load and never changes executable IR.
fn stored_value(mut value: &Expr, width: Width) -> &Expr {
    // Preserve the idiom's explicit result mask before recognizing its
    // whole-u64 value, independently of the destination's C storage width.
    if idioms::preserve_mask(value) {
        return value;
    }
    while let Expr::Binary(BinaryOp::And, left, right) = value {
        if let Expr::Const(mask) = **right
            && mask & width.mask() == width.mask()
        {
            value = left;
        } else if let Expr::Const(mask) = **left
            && mask & width.mask() == width.mask()
        {
            value = right;
        } else {
            break;
        }
    }
    value
}

fn line(code: &mut String, indent: usize, text: &str) {
    for part in text.split('\n') {
        writeln!(code, "{}{part}", "    ".repeat(indent)).unwrap();
    }
}

fn max_indent(code: &str) -> usize {
    code.lines()
        .map(|line| line.len() - line.trim_start().len())
        .max()
        .unwrap_or(0)
}

fn contains_continue(nodes: &[Node]) -> bool {
    nodes.iter().any(|node| match node {
        Node::Continue | Node::ContinueOuter { .. } => true,
        Node::Loop(body) => contains_continue(body),
        Node::If {
            taken, not_taken, ..
        } => contains_continue(taken) || contains_continue(not_taken),
        _ => false,
    })
}
