//! Reduced C with value parameters and locals, observing return and guest memory.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use std::rc::Rc;

use crate::block_verify::Validation;
use crate::emit::{MEMORY_HELPERS, MULTIPLY_HELPER};
use crate::goto_layout::GotoLayout;
use crate::hir::ViewPath;
use crate::ir::{Assignment, BinaryOp, Control, Expr, Place, Program, Reg, Width};
use crate::reduce::{ReducedFunction, ReductionError, ReductionStats, reduce, reduce_checked};
use crate::sequence::{Evaluation, SequenceError, sequence};
use crate::structure::{Node, StructureError, StructureStats};
use crate::structure_verify::StructureEvidence;
use crate::value_role::ValueRole;
use crate::verify::Solver;

mod declarations;
mod idioms;
mod locals;
mod loops;
mod prepare;
mod syntax;
mod views;
mod webs;
use declarations::DeclarationPlan;
use locals::LocalPlan;
use prepare::{PreparedFunction, is_break, is_continue};
use views::{MemoryViews, VIEW_HELPERS, address_registers, rendered_reads};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReadableError {
    Reduction(ReductionError),
    Sequencing(SequenceError),
}
impl std::fmt::Display for ReadableError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Reduction(error) => error.fmt(f),
            Self::Sequencing(error) => error.fmt(f),
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
    /// Structural check for the selected display IR, after validated web renaming.
    /// It does not replace the original reduced-IR evidence above.
    pub display_structure_evidence: Option<StructureEvidence>,
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
    pub stack_roles: Option<crate::stack_role::StackRoles>,
    /// Exact load locations, independent of uncertainty about reaching stores.
    /// Location evidence does not authorize caching or removing a load.
    pub stack_cells: Option<crate::stack_cells::CellBindings>,
    /// Exhaustive correspondence for adopted pure finite display regions.
    /// This does not replace either original-IR structure certificate.
    pub finite_regions: Vec<crate::finite_region::FiniteEvidence>,
    /// Correspondence for finite-control regions with one arbitrary u64 input.
    /// Exact affine arithmetic replaces enumeration of that symbolic input.
    pub affine_regions: Vec<crate::affine_region::AffineEvidence>,
}

/// Outcome of the optional definition-web pass. Invalid or unavailable
/// candidates retain the original reduced IR and its rendering path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WebRecovery {
    Unchanged,
    Unavailable,
    Rejected(crate::web_verify::WebError),
    StructureFallback(StructureError),
    RenderingFallback(ReadableError),
    Applied {
        stats: crate::web::WebStats,
        evidence: crate::web_verify::WebEvidence,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LocalValue {
    /// First member in the selected display IR, which may use renamed web IDs.
    pub register: Reg,
    pub registers: Vec<Reg>,
    pub name: String,
    pub width: Width,
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
    /// global source-candidate map. None means the previous map was retained.
    pub source_allocation: Option<crate::source_locals::SourceStats>,
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

struct Printer {
    names: BTreeMap<usize, String>,
    read: BTreeSet<usize>,
    views: Option<MemoryViews>,
    first_temporary: usize,
    widths: BTreeMap<usize, Width>,
    address_uses: BTreeSet<usize>,
    compact_memory: bool,
    slots: BTreeMap<usize, usize>,
    initial_slots: Vec<usize>,
    declarations: Rc<DeclarationPlan>,
}

impl Printer {
    fn expression(&self, expr: &Expr) -> Render {
        self.expression_at(expr, None)
    }

    fn expression_at(&self, expr: &Expr, point: Option<(u64, usize)>) -> Render {
        let atom = |text, unsigned| Render {
            text,
            unsigned,
            precedence: 13,
        };
        if let Some(call) = idioms::recognize(expr) {
            let arguments = call
                .arguments
                .into_iter()
                .map(|argument| self.expression_at(argument, point).text)
                .collect::<Vec<_>>()
                .join(", ");
            return atom(format!("{}({arguments})", call.name), true);
        }
        match expr {
            Expr::Const(value) if *value <= i32::MAX as u64 => atom(value.to_string(), false),
            Expr::Const(value) => atom(format!("UINT64_C(0x{value:x})"), true),
            Expr::Register(reg) => atom(
                self.register(*reg),
                self.widths.get(&reg.0).copied().unwrap_or(Width::U64) == Width::U64,
            ),
            Expr::Load { address, width } => atom(self.load(point, address, address, *width), true),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let condition = self.expression_at(condition, point);
                let taken = self.expression_at(taken, point);
                let not_taken = self.expression_at(not_taken, point);
                Render {
                    text: format!(
                        "{} ? {} : {}",
                        condition.child(3),
                        taken.text,
                        not_taken.child(2)
                    ),
                    precedence: 2,
                    unsigned: taken.unsigned || not_taken.unsigned,
                }
            }
            Expr::Binary(op, left, right) => {
                // Truth wrappers are introduced by control-flow rendering.
                // Only remove/invert these wrappers; general algebra here can
                // erase a variable after dependency/allocation analysis.
                if matches!(op, BinaryOp::Eq | BinaryOp::Ne)
                    && matches!(**right, Expr::Const(0))
                    && matches!(
                        **left,
                        Expr::Binary(
                            BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule,
                            ..
                        )
                    )
                {
                    if *op == BinaryOp::Ne {
                        return self.expression_at(left, point);
                    }
                    let Expr::Binary(inner, a, b) = &**left else {
                        unreachable!()
                    };
                    if matches!(inner, BinaryOp::Eq | BinaryOp::Ne) {
                        let complement = if *inner == BinaryOp::Eq {
                            BinaryOp::Ne
                        } else {
                            BinaryOp::Eq
                        };
                        return self.expression_at(
                            &Expr::binary(complement, (**a).clone(), (**b).clone()),
                            point,
                        );
                    }
                    let symbol = match inner {
                        BinaryOp::Ult => ">=",
                        BinaryOp::Ule => ">",
                        _ => unreachable!(),
                    };
                    return Render {
                        text: format!(
                            "{} {symbol} {}",
                            self.expression_at(a, point).child(9),
                            self.expression_at(b, point).child(9)
                        ),
                        precedence: 8,
                        unsigned: false,
                    };
                }
                if *op == BinaryOp::Add
                    && let Expr::Const(value) = **left
                    && !matches!(**right, Expr::Const(_))
                {
                    return self.expression_at(
                        &Expr::binary(BinaryOp::Add, (**right).clone(), Expr::Const(value)),
                        point,
                    );
                }
                if *op == BinaryOp::Add
                    && let Expr::Const(value) = **right
                    && value > i64::MAX as u64
                {
                    return self.expression_at(
                        &Expr::binary(
                            BinaryOp::Sub,
                            (**left).clone(),
                            Expr::Const(value.wrapping_neg()),
                        ),
                        point,
                    );
                }
                let l = self.expression_at(left, point);
                let r = self.expression_at(right, point);
                if *op == BinaryOp::UMulHigh {
                    return atom(format!("nirvana_umul_high({}, {})", l.text, r.text), true);
                }
                let (symbol, precedence) = match op {
                    BinaryOp::Or => ("|", 4),
                    BinaryOp::Xor => ("^", 5),
                    BinaryOp::And => ("&", 6),
                    BinaryOp::Eq => ("==", 7),
                    BinaryOp::Ne => ("!=", 7),
                    BinaryOp::Ult => ("<", 8),
                    BinaryOp::Ule => ("<=", 8),
                    BinaryOp::Shl => ("<<", 9),
                    BinaryOp::Shr => (">>", 9),
                    BinaryOp::Add => ("+", 10),
                    BinaryOp::Sub => ("-", 10),
                    BinaryOp::Mul => ("*", 11),
                    BinaryOp::UMulHigh => unreachable!(),
                };
                let comparison = matches!(
                    op,
                    BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule
                );
                let shift = matches!(op, BinaryOp::Shl | BinaryOp::Shr);
                // A comparison in C has type int. Promote before wrapping
                // arithmetic and before a shift, not after a possible overflow.
                let promote = !comparison && (!l.unsigned && (!r.unsigned || shift));
                let bitwise = matches!(op, BinaryOp::And | BinaryOp::Or | BinaryOp::Xor);
                // Equal bitwise operators associate without changing any bits.
                // Keep mixed/arithmetic operands parenthesized for C warnings.
                let bitwise_precedence = |operand: &Expr| {
                    if matches!(operand, Expr::Binary(inner, ..) if inner == op) {
                        precedence
                    } else {
                        12
                    }
                };
                let operand_precedence = if bitwise {
                    bitwise_precedence(left)
                } else if shift {
                    12
                } else if comparison {
                    9
                } else {
                    precedence
                };
                let left_text = if promote {
                    l.u64()
                } else {
                    l.child(operand_precedence)
                };
                let right_text = if shift && !bounded_shift(right) {
                    format!("({} & 63)", r.child(12))
                } else {
                    r.child(if bitwise {
                        bitwise_precedence(right)
                    } else if comparison {
                        9
                    } else {
                        precedence + 1
                    })
                };
                Render {
                    text: format!("{left_text} {symbol} {right_text}"),
                    precedence,
                    unsigned: !comparison,
                }
            }
        }
    }

    fn address_value(&self, reg: Reg, point: Option<(u64, usize)>, value: &Expr) -> Option<String> {
        if !self.address_uses.contains(&reg.0) {
            return None;
        }
        self.address_view(point, value)
            .map(|view| format!("{view}.address"))
    }

    fn address_view(&self, point: Option<(u64, usize)>, address: &Expr) -> Option<String> {
        self.views
            .as_ref()?
            .at(point, address)
            .map(|view| view.render(self.compact_memory, |index| self.expression(index).text))
    }

    fn load(
        &self,
        point: Option<(u64, usize)>,
        address: &Expr,
        original: &Expr,
        width: Width,
    ) -> String {
        let view = self.address_view(point, original);
        if self.compact_memory {
            let location = view.unwrap_or_else(|| self.expression_at(address, point).text);
            format!("read{}({location})", width.bits())
        } else if let Some(view) = view {
            format!("nirvana_view_load(&m, {view}, {})", width.bytes())
        } else {
            format!(
                "nirvana_load(&m, {}, {})",
                self.expression_at(address, point).text,
                width.bytes()
            )
        }
    }

    fn register(&self, reg: Reg) -> String {
        if reg.0 >= self.first_temporary {
            format!("nirvana_value_{}", reg.0 - self.first_temporary)
        } else {
            self.names[&reg.0].clone()
        }
    }

    fn evaluations(
        &self,
        code: &mut String,
        indent: usize,
        steps: &[Evaluation],
        point: Option<(u64, usize)>,
    ) {
        for step in steps {
            match step {
                Evaluation::Assign { destination, value } => line(
                    code,
                    indent,
                    &format!(
                        "{} = {};",
                        self.register(*destination),
                        self.expression(value).text
                    ),
                ),
                Evaluation::Load {
                    destination,
                    address,
                    original_address,
                    width,
                } => {
                    let value = self.load(point, address, original_address, *width);
                    line(
                        code,
                        indent,
                        &format!("{} = {value};", self.register(*destination)),
                    );
                }
                Evaluation::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    line(
                        code,
                        indent,
                        &format!("if ({}) {{", self.expression(condition).text),
                    );
                    self.evaluations(code, indent + 1, taken, point);
                    line(code, indent, "} else {");
                    self.evaluations(code, indent + 1, not_taken, point);
                    line(code, indent, "}");
                }
            }
        }
    }

    fn ordered_expression(
        &self,
        code: &mut String,
        indent: usize,
        expr: &Expr,
        point: Option<(u64, usize)>,
        next: &mut usize,
    ) -> Result<Render, SequenceError> {
        if !needs_sequence(expr) {
            return Ok(self.expression_at(expr, point));
        }
        let plan = sequence(expr, *next)?;
        for reg in *next..plan.next_register {
            line(
                code,
                indent,
                &format!("uint64_t {};", self.register(Reg(reg))),
            );
        }
        *next = plan.next_register;
        self.evaluations(code, indent, &plan.steps, point);
        Ok(self.expression(&plan.value))
    }

    fn value_statement(
        &self,
        code: &mut String,
        indent: usize,
        expr: &Expr,
        point: Option<(u64, usize)>,
        prefix: &str,
        suffix: &str,
    ) -> Result<(), SequenceError> {
        let scoped = needs_sequence(expr);
        if scoped {
            line(code, indent, "{");
        }
        let inner = indent + usize::from(scoped);
        let mut next = self.first_temporary;
        let value = self.ordered_expression(code, inner, expr, point, &mut next)?;
        line(code, inner, &format!("{prefix}{}{suffix}", value.text));
        if scoped {
            line(code, indent, "}");
        }
        Ok(())
    }

    fn assignments(
        &self,
        code: &mut String,
        indent: usize,
        address: u64,
        assignments: &[Assignment],
    ) -> Result<(), SequenceError> {
        for (index, assignment) in assignments.iter().enumerate() {
            let point = Some((address, index));
            match &assignment.destination {
                Place::Register(reg) => {
                    if self.read.contains(&reg.0)
                        && let Expr::Register(source) = assignment.value
                        && self.names.contains_key(&source.0)
                        && self.register(*reg) == self.register(source)
                    {
                        continue;
                    }
                    if self.read.contains(&reg.0) {
                        let name = self.register(*reg);
                        let width = self.widths.get(&reg.0).copied().unwrap_or(Width::U64);
                        let initialize = self.declarations.at((address, index), &name);
                        let prefix = if initialize {
                            format!("uint{}_t {name} = ", width.bits())
                        } else {
                            format!("{name} = ")
                        };
                        if let Some(value) = self.address_value(*reg, point, &assignment.value) {
                            line(code, indent, &format!("{prefix}{value};"));
                        } else {
                            let value = stored_value(&assignment.value, width);
                            if !initialize
                                && self.compact_memory
                                && let Some(statement) = self.compound(*reg, value, point)
                            {
                                line(code, indent, &statement);
                                continue;
                            }
                            self.value_statement(code, indent, value, point, &prefix, ";")?;
                        }
                    } else if assignment.value.uses_memory() {
                        self.value_statement(
                            code,
                            indent,
                            &assignment.value,
                            point,
                            "(void)(",
                            ");",
                        )?;
                    }
                }
                Place::Memory { address, width } => {
                    // Evaluate and check the destination before a possibly
                    // faulting RHS, capturing an address exactly once.
                    let scoped = assignment.value.uses_memory() || needs_sequence(address);
                    if scoped {
                        line(code, indent, "{");
                    }
                    let inner = indent + usize::from(scoped);
                    let mut next = self.first_temporary;
                    let view = self.address_view(point, address);
                    let destination = if let Some(view) = &view {
                        format!("{view}.address")
                    } else {
                        let value =
                            self.ordered_expression(code, inner, address, point, &mut next)?;
                        if scoped {
                            line(
                                code,
                                inner,
                                &format!("const uint64_t nirvana_address = {};", value.text),
                            );
                            "nirvana_address".into()
                        } else {
                            value.text
                        }
                    };
                    if scoped {
                        line(
                            code,
                            inner,
                            &format!(
                                "(void)nirvana_offset(&m, {destination}, {});",
                                width.bytes()
                            ),
                        );
                    }
                    let value = self
                        .ordered_expression(
                            code,
                            inner,
                            stored_value(&assignment.value, *width),
                            point,
                            &mut next,
                        )?
                        .text;
                    let statement = if self.compact_memory {
                        format!(
                            "write{}({}, {value});",
                            width.bits(),
                            view.unwrap_or(destination)
                        )
                    } else if let Some(view) = view {
                        format!(
                            "nirvana_view_store(&m, {view}, {}, {value});",
                            width.bytes()
                        )
                    } else {
                        format!(
                            "nirvana_store(&m, {destination}, {}, {value});",
                            width.bytes()
                        )
                    };
                    line(code, inner, &statement);
                    if scoped {
                        line(code, indent, "}");
                    }
                }
            }
        }
        Ok(())
    }

    fn compound(
        &self,
        destination: Reg,
        value: &Expr,
        point: Option<(u64, usize)>,
    ) -> Option<String> {
        if needs_sequence(value) {
            return None;
        }
        let same = |a: Reg, b: Reg| {
            self.names
                .get(&a.0)
                .zip(self.names.get(&b.0))
                .is_some_and(|(a, b)| a == b)
        };
        let (mut op, mut right) =
            crate::self_update::extract(value, destination, same).or_else(|| {
                // Subtraction has no associative-chain rule; preserve the existing
                // direct x=x-y spelling without reassociating any operands.
                if let Expr::Binary(BinaryOp::Sub, left, right) = value
                    && let Expr::Register(source) = **left
                    && same(destination, source)
                {
                    Some((BinaryOp::Sub, (**right).clone()))
                } else {
                    None
                }
            })?;
        // x + (2^64 - n) and x - n have the same unsigned low bits at
        // every supported storage width. Keep small decrements readable.
        if op == BinaryOp::Add
            && let Expr::Const(value) = right
            && value > i64::MAX as u64
        {
            op = BinaryOp::Sub;
            right = Expr::Const(value.wrapping_neg());
        }
        // These are standalone updates (also used as for-loop clauses), so
        // no expression consumes the old or new value. Unsigned ++/-- retain
        // the same wrap and narrowing as the corresponding compound update.
        if right == Expr::Const(1) {
            match op {
                BinaryOp::Add => return Some(format!("++{};", self.register(destination))),
                BinaryOp::Sub => return Some(format!("--{};", self.register(destination))),
                _ => {}
            }
        }
        let symbol = match op {
            BinaryOp::Add => "+",
            BinaryOp::Sub => "-",
            BinaryOp::Mul => "*",
            BinaryOp::And => "&",
            BinaryOp::Or => "|",
            BinaryOp::Xor => "^",
            _ => return None,
        };
        let right = self.expression_at(&right, point);
        // Narrow C integers promote to signed int. Force 64-bit arithmetic
        // before the operation, then let the unsigned destination truncate.
        let right = if self
            .widths
            .get(&destination.0)
            .copied()
            .unwrap_or(Width::U64)
            == Width::U64
        {
            right.text
        } else {
            right.u64()
        };
        Some(format!("{} {symbol}= {right};", self.register(destination)))
    }

    fn loop_clauses(&self, steps: &[Node], update: bool) -> Option<Vec<String>> {
        let mut clauses = Vec::new();
        for step in steps {
            let Node::Step {
                address,
                assignments,
            } = step
            else {
                return None;
            };
            for (index, assignment) in assignments.iter().enumerate() {
                let point = Some((*address, index));
                match &assignment.destination {
                    Place::Register(reg) => {
                        if self.read.contains(&reg.0)
                            && let Expr::Register(source) = assignment.value
                            && self.names.contains_key(&source.0)
                            && self.register(*reg) == self.register(source)
                        {
                            continue;
                        }
                        if self.read.contains(&reg.0) {
                            let width = self.widths.get(&reg.0).copied().unwrap_or(Width::U64);
                            let value = stored_value(&assignment.value, width);
                            if let Some(value) = self.address_value(*reg, point, value) {
                                clauses.push(format!("{} = {value}", self.register(*reg)));
                            } else if update
                                && self.compact_memory
                                && let Some(statement) = self.compound(*reg, value, point)
                            {
                                clauses.push(statement.strip_suffix(';')?.into());
                            } else {
                                clauses.push(format!(
                                    "{} = {}",
                                    self.register(*reg),
                                    self.expression_at(value, point).text
                                ));
                            }
                        } else if assignment.value.uses_memory() {
                            clauses.push(self.expression_at(&assignment.value, point).text);
                        }
                    }
                    Place::Memory { address, width } => {
                        // For-header recovery admits only pure destinations and
                        // pure RHS values. The checked store is the only faulting
                        // operation in this clause, just as in a standalone store.
                        if !update || address.uses_memory() || assignment.value.uses_memory() {
                            return None;
                        }
                        let value = self
                            .expression_at(stored_value(&assignment.value, *width), point)
                            .text;
                        let view = self.address_view(point, address);
                        let text = if self.compact_memory {
                            let destination =
                                view.unwrap_or_else(|| self.expression_at(address, point).text);
                            format!("write{}({destination}, {value})", width.bits())
                        } else if let Some(view) = view {
                            format!("nirvana_view_store(&m, {view}, {}, {value})", width.bytes())
                        } else {
                            format!(
                                "nirvana_store(&m, {}, {}, {value})",
                                self.expression_at(address, point).text,
                                width.bytes()
                            )
                        };
                        clauses.push(text);
                    }
                }
            }
        }
        Some(clauses)
    }

    fn loop_condition(&self, setup: &[Node], condition: &Expr) -> Option<String> {
        let mut clauses = self.loop_clauses(setup, false)?;
        clauses.push(self.expression(condition).text);
        Some(if clauses.len() == 1 {
            clauses.pop()?
        } else {
            format!("({})", clauses.join(", "))
        })
    }

    fn loop_header<'a>(&self, body: &'a [Node]) -> Option<(String, &'a [Node])> {
        if let Some(header) = crate::for_loop::recover(body, |reg| self.slots.get(&reg.0).copied())
        {
            let condition = self.loop_condition(header.setup, &header.condition)?;
            let updates = self.loop_clauses(header.update, true)?;
            if !updates.is_empty() && (!header.body.is_empty() || updates.len() == 1) {
                let header_text = format!("for (; {condition}; {}) {{", updates.join(", "));
                let header_text = if header_text.len() > 100 {
                    format!(
                        "for (;\n     {condition};\n     {}) {{",
                        updates.join(",\n     ")
                    )
                } else {
                    header_text
                };
                return Some((header_text, header.body));
            }
        }
        let header = crate::loop_shape::while_header(body)?;
        let condition = self.loop_condition(header.setup, &header.condition)?;
        Some((format!("while ({condition}) {{"), header.body))
    }

    fn nodes(
        &self,
        code: &mut String,
        nodes: &[Node],
        indent: usize,
        depth: usize,
        nonlocal: bool,
    ) -> Result<(), SequenceError> {
        let facts = crate::guarded_loop::Facts::new(&self.initial_slots);
        self.nodes_with_facts(code, nodes, indent, depth, nonlocal, &facts)
    }

    fn nodes_with_facts(
        &self,
        code: &mut String,
        nodes: &[Node],
        indent: usize,
        depth: usize,
        nonlocal: bool,
        incoming: &crate::guarded_loop::Facts,
    ) -> Result<(), SequenceError> {
        let mut facts = incoming.clone();
        for node in nodes {
            match node {
                Node::Evaluate(value) => {
                    self.value_statement(code, indent, value, None, "(void)(", ");")?;
                }
                Node::Step {
                    address,
                    assignments,
                } => self.assignments(code, indent, *address, assignments)?,
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    if !nonlocal
                        && let Some(loop_view) = crate::guarded_loop::recover(
                            condition,
                            taken,
                            not_taken,
                            &facts,
                            |reg| self.slots.get(&reg.0).copied(),
                        )
                        && self.guard_alias_reads_safe(taken, &loop_view.condition)
                    {
                        // Reuse the existing pre-test/for renderer. The proof
                        // expression is never emitted: this condition is the
                        // original latch, with only proven copy aliases changed.
                        let mut pretest = vec![Node::If {
                            condition: loop_view.condition.clone(),
                            taken: vec![],
                            not_taken: vec![Node::Break],
                        }];
                        pretest.extend_from_slice(loop_view.body);
                        pretest.push(Node::Continue);
                        let loop_facts =
                            facts.enter_loop(loop_view.body, |reg| self.slots.get(&reg.0).copied());
                        if let Some((header, middle)) = self.loop_header(&pretest) {
                            line(code, indent, &header);
                            let middle = if matches!(middle.last(), Some(Node::Continue)) {
                                &middle[..middle.len() - 1]
                            } else {
                                middle
                            };
                            self.nodes_with_facts(
                                code,
                                middle,
                                indent + 1,
                                depth + 1,
                                nonlocal,
                                &loop_facts,
                            )?;
                            line(code, indent, "}");
                            facts.observe(node, |reg| self.slots.get(&reg.0).copied());
                            continue;
                        }
                    }
                    let scoped = needs_sequence(condition);
                    if scoped {
                        line(code, indent, "{");
                    }
                    let inner = indent + usize::from(scoped);
                    let mut next = self.first_temporary;
                    let value = self.ordered_expression(code, inner, condition, None, &mut next)?;
                    line(code, inner, &format!("if ({}) {{", value.text));
                    self.nodes_with_facts(code, taken, inner + 1, depth, nonlocal, &facts)?;
                    if !not_taken.is_empty() {
                        line(code, inner, "} else {");
                        self.nodes_with_facts(code, not_taken, inner + 1, depth, nonlocal, &facts)?;
                    }
                    line(code, inner, "}");
                    if scoped {
                        line(code, indent, "}");
                    }
                }
                Node::Loop(body) => {
                    if !nonlocal && let Some(view) = crate::loop_exit::recover(body) {
                        let loop_facts =
                            facts.enter_loop(body, |reg| self.slots.get(&reg.0).copied());
                        line(code, indent, "do {");
                        self.nodes_with_facts(
                            code,
                            view.body,
                            indent + 1,
                            depth + 1,
                            nonlocal,
                            &loop_facts,
                        )?;
                        let condition = self.expression(view.condition).text;
                        let condition = if view.continue_when {
                            condition
                        } else {
                            format!("!({condition})")
                        };
                        line(code, indent, &format!("}} while ({condition});"));
                        // The exit follows successful loop completion. Entry
                        // constants must not survive writes from any iteration.
                        facts.observe(node, |reg| self.slots.get(&reg.0).copied());
                        self.nodes_with_facts(code, view.exit, indent, depth, nonlocal, &facts)?;
                        continue;
                    }
                    let (header, middle, footer) =
                        if let Some((header, middle)) = self.loop_header(body) {
                            (header, middle, String::from("}"))
                        } else if !nonlocal && let Some(view) = crate::loop_shape::post_test(body) {
                            let condition = self.expression(view.condition).text;
                            let condition = if view.continue_when {
                                condition
                            } else {
                                format!("!({condition})")
                            };
                            ("do {".into(), view.body, format!("}} while ({condition});"))
                        } else {
                            match body.as_slice() {
                                [
                                    prefix @ ..,
                                    Node::If {
                                        condition,
                                        taken,
                                        not_taken,
                                    },
                                ] if is_continue(taken)
                                    && is_break(not_taken)
                                    && !contains_continue(prefix)
                                    && !needs_sequence(condition) =>
                                {
                                    (
                                        "do {".into(),
                                        prefix,
                                        format!("}} while ({});", self.expression(condition).text),
                                    )
                                }
                                _ => ("for (;;) {".into(), body.as_slice(), "}".into()),
                            }
                        };
                    line(code, indent, &header);
                    let middle = if matches!(middle.last(), Some(Node::Continue)) {
                        &middle[..middle.len() - 1]
                    } else {
                        middle
                    };
                    let loop_facts = facts.enter_loop(body, |reg| self.slots.get(&reg.0).copied());
                    self.nodes_with_facts(
                        code,
                        middle,
                        indent + 1,
                        depth + 1,
                        nonlocal,
                        &loop_facts,
                    )?;
                    line(code, indent, &footer);
                    if nonlocal && depth > 0 {
                        line(code, indent, "if (nirvana_transfer != 0) {");
                        line(code, indent + 1, "--nirvana_transfer;");
                        line(
                            code,
                            indent + 1,
                            "if (nirvana_transfer == 0 && nirvana_continue) continue;",
                        );
                        line(code, indent + 1, "break;");
                        line(code, indent, "}");
                    }
                }
                Node::Break => line(code, indent, "break;"),
                Node::Continue => line(code, indent, "continue;"),
                Node::BreakOuter { levels } | Node::ContinueOuter { levels } => {
                    line(code, indent, &format!("nirvana_transfer = {levels};"));
                    line(
                        code,
                        indent,
                        &format!(
                            "nirvana_continue = {};",
                            usize::from(matches!(node, Node::ContinueOuter { .. }))
                        ),
                    );
                    line(code, indent, "break;");
                }
                Node::Return(value) => {
                    self.value_statement(code, indent, value, None, "return ", ";")?
                }
            }
            facts.observe(node, |reg| self.slots.get(&reg.0).copied());
        }
        Ok(())
    }

    fn guard_alias_reads_safe(&self, taken: &[Node], condition: &Expr) -> bool {
        let mut pending = vec![condition];
        while let Some(expr) = pending.pop() {
            match expr {
                Expr::Binary(op, a, b) => {
                    if matches!(
                        op,
                        BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule
                    ) && self.expression(a).text == self.expression(b).text
                    {
                        // A proof under initial constants can accept this, but
                        // emitting x==x would introduce a C diagnostic. Keep the
                        // original guard instead of doing late algebra/DCE.
                        return false;
                    }
                    pending.extend([&**a, &**b]);
                }
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([&**condition, &**taken, &**not_taken]),
                Expr::Load { address, .. } => pending.push(address),
                _ => {}
            }
        }
        if self.views.is_none() {
            return true;
        }
        let [Node::Loop(body)] = taken else {
            return false;
        };
        let Some(Node::If { condition: old, .. }) = body.last() else {
            return false;
        };
        let reads = |expression: &Expr| {
            let mut found = BTreeSet::new();
            let mut pending = vec![expression];
            while let Some(expr) = pending.pop() {
                match expr {
                    Expr::Register(reg) => {
                        if let Some(&slot) = self.slots.get(&reg.0) {
                            found.insert(slot);
                        }
                    }
                    Expr::Const(_) => {}
                    Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
                    Expr::Load { address, .. } => pending.push(address),
                    Expr::Select {
                        condition,
                        taken,
                        not_taken,
                    } => pending.extend([&**condition, &**taken, &**not_taken]),
                }
            }
            found
        };
        let protected: BTreeSet<_> = self
            .address_uses
            .iter()
            .filter_map(|r| self.slots.get(r))
            .copied()
            .collect();
        // Address-view printing may replace a copy's RHS with a captured view.
        // Retain the original guard if it could be the last printed read of
        // such a slot; raw AST copy use alone is insufficient here.
        reads(old)
            .difference(&reads(condition))
            .all(|slot| !protected.contains(slot))
    }

    fn gotos(&self, code: &mut String, program: &Program) -> Result<(), SequenceError> {
        let cfg = program.cfg();
        let layout = GotoLayout::compute(program);
        let order = layout
            .as_ref()
            .map(|l| l.blocks().to_vec())
            .unwrap_or_else(|| cfg.reachable_blocks().into_iter().collect());
        let resolve = |id| layout.as_ref().map_or(id, |l| l.resolve(id));
        let block_at = |address| resolve(cfg.block_at(address).expect("validated destination"));
        let entry = layout.as_ref().map_or(cfg.entry(), |l| l.entry());
        // Only destinations of jumps which survive fallthrough need labels.
        let mut labels = BTreeSet::new();
        if order.first() != Some(&entry) {
            labels.insert(entry);
        }
        for (index, &id) in order.iter().enumerate() {
            let next = order.get(index + 1).copied();
            let block = cfg.block(id);
            let instruction = &program.instructions()[block.instructions.end - 1];
            let mut target = |id| {
                if Some(id) != next {
                    labels.insert(id);
                }
            };
            match &instruction.control {
                Control::Next => {
                    target(block_at(instruction.address + u64::from(instruction.size)))
                }
                Control::Jump(address) => target(block_at(*address)),
                Control::Branch {
                    target: address, ..
                } => {
                    target(block_at(*address));
                    target(block_at(instruction.address + u64::from(instruction.size)));
                }
                Control::Return(_) => {}
            }
        }
        if order.first() != Some(&entry) {
            line(code, 1, &format!("goto {entry};"));
        }
        for (index, &id) in order.iter().enumerate() {
            let next = order.get(index + 1).copied();
            let block = cfg.block(id);
            if labels.contains(&id) {
                writeln!(code, "{id}:").unwrap();
            }
            for instruction in &program.instructions()[block.instructions.clone()] {
                self.assignments(code, 1, instruction.address, &instruction.assignments)?;
            }
            let instruction = &program.instructions()[block.instructions.end - 1];
            match &instruction.control {
                Control::Next | Control::Jump(_) => {
                    let target = match instruction.control {
                        Control::Jump(address) => block_at(address),
                        _ => block_at(instruction.address + u64::from(instruction.size)),
                    };
                    if Some(target) != next {
                        line(code, 1, &format!("goto {target};"));
                    }
                }
                Control::Branch { condition, target } => {
                    let taken = block_at(*target);
                    let not_taken = block_at(instruction.address + u64::from(instruction.size));
                    if taken == not_taken {
                        self.value_statement(code, 1, condition, None, "(void)(", ");")?;
                        if Some(taken) != next {
                            line(code, 1, &format!("goto {taken};"));
                        }
                        continue;
                    }
                    let scoped = needs_sequence(condition);
                    if scoped {
                        line(code, 1, "{");
                    }
                    let inner = 1 + usize::from(scoped);
                    let mut temporary = self.first_temporary;
                    let value =
                        self.ordered_expression(code, inner, condition, None, &mut temporary)?;
                    if Some(taken) == next {
                        line(
                            code,
                            inner,
                            &format!("if (!({})) goto {not_taken};", value.text),
                        );
                    } else {
                        line(code, inner, &format!("if ({}) goto {taken};", value.text));
                        if Some(not_taken) != next {
                            line(code, inner, &format!("goto {not_taken};"));
                        }
                    }
                    if scoped {
                        line(code, 1, "}");
                    }
                }
                Control::Return(value) => {
                    self.value_statement(code, 1, value, None, "return ", ";")?
                }
            }
        }
        Ok(())
    }
}

// A single load has no competing faulting operand. Keep that common machine
// shape compact; multiple/nested loads need explicit evaluation statements.
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

fn nonlocal(nodes: &[Node]) -> bool {
    nodes.iter().any(|node| match node {
        Node::BreakOuter { .. } | Node::ContinueOuter { .. } => true,
        Node::Loop(body) => nonlocal(body),
        Node::If {
            taken, not_taken, ..
        } => nonlocal(taken) || nonlocal(not_taken),
        _ => false,
    })
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
pub fn emit_readable_c(program: &Program) -> Result<ReadableC, ReadableError> {
    emit_readable_c_with_options(program, ReadableOptions::default())
}

pub fn emit_readable_c_with_options(
    program: &Program,
    options: ReadableOptions,
) -> Result<ReadableC, ReadableError> {
    emit_reduced_c(reduce(program)?, options)
}

/// Validate only the IR reduction. Structuring and C emission have their own
/// testing boundary and are not certified by this block model.
pub fn emit_readable_c_with_checked_reduction(
    program: &Program,
    solver: &Solver,
) -> Result<(ReadableC, Validation), ReadableError> {
    emit_readable_c_with_checked_reduction_and_options(program, solver, ReadableOptions::default())
}

pub fn emit_readable_c_with_checked_reduction_and_options(
    program: &Program,
    solver: &Solver,
    options: ReadableOptions,
) -> Result<(ReadableC, Validation), ReadableError> {
    let checked = reduce_checked(program, solver)?;
    Ok((
        emit_reduced_c(checked.function, options)?,
        checked.validation,
    ))
}

fn emit_reduced_c(
    reduced: ReducedFunction,
    options: ReadableOptions,
) -> Result<ReadableC, ReadableError> {
    let prepared = prepare::prepare(reduced.program(), reduced.parameters())?;
    let renamed = matches!(prepared.web_recovery, WebRecovery::Applied { .. });
    match emit_prepared_c(&reduced, options, prepared) {
        Ok(output) => Ok(output),
        Err(error) if renamed => {
            let fallback = prepare::prepare_original(
                reduced.program(),
                reduced.parameters(),
                WebRecovery::RenderingFallback(error),
            )?;
            emit_prepared_c(&reduced, options, fallback)
        }
        Err(error) => Err(error),
    }
}

fn emit_prepared_c(
    reduced: &ReducedFunction,
    options: ReadableOptions,
    prepared: PreparedFunction,
) -> Result<ReadableC, ReadableError> {
    let PreparedFunction {
        program: presented,
        widths: value_widths,
        structure: structured,
        nodes,
        shared_nodes,
        source_evidence: structure_evidence,
        source_stats: structure_stats,
        web_recovery,
    } = prepared;
    let program = &presented;
    let display_nodes = nodes.as_deref();
    let mut views = MemoryViews::recover(program, reduced.parameters(), options);
    let read = rendered_reads(program, views.as_ref());
    let address_uses = if options.recover_objects {
        address_registers(program)
    } else {
        BTreeSet::new()
    };
    let mut names = BTreeMap::new();
    let mut arguments = Vec::new();
    let mut code = String::from("#include <stdint.h>\n");
    for (index, reg) in reduced.parameters().iter().enumerate() {
        let name = if options.compact_memory && options.stack_register == Some(*reg) {
            "stack_base".into()
        } else if options.compact_memory
            && let Some(object) = views
                .as_ref()
                .and_then(|v| v.objects.iter().find(|o| o.register == *reg))
        {
            format!("{}_address", object.name)
        } else {
            format!("arg{index}")
        };
        names.insert(reg.0, name.clone());
        arguments.push(format!("uint64_t {name}"));
        writeln!(code, "/* {name}: input machine register {} */", reg.0).unwrap();
    }
    if program.uses_high_multiply() {
        code.push_str(MULTIPLY_HELPER);
    }
    if program.uses_memory() {
        code.push_str(MEMORY_HELPERS);
        if views.is_some() || options.compact_memory {
            code.push_str(VIEW_HELPERS);
        }
        if options.compact_memory {
            code.push_str(syntax::COMPACT_MEMORY);
        }
        arguments.extend(["uint8_t *memory", "uint64_t base", "uint64_t size"].map(String::from));
    }
    let LocalPlan {
        names,
        widths,
        slots: printer_slots,
        initial_slots,
        locals,
        value_count: local_value_count,
        stats: local_plan,
        stack_roles,
        stack_cells,
    } = LocalPlan::build(
        program,
        reduced.parameters(),
        &read,
        names,
        &value_widths,
        display_nodes.unwrap_or(&[]),
        options,
    );
    if options.compact_memory
        && let (Some(views), Some(roles)) = (&mut views, &stack_roles)
    {
        views.name_stack_roles(roles);
    }
    let arguments = if arguments.is_empty() {
        "void".into()
    } else {
        arguments.join(", ")
    };
    writeln!(code, "\nuint64_t nirvana_readable({arguments}) {{").unwrap();
    for reg in reduced.parameters() {
        if !read.contains(&reg.0) {
            line(&mut code, 1, &format!("(void){};", names[&reg.0]));
        }
    }
    if program.uses_memory() {
        line(
            &mut code,
            1,
            "struct nirvana_memory m = {memory, base, size};",
        );
    }
    if let Some(views) = &views {
        let printer = Printer {
            names: names.clone(),
            read: read.clone(),
            views: None,
            first_temporary: program.register_count(),
            widths: widths.clone(),
            address_uses: address_uses.clone(),
            compact_memory: options.compact_memory,
            slots: printer_slots.clone(),
            initial_slots: initial_slots.clone(),
            declarations: Rc::new(DeclarationPlan::default()),
        };
        for view in views.stack_views() {
            let base = Expr::Register(options.stack_register.expect("stack view base"));
            let base = if view.offset < 0 {
                Expr::binary(BinaryOp::Sub, base, Expr::Const(view.offset.unsigned_abs()))
            } else if view.offset > 0 {
                Expr::binary(BinaryOp::Add, base, Expr::Const(view.offset as u64))
            } else {
                base
            };
            let path = ViewPath::Object {
                name: view.name.clone(),
                base,
            };
            line(
                &mut code,
                1,
                &format!(
                    "const struct nirvana_view {} = {{{}}}; /* entry stack {:+}, up to {} bytes{} */",
                    view.name,
                    printer.expression(&path.address()).text,
                    view.offset,
                    view.byte_size,
                    if view.overlaps.is_empty() {
                        ""
                    } else {
                        ", overlapping views"
                    }
                ),
            );
        }
    }
    if let Some(views) = &views {
        let printer = Printer {
            names: names.clone(),
            read: read.clone(),
            views: None,
            first_temporary: program.register_count(),
            widths: widths.clone(),
            address_uses: address_uses.clone(),
            compact_memory: options.compact_memory,
            slots: printer_slots.clone(),
            initial_slots: initial_slots.clone(),
            declarations: Rc::new(DeclarationPlan::default()),
        };
        for object in &views.objects {
            line(
                &mut code,
                1,
                &format!(
                    "/* input register {}: address views, potentially aliased */",
                    object.register.0
                ),
            );
            line(&mut code, 1, "const struct {");
            if !object.indexed.is_empty() {
                line(&mut code, 2, "struct nirvana_view base;");
            }
            for field in &object.fields {
                line(
                    &mut code,
                    2,
                    &format!("struct nirvana_view {};", field.name),
                );
            }
            line(&mut code, 1, &format!("}} {} = {{", object.name));
            if !object.indexed.is_empty() {
                line(
                    &mut code,
                    2,
                    &format!(
                        "{{{}}},",
                        printer.expression(&Expr::Register(object.register)).text
                    ),
                );
            }
            for field in &object.fields {
                let base = ViewPath::Object {
                    name: object.name.clone(),
                    base: Expr::Register(object.register),
                };
                let address = if field.offset < 0 {
                    Expr::binary(
                        BinaryOp::Sub,
                        base.address(),
                        Expr::Const(field.offset.unsigned_abs()),
                    )
                } else {
                    crate::simplify::simplify(
                        &ViewPath::Field {
                            base: Box::new(base),
                            offset: field.offset as u64,
                        }
                        .address(),
                    )
                };
                line(
                    &mut code,
                    2,
                    &format!("{{{}}},", printer.expression(&address).text),
                );
            }
            line(&mut code, 1, "};");
        }
    }
    let eligible = locals.iter().map(|local| local.name.clone()).collect();
    let declarations = Rc::new(DeclarationPlan::build(
        display_nodes,
        shared_nodes.as_deref(),
        &names,
        &read,
        &eligible,
    ));
    for local in &locals {
        if declarations.inline(&local.name) {
            continue;
        }
        line(
            &mut code,
            1,
            &format!("uint{}_t {};", local.width.bits(), local.name),
        );
    }
    let stack_views = views
        .as_ref()
        .map(|v| v.stack_views().to_vec())
        .unwrap_or_default();
    let object_views = views
        .as_ref()
        .map(|v| v.objects.clone())
        .unwrap_or_default();
    let printer = Printer {
        names,
        read,
        views,
        first_temporary: program.register_count(),
        widths,
        address_uses,
        compact_memory: options.compact_memory,
        slots: printer_slots,
        initial_slots,
        declarations,
    };
    let mut finite_regions = Vec::new();
    let mut affine_regions = Vec::new();
    let (fallback_reason, display_structure_evidence) = match structured {
        Ok(function) => {
            let nonlocal = nonlocal(function.body());
            if nonlocal {
                line(&mut code, 1, "uint64_t nirvana_transfer = 0;");
                line(&mut code, 1, "int nirvana_continue = 0;");
            }
            let nodes = display_nodes.expect("recovered nodes");
            let mut selected = nodes;
            let mut body = String::new();
            printer.nodes(&mut body, nodes, 1, 0, nonlocal)?;
            if let Some(shared) = &shared_nodes
                && shared != nodes
            {
                let mut candidate = String::new();
                // Compare the same C body using the same names, storage,
                // widths, views and checks. Sharing a lone break/return can
                // otherwise replace flat exits by deep else chains.
                if printer
                    .nodes(&mut candidate, shared, 1, 0, nonlocal)
                    .is_ok()
                    && candidate.len() < body.len()
                    && max_indent(&candidate) <= max_indent(&body)
                {
                    body = candidate;
                    selected = shared;
                }
            }
            if !nonlocal && let Some(recovered) = loops::recover(&printer, selected, &locals) {
                let mut candidate = String::new();
                if printer
                    .nodes(&mut candidate, &recovered.nodes, 1, 0, false)
                    .is_ok()
                    && candidate.len() < body.len()
                    && max_indent(&candidate) <= max_indent(&body)
                {
                    body = candidate;
                    match recovered.evidence {
                        loops::RegionEvidence::Finite(evidence) => finite_regions.push(evidence),
                        loops::RegionEvidence::Affine(evidence) => affine_regions.push(evidence),
                    }
                }
            }
            code.push_str(&body);
            (None, Some(function.evidence()))
        }
        Err(reason) => {
            printer.gotos(&mut code, program)?;
            (Some(reason), None)
        }
    };
    code.push_str("}\n");
    if program.uses_memory() && options.compact_memory {
        code.push_str(syntax::COMPACT_END);
    }
    // Emit only helpers referenced by the final selected layout. Discarded
    // candidates and metadata rendering must not add unused definitions.
    let bit_helpers = idioms::definitions(&code);
    if !bit_helpers.is_empty() {
        let start = code
            .find("uint64_t nirvana_readable(")
            .expect("function declaration");
        code.insert_str(start, &bit_helpers);
    }
    Ok(ReadableC {
        code,
        parameters: reduced.parameters().to_vec(),
        uses_memory: program.uses_memory(),
        reduction_stats: reduced.stats(),
        fallback_reason,
        structure_stats,
        structure_evidence,
        display_structure_evidence,
        web_recovery,
        stack_views,
        object_views,
        locals,
        local_value_count,
        local_plan,
        stack_roles,
        stack_cells,
        finite_regions,
        affine_regions,
    })
}
