//! Reduced C with value parameters and locals, observing return and guest memory.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use crate::allocation::allocate_locals;
use crate::block_verify::Validation;
use crate::emit::{MEMORY_HELPERS, MULTIPLY_HELPER};
use crate::goto_layout::GotoLayout;
use crate::hir::ViewPath;
use crate::ir::{Assignment, BinaryOp, Control, Expr, Place, Program, Reg, Width};
use crate::reduce::{ReducedFunction, ReductionError, ReductionStats, reduce, reduce_checked};
use crate::sequence::{Evaluation, SequenceError, sequence};
use crate::structure::{Node, StructureError, StructureStats, StructuredFunction};
use crate::structure_verify::StructureEvidence;
use crate::value_role::ValueRole;
use crate::value_width::ValueWidths;
use crate::verify::Solver;

mod syntax;
mod views;
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
    /// Correspondence for the Node AST, before tail sharing/compact/loop/C rendering.
    pub structure_evidence: Option<StructureEvidence>,
    /// Named guest-memory locations, not recovered source variables or types.
    pub stack_views: Vec<StackView>,
    pub object_views: Vec<ObjectView>,
    /// Storage widths of named local values; parameters remain uint64_t.
    pub locals: Vec<LocalValue>,
    /// Number of individual IR local registers before assigning C storage.
    pub local_value_count: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LocalValue {
    /// First member, retained for callers that inspect a representative value.
    pub register: Reg,
    pub registers: Vec<Reg>,
    pub name: String,
    pub width: Width,
    /// A conservative generated storage role, not an original source name.
    pub role: Option<ValueRole>,
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
                let operand_precedence = if bitwise || shift {
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
                        12
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
                        if let Some(value) = self.address_value(*reg, point, &assignment.value) {
                            line(code, indent, &format!("{} = {value};", self.register(*reg)));
                        } else {
                            let width = self.widths.get(&reg.0).copied().unwrap_or(Width::U64);
                            let value = stored_value(&assignment.value, width);
                            if self.compact_memory
                                && let Some(statement) = self.compound(*reg, value, point)
                            {
                                line(code, indent, &statement);
                                continue;
                            }
                            self.value_statement(
                                code,
                                indent,
                                value,
                                point,
                                &format!("{} = ", self.register(*reg)),
                                ";",
                            )?;
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
        let (op, right) = crate::self_update::extract(value, destination, same).or_else(|| {
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
                    let (header, middle, footer) =
                        if let Some((header, middle)) = self.loop_header(body) {
                            (header, middle, String::from("}"))
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

fn is_break(nodes: &[Node]) -> bool {
    matches!(nodes, [Node::Break])
}
fn is_continue(nodes: &[Node]) -> bool {
    matches!(nodes, [Node::Continue])
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
fn invert(condition: &Expr) -> Expr {
    // Preserve operand dependencies and all load evaluation. Algebraic folds
    // belong to presentation_program, before rendered_reads is computed.
    match condition {
        Expr::Binary(BinaryOp::Eq, a, b) => {
            Expr::binary(BinaryOp::Ne, (**a).clone(), (**b).clone())
        }
        Expr::Binary(BinaryOp::Ne, a, b) => {
            Expr::binary(BinaryOp::Eq, (**a).clone(), (**b).clone())
        }
        _ => Expr::binary(BinaryOp::Eq, condition.clone(), Expr::Const(0)),
    }
}

// Empty machine steps still exist in the executable reduced IR. They need no C
// statement; removing them here also exposes conventional loop guards.
fn compact(nodes: &[Node]) -> Vec<Node> {
    let mut result = Vec::new();
    for node in nodes {
        match node {
            Node::Step { assignments, .. } if assignments.is_empty() => {}
            Node::Loop(body) => result.push(Node::Loop(compact(body))),
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                let taken = compact(taken);
                let not_taken = compact(not_taken);
                if taken.is_empty() && not_taken.is_empty() {
                    result.push(Node::Evaluate(condition.clone()));
                } else if taken.is_empty() {
                    result.push(Node::If {
                        condition: invert(condition),
                        taken: not_taken,
                        not_taken: taken,
                    });
                } else if !not_taken.is_empty()
                    && !(is_continue(&taken) && is_break(&not_taken))
                    && !(is_break(&taken) && is_continue(&not_taken))
                    && exits(&not_taken)
                    && (not_taken.len() <= taken.len() || !exits(&taken))
                {
                    result.push(Node::If {
                        condition: invert(condition),
                        taken: not_taken,
                        not_taken: vec![],
                    });
                    result.extend(taken);
                } else if !not_taken.is_empty()
                    && exits(&taken)
                    && !(is_continue(&taken) && is_break(&not_taken))
                {
                    result.push(Node::If {
                        condition: condition.clone(),
                        taken,
                        not_taken: vec![],
                    });
                    result.extend(not_taken);
                } else {
                    result.push(Node::If {
                        condition: condition.clone(),
                        taken,
                        not_taken,
                    });
                }
            }
            _ => result.push(node.clone()),
        }
    }
    result
}

fn exits(nodes: &[Node]) -> bool {
    matches!(
        nodes.last(),
        Some(
            Node::Break
                | Node::Continue
                | Node::BreakOuter { .. }
                | Node::ContinueOuter { .. }
                | Node::Return(_)
        )
    )
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

fn presentation_assignment(a: &Assignment, width: &impl Fn(Reg) -> Width) -> Assignment {
    Assignment {
        destination: match &a.destination {
            Place::Register(reg) => Place::Register(*reg),
            Place::Memory {
                address,
                width: size,
            } => Place::Memory {
                address: crate::presentation::normalize(address, width),
                width: *size,
            },
        },
        value: crate::presentation::normalize(&a.value, width),
    }
}

fn presentation_program(
    program: &Program,
    width: &impl Fn(Reg) -> Width,
) -> Result<Program, ReductionError> {
    let mut instructions = program.instructions().to_vec();
    for instruction in &mut instructions {
        instruction.assignments = instruction
            .assignments
            .iter()
            .map(|a| presentation_assignment(a, width))
            .collect();
        match &mut instruction.control {
            Control::Branch { condition, .. } | Control::Return(condition) => {
                *condition = crate::presentation::normalize(condition, width);
            }
            _ => {}
        }
    }
    Program::new(
        program.cfg().block(program.cfg().entry()).start,
        program.register_count(),
        instructions,
    )
    .map_err(ReductionError::Program)
}

fn presentation_nodes(nodes: &[Node], width: &impl Fn(Reg) -> Width) -> Vec<Node> {
    nodes
        .iter()
        .map(|node| match node {
            Node::Evaluate(value) => Node::Evaluate(crate::presentation::normalize(value, width)),
            Node::Return(value) => Node::Return(crate::presentation::normalize(value, width)),
            Node::Step {
                address,
                assignments,
            } => Node::Step {
                address: *address,
                assignments: assignments
                    .iter()
                    .map(|a| presentation_assignment(a, width))
                    .collect(),
            },
            Node::If {
                condition,
                taken,
                not_taken,
            } => Node::If {
                condition: crate::presentation::normalize(condition, width),
                taken: presentation_nodes(taken, width),
                not_taken: presentation_nodes(not_taken, width),
            },
            Node::Loop(body) => Node::Loop(presentation_nodes(body, width)),
            _ => node.clone(),
        })
        .collect()
}

fn groups_count(slots: &BTreeMap<usize, usize>) -> usize {
    slots.values().max().map_or(0, |slot| slot + 1)
}

fn emit_reduced_c(
    reduced: ReducedFunction,
    options: ReadableOptions,
) -> Result<ReadableC, ReadableError> {
    let original = reduced.program();
    let value_widths = ValueWidths::analyze(original);
    let width = |reg| {
        if reduced.parameters().contains(&reg) {
            Width::U64
        } else {
            value_widths.width(reg)
        }
    };
    // A presentation copy keeps the executable IR and its checked structure
    // certificate intact. All dependency/view/allocation analyses see the same
    // expressions that will actually be printed.
    let presented = presentation_program(original, &width)?;
    let program = &presented;
    let structured = StructuredFunction::recover(original);
    let candidates = structured.as_ref().ok().map(|function| {
        let nodes = presentation_nodes(function.body(), &width);
        // Exact program points are part of suffix equality: memory views
        // are proved at those points. Keep the original presentation tree
        // when the whole bounded pass cannot complete.
        let shared = crate::branch_tail::factor(&nodes);
        (compact(&nodes), shared.map(|nodes| compact(&nodes)))
    });
    let display_nodes = candidates.as_ref().map(|(nodes, _)| nodes.as_slice());
    let views = MemoryViews::recover(program, reduced.parameters(), options);
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
    let eligible: Vec<_> = read
        .iter()
        .filter(|r| !names.contains_key(r))
        .map(|&r| Reg(r))
        .collect();
    let local_value_count = eligible.len();
    // Keep storage classes separate so reusing a wide pointer temporary never
    // erases an inferred byte/word type merely to save another declaration.
    let mut colors: Vec<_> = (0..eligible.len()).collect();
    if options.coalesce_locals {
        let mut next_color = 0;
        for width in [Width::U64, Width::U32, Width::U16, Width::U8] {
            let members: Vec<_> = eligible
                .iter()
                .enumerate()
                .filter(|(_, r)| value_widths.width(**r) == width)
                .map(|(i, &r)| (i, r))
                .collect();
            let registers: Vec<_> = members.iter().map(|(_, r)| *r).collect();
            let allocated = allocate_locals(program, &registers).and_then(|a| {
                registers
                    .iter()
                    .map(|&r| a.color(r))
                    .collect::<Option<Vec<_>>>()
            });
            let palette = allocated.unwrap_or_else(|| (0..members.len()).collect());
            let palette_size = palette.iter().max().map_or(0, |c| c + 1);
            for ((index, _), color) in members.into_iter().zip(palette) {
                colors[index] = next_color + color;
            }
            next_color += palette_size;
        }
    }
    let mut groups: BTreeMap<usize, Vec<Reg>> = BTreeMap::new();
    for (&reg, color) in eligible.iter().zip(colors) {
        groups.entry(color).or_default().push(reg);
    }
    let slots: BTreeMap<usize, usize> = groups
        .iter()
        .flat_map(|(&color, registers)| registers.iter().map(move |reg| (reg.0, color)))
        .collect();
    let roles = crate::value_role::infer(display_nodes.unwrap_or(&[]), |reg| {
        slots.get(&reg.0).copied()
    });
    let mut role_counts = BTreeMap::new();
    for role in roles.values() {
        *role_counts.entry(role.stem()).or_insert(0usize) += 1;
    }
    let mut role_serials = BTreeMap::new();
    let mut widths = BTreeMap::new();
    let mut locals = Vec::new();
    let single_local = groups.len() == 1;
    for (color, registers) in groups {
        let width = registers
            .iter()
            .map(|&r| value_widths.width(r))
            .max_by_key(|w| w.bits())
            .unwrap_or(Width::U64);
        let role = roles.get(&color).copied();
        let name = if options.compact_memory {
            if let Some(role) = role {
                let stem = role.stem();
                if role_counts[stem] == 1 {
                    stem.into()
                } else {
                    let serial = role_serials.entry(stem).or_insert(0usize);
                    let name = format!("{stem}{serial}");
                    *serial += 1;
                    name
                }
            } else if single_local {
                "value".into()
            } else {
                format!("value{color}")
            }
        } else {
            format!("v{color}")
        };
        for reg in &registers {
            names.insert(reg.0, name.clone());
            widths.insert(reg.0, width);
        }
        locals.push(LocalValue {
            register: registers[0],
            registers,
            name,
            width,
            role,
        });
    }
    let mut printer_slots = slots.clone();
    let first_parameter = groups_count(&slots);
    let mut initial_slots = Vec::new();
    for (index, reg) in reduced.parameters().iter().enumerate() {
        if read.contains(&reg.0) {
            let slot = first_parameter + index;
            printer_slots.insert(reg.0, slot);
            initial_slots.push(slot);
        }
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
    for local in &locals {
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
    };
    let (fallback_reason, structure_stats, structure_evidence) = match structured {
        Ok(function) => {
            let nonlocal = nonlocal(function.body());
            if nonlocal {
                line(&mut code, 1, "uint64_t nirvana_transfer = 0;");
                line(&mut code, 1, "int nirvana_continue = 0;");
            }
            let nodes = display_nodes.expect("recovered nodes");
            let mut body = String::new();
            printer.nodes(&mut body, nodes, 1, 0, nonlocal)?;
            if let Some((_, Some(shared))) = &candidates
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
                }
            }
            code.push_str(&body);
            (None, Some(function.stats()), Some(function.evidence()))
        }
        Err(reason) => {
            printer.gotos(&mut code, program)?;
            (Some(reason), None, None)
        }
    };
    code.push_str("}\n");
    if program.uses_memory() && options.compact_memory {
        code.push_str(syntax::COMPACT_END);
    }
    Ok(ReadableC {
        code,
        parameters: reduced.parameters().to_vec(),
        uses_memory: program.uses_memory(),
        reduction_stats: reduced.stats(),
        fallback_reason,
        structure_stats,
        structure_evidence,
        stack_views,
        object_views,
        locals,
        local_value_count,
    })
}
