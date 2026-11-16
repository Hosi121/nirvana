//! Reduced C with value parameters and locals, observing return and guest memory.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use crate::block_verify::Validation;
use crate::emit::{MEMORY_HELPERS, MULTIPLY_HELPER};
use crate::hir::ViewPath;
use crate::ir::{Assignment, BinaryOp, Control, Expr, Place, Program, Reg};
use crate::reduce::{ReducedFunction, ReductionError, ReductionStats, reduce, reduce_checked};
use crate::structure::{Node, StructureError, StructureStats, StructuredFunction};
use crate::structure_verify::StructureEvidence;
use crate::verify::Solver;

mod views;
pub use views::StackView;
use views::{StackViews, VIEW_HELPERS, rendered_reads};

#[derive(Clone, Debug)]
pub struct ReadableC {
    pub code: String,
    /// Input machine-register indices corresponding to arg0, arg1, ... .
    pub parameters: Vec<Reg>,
    pub uses_memory: bool,
    pub reduction_stats: ReductionStats,
    pub fallback_reason: Option<StructureError>,
    pub structure_stats: Option<StructureStats>,
    /// Correspondence for the Node AST, before compact/loop/C rendering.
    pub structure_evidence: Option<StructureEvidence>,
    /// Named guest-memory locations, not recovered source variables or types.
    pub stack_views: Vec<StackView>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct ReadableOptions {
    /// The input register holding the entry stack address. No architecture is
    /// assumed by default; the x86 frontend supplies RSP explicitly.
    pub stack_register: Option<Reg>,
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
    views: Option<StackViews>,
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
            Expr::Const(value) => atom(format!("UINT64_C({value})"), true),
            Expr::Register(reg) => atom(self.names[&reg.0].clone(), true),
            Expr::Load { address, width } => atom(
                if let Some(view) = self.views.as_ref().and_then(|v| v.at(point, address)) {
                    format!("nirvana_view_load(&m, {}, {})", view.name, width.bytes())
                } else {
                    format!(
                        "nirvana_load(&m, {}, {})",
                        self.expression_at(address, point).text,
                        width.bytes()
                    )
                },
                true,
            ),
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
                let operand_precedence = if bitwise || shift { 12 } else { precedence };
                let left_text = if promote {
                    l.u64()
                } else {
                    l.child(operand_precedence)
                };
                let right_text = if shift && !bounded_shift(right) {
                    format!("({} & 63)", r.child(12))
                } else {
                    r.child(if bitwise { 12 } else { precedence + 1 })
                };
                Render {
                    text: format!("{left_text} {symbol} {right_text}"),
                    precedence,
                    unsigned: !comparison,
                }
            }
        }
    }

    fn assignments(
        &self,
        code: &mut String,
        indent: usize,
        address: u64,
        assignments: &[Assignment],
    ) {
        for (index, assignment) in assignments.iter().enumerate() {
            if let Place::Register(reg) = assignment.destination
                && !self.read.contains(&reg.0)
                && !assignment.value.uses_memory()
            {
                continue;
            }
            let point = Some((address, index));
            let value = self.expression_at(&assignment.value, point).text;
            if let Place::Memory { address, width } = &assignment.destination
                && assignment.value.uses_memory()
            {
                // C evaluates argument expressions before entering a function.
                // The IR checks the destination before a possibly faulting RHS.
                // Capture a raw address once, then check it in a full statement.
                let view = self.views.as_ref().and_then(|v| v.at(point, address));
                line(code, indent, "{");
                let destination = if let Some(view) = view {
                    format!("{}.address", view.name)
                } else {
                    line(
                        code,
                        indent + 1,
                        &format!(
                            "const uint64_t nirvana_address = {};",
                            self.expression_at(address, point).text
                        ),
                    );
                    "nirvana_address".into()
                };
                line(
                    code,
                    indent + 1,
                    &format!(
                        "(void)nirvana_offset(&m, {destination}, {});",
                        width.bytes()
                    ),
                );
                let store = if let Some(view) = view {
                    format!(
                        "nirvana_view_store(&m, {}, {}, {value});",
                        view.name,
                        width.bytes()
                    )
                } else {
                    format!(
                        "nirvana_store(&m, {destination}, {}, {value});",
                        width.bytes()
                    )
                };
                line(code, indent + 1, &store);
                line(code, indent, "}");
                continue;
            }
            let statement = match &assignment.destination {
                Place::Register(reg) if self.read.contains(&reg.0) => {
                    format!("{} = {value};", self.names[&reg.0])
                }
                Place::Register(_) => format!("(void)({value});"),
                Place::Memory { address, width } => {
                    if let Some(view) = self.views.as_ref().and_then(|v| v.at(point, address)) {
                        format!(
                            "nirvana_view_store(&m, {}, {}, {value});",
                            view.name,
                            width.bytes()
                        )
                    } else {
                        format!(
                            "nirvana_store(&m, {}, {}, {value});",
                            self.expression_at(address, point).text,
                            width.bytes()
                        )
                    }
                }
            };
            line(code, indent, &statement);
        }
    }

    fn nodes(
        &self,
        code: &mut String,
        nodes: &[Node],
        indent: usize,
        depth: usize,
        nonlocal: bool,
    ) {
        for node in nodes {
            match node {
                Node::Evaluate(value) => {
                    line(
                        code,
                        indent,
                        &format!("(void)({});", self.expression(value).text),
                    );
                }
                Node::Step {
                    address,
                    assignments,
                } => self.assignments(code, indent, *address, assignments),
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    line(
                        code,
                        indent,
                        &format!("if ({}) {{", self.expression(condition).text),
                    );
                    self.nodes(code, taken, indent + 1, depth, nonlocal);
                    if !not_taken.is_empty() {
                        line(code, indent, "} else {");
                        self.nodes(code, not_taken, indent + 1, depth, nonlocal);
                    }
                    line(code, indent, "}");
                }
                Node::Loop(body) => {
                    let (header, middle, footer) = match body.as_slice() {
                        [
                            Node::If {
                                condition,
                                taken,
                                not_taken,
                            },
                            rest @ ..,
                        ] if is_break(taken) && not_taken.is_empty() => {
                            let condition = invert(condition);
                            (
                                format!("while ({}) {{", self.expression(&condition).text),
                                rest,
                                "}".into(),
                            )
                        }
                        [
                            prefix @ ..,
                            Node::If {
                                condition,
                                taken,
                                not_taken,
                            },
                        ] if is_continue(taken)
                            && is_break(not_taken)
                            && !contains_continue(prefix) =>
                        {
                            (
                                "do {".into(),
                                prefix,
                                format!("}} while ({});", self.expression(condition).text),
                            )
                        }
                        _ => ("for (;;) {".into(), body.as_slice(), "}".into()),
                    };
                    line(code, indent, &header);
                    self.nodes(code, middle, indent + 1, depth + 1, nonlocal);
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
                Node::Return(value) => line(
                    code,
                    indent,
                    &format!("return {};", self.expression(value).text),
                ),
            }
        }
    }

    fn gotos(&self, code: &mut String, program: &Program) {
        let cfg = program.cfg();
        let block_at = |address| cfg.block_at(address).expect("validated destination");
        line(code, 1, &format!("goto {};", cfg.entry()));
        for id in cfg.reachable_blocks() {
            let block = cfg.block(id);
            writeln!(code, "{id}:").unwrap();
            for instruction in &program.instructions()[block.instructions.clone()] {
                self.assignments(code, 1, instruction.address, &instruction.assignments);
            }
            let instruction = &program.instructions()[block.instructions.end - 1];
            match &instruction.control {
                Control::Next => line(
                    code,
                    1,
                    &format!(
                        "goto {};",
                        block_at(instruction.address + u64::from(instruction.size))
                    ),
                ),
                Control::Jump(target) => line(code, 1, &format!("goto {};", block_at(*target))),
                Control::Branch { condition, target } => {
                    line(
                        code,
                        1,
                        &format!(
                            "if ({}) goto {};",
                            self.expression(condition).text,
                            block_at(*target)
                        ),
                    );
                    line(
                        code,
                        1,
                        &format!(
                            "goto {};",
                            block_at(instruction.address + u64::from(instruction.size))
                        ),
                    );
                }
                Control::Return(value) => {
                    line(code, 1, &format!("return {};", self.expression(value).text))
                }
            }
        }
    }
}

fn bounded_shift(expression: &Expr) -> bool {
    match expression {
        Expr::Const(value) => *value <= 63,
        Expr::Binary(BinaryOp::And, left, right) => bounded_shift(left) || bounded_shift(right),
        _ => false,
    }
}

fn line(code: &mut String, indent: usize, text: &str) {
    writeln!(code, "{}{text}", "    ".repeat(indent)).unwrap();
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
    crate::simplify::simplify(&Expr::binary(
        BinaryOp::Eq,
        condition.clone(),
        Expr::Const(0),
    ))
}

// Empty machine steps still exist in the executable reduced IR. They need no C
// statement; removing them here also exposes conventional loop guards.
fn compact(nodes: &[Node]) -> Vec<Node> {
    nodes
        .iter()
        .filter_map(|node| match node {
            Node::Step { assignments, .. } if assignments.is_empty() => None,
            Node::Loop(body) => Some(Node::Loop(compact(body))),
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                let taken = compact(taken);
                let not_taken = compact(not_taken);
                if taken.is_empty() && not_taken.is_empty() {
                    Some(Node::Evaluate(condition.clone()))
                } else if taken.is_empty() {
                    Some(Node::If {
                        condition: invert(condition),
                        taken: not_taken,
                        not_taken: taken,
                    })
                } else {
                    Some(Node::If {
                        condition: condition.clone(),
                        taken,
                        not_taken,
                    })
                }
            }
            _ => Some(node.clone()),
        })
        .collect()
}

pub fn emit_readable_c(program: &Program) -> Result<ReadableC, ReductionError> {
    emit_readable_c_with_options(program, ReadableOptions::default())
}

pub fn emit_readable_c_with_options(
    program: &Program,
    options: ReadableOptions,
) -> Result<ReadableC, ReductionError> {
    Ok(emit_reduced_c(reduce(program)?, options))
}

/// Validate only the IR reduction. Structuring and C emission have their own
/// testing boundary and are not certified by this block model.
pub fn emit_readable_c_with_checked_reduction(
    program: &Program,
    solver: &Solver,
) -> Result<(ReadableC, Validation), ReductionError> {
    emit_readable_c_with_checked_reduction_and_options(program, solver, ReadableOptions::default())
}

pub fn emit_readable_c_with_checked_reduction_and_options(
    program: &Program,
    solver: &Solver,
    options: ReadableOptions,
) -> Result<(ReadableC, Validation), ReductionError> {
    let checked = reduce_checked(program, solver)?;
    Ok((
        emit_reduced_c(checked.function, options),
        checked.validation,
    ))
}

fn emit_reduced_c(reduced: ReducedFunction, options: ReadableOptions) -> ReadableC {
    let program = reduced.program();
    let views = options
        .stack_register
        .filter(|r| reduced.parameters().contains(r))
        .and_then(|r| StackViews::recover(program, r));
    let read = rendered_reads(program, &views);
    let mut names = BTreeMap::new();
    let mut arguments = Vec::new();
    let mut code = String::from("#include <stdint.h>\n");
    for (index, reg) in reduced.parameters().iter().enumerate() {
        let name = format!("arg{index}");
        names.insert(reg.0, name.clone());
        arguments.push(format!("uint64_t {name}"));
        writeln!(code, "/* {name}: input machine register {} */", reg.0).unwrap();
    }
    if program.uses_high_multiply() {
        code.push_str(MULTIPLY_HELPER);
    }
    if program.uses_memory() {
        code.push_str(MEMORY_HELPERS);
        if views.is_some() {
            code.push_str(VIEW_HELPERS);
        }
        arguments.extend(["uint8_t *memory", "uint64_t base", "uint64_t size"].map(String::from));
    }
    let mut locals = Vec::new();
    for reg in &read {
        if !names.contains_key(reg) {
            let name = format!("v{}", locals.len());
            names.insert(*reg, name.clone());
            locals.push(name);
        }
    }
    let arguments = if arguments.is_empty() {
        "void".into()
    } else {
        arguments.join(", ")
    };
    writeln!(code, "\nuint64_t nirvana_readable({arguments}) {{").unwrap();
    for (index, reg) in reduced.parameters().iter().enumerate() {
        if !read.contains(&reg.0) {
            line(&mut code, 1, &format!("(void)arg{index};"));
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
        };
        for view in &views.views {
            let base = Expr::Register(views.register);
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
    for local in locals {
        line(&mut code, 1, &format!("uint64_t {local};"));
    }
    let stack_views = views.as_ref().map(|v| v.views.clone()).unwrap_or_default();
    let printer = Printer { names, read, views };
    let (fallback_reason, structure_stats, structure_evidence) =
        match StructuredFunction::recover(program) {
            Ok(function) => {
                let nonlocal = nonlocal(function.body());
                if nonlocal {
                    line(&mut code, 1, "uint64_t nirvana_transfer = 0;");
                    line(&mut code, 1, "int nirvana_continue = 0;");
                }
                printer.nodes(&mut code, &compact(function.body()), 1, 0, nonlocal);
                (None, Some(function.stats()), Some(function.evidence()))
            }
            Err(reason) => {
                printer.gotos(&mut code, program);
                (Some(reason), None, None)
            }
        };
    code.push_str("}\n");
    ReadableC {
        code,
        parameters: reduced.parameters().to_vec(),
        uses_memory: program.uses_memory(),
        reduction_stats: reduced.stats(),
        fallback_reason,
        structure_stats,
        structure_evidence,
        stack_views,
    }
}
