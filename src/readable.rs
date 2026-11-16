//! Reduced C with value parameters and locals, observing return and guest memory.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use crate::block_verify::Validation;
use crate::emit::{MEMORY_HELPERS, MULTIPLY_HELPER};
use crate::ir::{Assignment, BinaryOp, Control, Expr, Place, Program, Reg};
use crate::reduce::{ReducedFunction, ReductionError, ReductionStats, reduce, reduce_checked};
use crate::structure::{Node, StructureError, StructureStats, StructuredFunction};
use crate::verify::Solver;

#[derive(Clone, Debug)]
pub struct ReadableC {
    pub code: String,
    /// Input machine-register indices corresponding to arg0, arg1, ... .
    pub parameters: Vec<Reg>,
    pub uses_memory: bool,
    pub reduction_stats: ReductionStats,
    pub fallback_reason: Option<StructureError>,
    pub structure_stats: Option<StructureStats>,
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
}

impl Printer {
    fn expression(&self, expr: &Expr) -> Render {
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
                format!(
                    "nirvana_load(&m, {}, {})",
                    self.expression(address).text,
                    width.bytes()
                ),
                true,
            ),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let condition = self.expression(condition);
                let taken = self.expression(taken);
                let not_taken = self.expression(not_taken);
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
                let l = self.expression(left);
                let r = self.expression(right);
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

    fn assignments(&self, code: &mut String, indent: usize, assignments: &[Assignment]) {
        for assignment in assignments {
            let value = self.expression(&assignment.value).text;
            let statement = match &assignment.destination {
                Place::Register(reg) if self.read.contains(&reg.0) => {
                    format!("{} = {value};", self.names[&reg.0])
                }
                Place::Register(_) => format!("(void)({value});"),
                Place::Memory { address, width } => format!(
                    "nirvana_store(&m, {}, {}, {value});",
                    self.expression(address).text,
                    width.bytes()
                ),
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
                Node::Step { assignments, .. } => self.assignments(code, indent, assignments),
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
                self.assignments(code, 1, &instruction.assignments);
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

fn read_registers(expression: &Expr, read: &mut BTreeSet<usize>) {
    match expression {
        Expr::Const(_) => {}
        Expr::Register(reg) => {
            read.insert(reg.0);
        }
        Expr::Load { address, .. } => read_registers(address, read),
        Expr::Binary(_, left, right) => {
            read_registers(left, read);
            read_registers(right, read);
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            read_registers(condition, read);
            read_registers(taken, read);
            read_registers(not_taken, read);
        }
    }
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
    Ok(emit_reduced_c(reduce(program)?))
}

/// Validate only the IR reduction. Structuring and C emission have their own
/// testing boundary and are not certified by this block model.
pub fn emit_readable_c_with_checked_reduction(
    program: &Program,
    solver: &Solver,
) -> Result<(ReadableC, Validation), ReductionError> {
    let checked = reduce_checked(program, solver)?;
    Ok((emit_reduced_c(checked.function), checked.validation))
}

fn emit_reduced_c(reduced: ReducedFunction) -> ReadableC {
    let program = reduced.program();
    let mut read = BTreeSet::new();
    for id in program.cfg().reachable_blocks() {
        let block = program.cfg().block(id);
        for instruction in &program.instructions()[block.instructions.clone()] {
            for assignment in &instruction.assignments {
                read_registers(&assignment.value, &mut read);
                if let Place::Memory { address, .. } = &assignment.destination {
                    read_registers(address, &mut read);
                }
            }
            match &instruction.control {
                Control::Branch { condition, .. } => read_registers(condition, &mut read),
                Control::Return(value) => read_registers(value, &mut read),
                _ => {}
            }
        }
    }
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
    for local in locals {
        line(&mut code, 1, &format!("uint64_t {local};"));
    }
    let printer = Printer { names, read };
    let (fallback_reason, structure_stats) = match StructuredFunction::recover(program) {
        Ok(function) => {
            let nonlocal = nonlocal(function.body());
            if nonlocal {
                line(&mut code, 1, "uint64_t nirvana_transfer = 0;");
                line(&mut code, 1, "int nirvana_continue = 0;");
            }
            printer.nodes(&mut code, &compact(function.body()), 1, 0, nonlocal);
            (None, Some(function.stats()))
        }
        Err(reason) => {
            printer.gotos(&mut code, program);
            (Some(reason), None)
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
    }
}
