//! C11 emission. Unsupported structured shapes retain explicit goto control flow.

use std::fmt::Write;

use crate::cfg::{BlockId, Target};
use crate::ir::{Assignment, BinaryOp, Control, Expr, Place, Program};
use crate::structure::{Node, StructureError, StructureStats, StructuredFunction};

pub(crate) const MULTIPLY_HELPER: &str = r#"
static inline uint64_t nirvana_umul_high(uint64_t a, uint64_t b) {
    uint64_t a0 = a & UINT64_C(0xffffffff), a1 = a >> 32;
    uint64_t b0 = b & UINT64_C(0xffffffff), b1 = b >> 32;
    uint64_t low = a0 * b0;
    uint64_t t = a1 * b0 + (low >> 32);
    uint64_t middle = (t & UINT64_C(0xffffffff)) + a0 * b1;
    return a1 * b1 + (t >> 32) + (middle >> 32);
}
"#;

pub(crate) const MEMORY_HELPERS: &str = r#"
#include <stdlib.h>
struct nirvana_memory { uint8_t *bytes; uint64_t base, size; };
static inline uint64_t nirvana_offset(struct nirvana_memory *m, uint64_t address, uint64_t width) {
    if (width == 0 || address > UINT64_MAX - (width - 1) || address < m->base || width > m->size || address - m->base > m->size - width) abort();
    return address - m->base;
}
static inline uint64_t nirvana_load(struct nirvana_memory *m, uint64_t address, unsigned width) {
    uint64_t offset = nirvana_offset(m, address, width), value = 0;
    for (unsigned i = 0; i < width; ++i) value |= (uint64_t)m->bytes[offset + i] << (i * 8);
    return value;
}
static inline void nirvana_store(struct nirvana_memory *m, uint64_t address, unsigned width, uint64_t value) {
    uint64_t offset = nirvana_offset(m, address, width);
    for (unsigned i = 0; i < width; ++i) m->bytes[offset + i] = (uint8_t)(value >> (i * 8));
}
"#;

#[derive(Clone, Debug)]
pub struct COutput {
    pub code: String,
    /// None means that structured recovery succeeded.
    pub fallback_reason: Option<StructureError>,
    pub structure_stats: Option<StructureStats>,
}

pub fn emit_c(program: &Program) -> COutput {
    let mut code = String::from("#include <stdint.h>\n");
    if program.uses_high_multiply() {
        code.push_str(MULTIPLY_HELPER);
    }
    if program.uses_memory() {
        code.push_str(MEMORY_HELPERS);
        code.push_str("\nuint64_t nirvana_fn(uint64_t *r, uint8_t *memory, uint64_t base, uint64_t size) {\n    struct nirvana_memory m = {memory, base, size};\n    (void)m;\n    (void)r;\n");
    } else {
        code.push_str("\nuint64_t nirvana_fn(uint64_t *r) {\n    (void)r;\n");
    }
    let (fallback_reason, structure_stats) = match StructuredFunction::recover(program) {
        Ok(function) => {
            let nonlocal = has_nonlocal_transfer(function.body());
            if nonlocal {
                line(&mut code, 1, "uint64_t nirvana_transfer = 0;");
                line(&mut code, 1, "int nirvana_continue = 0;");
            }
            emit_nodes(function.body(), 1, 0, nonlocal, &mut code);
            (None, Some(function.stats()))
        }
        Err(reason) => {
            emit_gotos(program, &mut code);
            (Some(reason), None)
        }
    };
    code.push_str("}\n");
    COutput {
        code,
        fallback_reason,
        structure_stats,
    }
}

fn expression(expr: &Expr) -> String {
    match expr {
        Expr::Const(value) => format!("UINT64_C({value})"),
        Expr::Register(reg) => format!("r[{}]", reg.0),
        Expr::Load { address, width } => format!(
            "nirvana_load(&m, {}, {})",
            expression(address),
            width.bytes()
        ),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => format!(
            "({} ? {} : {})",
            expression(condition),
            expression(taken),
            expression(not_taken)
        ),
        Expr::Binary(op, left, right) => {
            let left = expression(left);
            let mut right = expression(right);
            if *op == BinaryOp::UMulHigh {
                return format!("nirvana_umul_high({left}, {right})");
            }
            let operator = match op {
                BinaryOp::Add => "+",
                BinaryOp::Sub => "-",
                BinaryOp::Mul => "*",
                BinaryOp::And => "&",
                BinaryOp::Or => "|",
                BinaryOp::Xor => "^",
                BinaryOp::Shl => "<<",
                BinaryOp::Shr => ">>",
                BinaryOp::Eq => "==",
                BinaryOp::Ne => "!=",
                BinaryOp::Ult => "<",
                BinaryOp::Ule => "<=",
                BinaryOp::UMulHigh => unreachable!(),
            };
            if matches!(op, BinaryOp::Shl | BinaryOp::Shr) {
                right = format!("({right} & UINT64_C(63))");
            }
            // Comparisons must also have uint64_t type when nested inside
            // arithmetic, to avoid accidental signed-int operations in C.
            format!("((uint64_t)({left} {operator} {right}))")
        }
    }
}

fn line(code: &mut String, indent: usize, text: &str) {
    writeln!(code, "{}{text}", "    ".repeat(indent)).unwrap();
}

fn assignments(code: &mut String, indent: usize, statements: &[Assignment]) {
    for assignment in statements {
        let value = expression(&assignment.value);
        let statement = match &assignment.destination {
            Place::Register(reg) => format!("r[{}] = {value};", reg.0),
            Place::Memory { address, width } => format!(
                "nirvana_store(&m, {}, {}, {value});",
                expression(address),
                width.bytes()
            ),
        };
        line(code, indent, &statement);
    }
}

fn has_nonlocal_transfer(nodes: &[Node]) -> bool {
    nodes.iter().any(|node| match node {
        Node::BreakOuter { .. } | Node::ContinueOuter { .. } => true,
        Node::Loop(body) => has_nonlocal_transfer(body),
        Node::If {
            taken, not_taken, ..
        } => has_nonlocal_transfer(taken) || has_nonlocal_transfer(not_taken),
        _ => false,
    })
}

fn emit_nodes(nodes: &[Node], indent: usize, loop_depth: usize, nonlocal: bool, code: &mut String) {
    for node in nodes {
        match node {
            Node::Evaluate(value) => line(code, indent, &format!("(void)({});", expression(value))),
            Node::Step {
                address,
                assignments: statements,
            } => {
                line(code, indent, &format!("/* {address:#x} */"));
                assignments(code, indent, statements);
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                if taken.is_empty() && not_taken.is_empty() {
                    line(code, indent, &format!("(void)({});", expression(condition)));
                    continue;
                }
                let condition = expression(condition);
                let (condition, first, second) = if taken.is_empty() {
                    (format!("!({condition})"), not_taken, taken)
                } else {
                    (condition, taken, not_taken)
                };
                line(code, indent, &format!("if ({condition}) {{"));
                emit_nodes(first, indent + 1, loop_depth, nonlocal, code);
                if !second.is_empty() {
                    line(code, indent, "} else {");
                    emit_nodes(second, indent + 1, loop_depth, nonlocal, code);
                }
                line(code, indent, "}");
            }
            Node::Loop(body) => {
                line(code, indent, "while (1) {");
                emit_nodes(body, indent + 1, loop_depth + 1, nonlocal, code);
                line(code, indent, "}");
                if nonlocal && loop_depth > 0 {
                    // This handler runs before any following original step.
                    // Unwind an enclosing loop, or resume its next iteration
                    // once the requested continue target has been reached.
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
                line(
                    code,
                    indent,
                    &format!("nirvana_transfer = UINT64_C({levels});"),
                );
                line(
                    code,
                    indent,
                    if matches!(node, Node::ContinueOuter { .. }) {
                        "nirvana_continue = 1;"
                    } else {
                        "nirvana_continue = 0;"
                    },
                );
                line(code, indent, "break;");
            }
            Node::Return(value) => line(code, indent, &format!("return {};", expression(value))),
        }
    }
}

fn emit_gotos(program: &Program, code: &mut String) {
    let cfg = program.cfg();
    let block_at = |address| cfg.block_at(address).expect("validated destination");
    line(code, 1, &format!("goto {};", cfg.entry()));
    for id in cfg.reachable_blocks() {
        let block = cfg.block(id);
        writeln!(code, "{id}:").unwrap();
        for instruction in &program.instructions()[block.instructions.clone()] {
            line(code, 1, &format!("/* {:#x} */", instruction.address));
            assignments(code, 1, &instruction.assignments);
        }
        let instruction = &program.instructions()[block.instructions.end - 1];
        match &instruction.control {
            Control::Next => emit_jump(
                code,
                block_at(instruction.address + u64::from(instruction.size)),
            ),
            Control::Jump(target) => emit_jump(code, block_at(*target)),
            Control::Branch { condition, target } => {
                line(
                    code,
                    1,
                    &format!("if ({}) goto {};", expression(condition), block_at(*target)),
                );
                emit_jump(
                    code,
                    block_at(instruction.address + u64::from(instruction.size)),
                );
            }
            Control::Return(value) => line(code, 1, &format!("return {};", expression(value))),
        }
        debug_assert!(
            block
                .successors
                .iter()
                .all(|edge| matches!(edge.target, Target::Block(_)))
        );
    }
}

fn emit_jump(code: &mut String, target: BlockId) {
    line(code, 1, &format!("goto {target};"));
}
