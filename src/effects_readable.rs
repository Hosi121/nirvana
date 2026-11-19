//! Structured checked C for explicit effect IR.
//!
//! Recovery uses the control skeleton only. Every original instruction keeps
//! its step and its ordered assignments or external call; no pure-IR dataflow
//! transform may run over a skeleton whose calls hide register clobbers.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use crate::effects::{CallTarget, Instruction, Program};
use crate::effects_emit::{FUNCTION_OPEN, image_initialization, runtime_header};
use crate::emit::{Expressions, MULTIPLY_HELPER, validate_program};
use crate::ir::{Control, Expr, Place};
use crate::loop_labels::LoopLabels;
use crate::sequence::SequenceError;
use crate::structure::{Node, StructureError, StructuredFunction};

#[derive(Clone, Debug)]
pub struct COutput {
    pub code: String,
    /// None means structured recovery and loop-label planning succeeded.
    pub fallback_reason: Option<StructureError>,
}

/// Preserve the checked effect API, full guest state and every stop boundary.
/// Unsupported structures use the existing instruction-label renderer.
pub fn emit_c(program: &Program) -> Result<COutput, SequenceError> {
    validate_program(program.shape())?;
    let function = match StructuredFunction::recover(program.shape()) {
        Ok(function) => function,
        Err(reason) => return fallback(program, reason),
    };
    let Some(labels) = LoopLabels::analyze(function.body()) else {
        return fallback(program, StructureError::LoopLabelsUnavailable);
    };
    let expressions = Expressions::new(program.shape());
    let mut body = String::new();
    match emit_nodes(
        program,
        function.body(),
        1,
        &labels,
        &expressions,
        &mut body,
    ) {
        Ok(()) => {}
        Err(RenderError::Sequence(error)) => return Err(error),
        Err(RenderError::Labels) => {
            return fallback(program, StructureError::LoopLabelsUnavailable);
        }
    }
    let mut code = String::from("#include <stdint.h>\n#include <setjmp.h>\n");
    if program.shape().uses_high_multiply() {
        code.push_str(MULTIPLY_HELPER);
    }
    code.push_str(runtime_header());
    writeln!(
        code,
        "\n#define NIRVANA_EFFECT_REGISTERS {}",
        program.register_count()
    )
    .unwrap();
    code.push_str(FUNCTION_OPEN);
    code.push_str(&body);
    code.push_str("}\n");
    Ok(COutput {
        code,
        fallback_reason: None,
    })
}

/// Include the relocated initial guest image and bounded diagnostic byte views.
/// The previews never replace loads: calls still read the mutable guest RAM.
pub fn emit_image(
    program: &Program,
    image: &crate::loader::LinkedImage,
) -> Result<COutput, String> {
    let mut output = emit_c(program).map_err(|error| error.to_string())?;
    let previews = initial_string_views(program, image);
    output.code.insert_str(0, &previews);
    output.code.push_str(&image_initialization(image)?);
    Ok(output)
}

fn fallback(program: &Program, reason: StructureError) -> Result<COutput, SequenceError> {
    Ok(COutput {
        code: crate::effects_emit::emit_c(program)?,
        fallback_reason: Some(reason),
    })
}

fn line(code: &mut String, indent: usize, text: &str) {
    writeln!(code, "{}{text}", "    ".repeat(indent)).unwrap();
}

enum RenderError {
    Sequence(SequenceError),
    Labels,
}

impl From<SequenceError> for RenderError {
    fn from(error: SequenceError) -> Self {
        Self::Sequence(error)
    }
}

fn emit_nodes(
    program: &Program,
    nodes: &[Node],
    indent: usize,
    labels: &LoopLabels<'_>,
    expressions: &Expressions,
    code: &mut String,
) -> Result<(), RenderError> {
    for node in nodes {
        match node {
            Node::Evaluate(value) => expressions.statement(code, indent, value, "(void)(", ");")?,
            Node::Step { address, .. } => {
                line(
                    code,
                    indent,
                    &format!("if (!nirvana_step(&m, UINT64_C({address}))) return e->status;"),
                );
                let index = program
                    .instructions()
                    .binary_search_by_key(address, Instruction::address)
                    .expect("validated recovered instruction");
                match &program.instructions()[index] {
                    Instruction::Core(instruction) => {
                        expressions.assignments(code, indent, &instruction.assignments)?;
                    }
                    Instruction::Call(call) => {
                        let (kind, operand) = match call.target {
                            CallTarget::Direct(address) => {
                                ("NIRVANA_DIRECT_TARGET", format!("UINT64_C({address})"))
                            }
                            CallTarget::Register(register) => {
                                ("NIRVANA_DIRECT_TARGET", format!("r[{}]", register.0))
                            }
                            CallTarget::Memory(address) => {
                                ("NIRVANA_MEMORY_TARGET", format!("UINT64_C({address})"))
                            }
                            CallTarget::Plt(address) => {
                                ("NIRVANA_PLT_TARGET", format!("UINT64_C({address})"))
                            }
                        };
                        line(
                            code,
                            indent,
                            &format!(
                                "if (!nirvana_call_puts(&m, r, {kind}, {operand}, UINT64_C({}), {}, UINT64_C({}))) return e->status;",
                                call.address + u64::from(call.size),
                                u8::from(call.tail),
                                program.puts_address(),
                            ),
                        );
                    }
                }
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                if taken.is_empty() && not_taken.is_empty() {
                    expressions.statement(code, indent, condition, "(void)(", ");")?;
                    continue;
                }
                let (inner, condition) = expressions.begin(code, indent, condition)?;
                let (condition, first, second) = if taken.is_empty() {
                    (format!("!({condition})"), not_taken, taken)
                } else {
                    (condition, taken, not_taken)
                };
                line(code, inner, &format!("if ({condition}) {{"));
                emit_nodes(program, first, inner + 1, labels, expressions, code)?;
                if !second.is_empty() {
                    line(code, inner, "} else {");
                    emit_nodes(program, second, inner + 1, labels, expressions, code)?;
                }
                line(code, inner, "}");
                expressions.end(code, indent, inner);
            }
            Node::Loop(body) => {
                labels.loop_id(node).ok_or(RenderError::Labels)?;
                if let Some(label) = labels.continue_label(node) {
                    line(code, indent, &format!("{label}: ;"));
                }
                line(code, indent, "while (1) {");
                emit_nodes(program, body, indent + 1, labels, expressions, code)?;
                line(code, indent, "}");
                if let Some(label) = labels.break_label(node) {
                    line(code, indent, &format!("{label}: ;"));
                }
            }
            Node::Break => line(code, indent, "break;"),
            Node::Continue => line(code, indent, "continue;"),
            Node::BreakOuter { .. } | Node::ContinueOuter { .. } => {
                let target = labels.target(node).ok_or(RenderError::Labels)?;
                line(code, indent, &format!("goto {target};"));
            }
            Node::Return(value) => {
                expressions.statement(code, indent, value, "e->result = ", ";")?;
                line(code, indent, "e->status = 0; return e->status;");
            }
        }
    }
    Ok(())
}

// These are comments about the initial image, not inferred immutable strings.
// Both scanning and output are bounded; only explicit pointer constants are
// candidates, rather than unrelated strings found elsewhere in an ELF image.
fn initial_string_views(program: &Program, image: &crate::loader::LinkedImage) -> String {
    const MAX_CANDIDATES: usize = 256;
    const MAX_STRINGS: usize = 16;
    const MAX_LENGTH: usize = 96;
    let mut candidates = BTreeSet::new();
    let mut pending = Vec::new();
    for instruction in program.instructions() {
        if let Instruction::Core(instruction) = instruction {
            for assignment in &instruction.assignments {
                if let Place::Memory { address, .. } = &assignment.destination {
                    pending.push(address);
                }
                pending.push(&assignment.value);
            }
            match &instruction.control {
                Control::Branch { condition, .. } => pending.push(condition),
                Control::Return(value) => pending.push(value),
                _ => {}
            }
        }
    }
    while let Some(expr) = pending.pop() {
        match expr {
            Expr::Const(address) if candidates.len() < MAX_CANDIDATES => {
                candidates.insert(*address);
            }
            Expr::Binary(_, left, right) => pending.extend([&**left, &**right]),
            Expr::Load { address, .. } => pending.push(address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            _ => {}
        }
    }
    let mut code = String::new();
    for address in candidates {
        let Some(offset) = address
            .checked_sub(image.memory_base)
            .and_then(|offset| usize::try_from(offset).ok())
        else {
            continue;
        };
        let Some(bytes) = image.memory.get(offset..) else {
            continue;
        };
        let Some(length) = bytes
            .iter()
            .take(MAX_LENGTH + 1)
            .position(|&byte| byte == 0)
        else {
            continue;
        };
        if length == 0
            || !bytes[..length]
                .iter()
                .all(|byte| byte.is_ascii_graphic() || matches!(byte, b' ' | b'\n' | b'\r' | b'\t'))
        {
            continue;
        }
        if code.is_empty() {
            code.push_str("/* Initial guest string views; calls read mutable guest memory.\n");
        }
        write!(code, "   {address:#x}: \"").unwrap();
        for byte in &bytes[..length] {
            match byte {
                b'\n' => code.push_str("\\n"),
                b'\r' => code.push_str("\\r"),
                b'\t' => code.push_str("\\t"),
                b'\\' => code.push_str("\\\\"),
                b'\"' => code.push_str("\\\""),
                // Prevent comment terminators and C trigraphs even in C11.
                b'*' | b'/' | b'?' => write!(code, "\\{byte:03o}").unwrap(),
                _ => code.push(char::from(*byte)),
            }
        }
        code.push_str("\"\n");
        if code.lines().count() > MAX_STRINGS {
            break;
        }
    }
    if !code.is_empty() {
        code.push_str("*/\n");
    }
    code
}
