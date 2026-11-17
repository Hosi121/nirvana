//! Prepare display expressions and structured candidates without changing the
//! reduced executable IR or its structure certificate.

use crate::ir::{Assignment, BinaryOp, Control, Expr, Place, Program, Reg, Width};
use crate::reduce::ReductionError;
use crate::structure::{Node, StructureError, StructuredFunction};
use crate::value_width::ValueWidths;

pub(super) struct PreparedFunction {
    pub program: Program,
    pub widths: ValueWidths,
    pub structure: Result<StructuredFunction, StructureError>,
    pub nodes: Option<Vec<Node>>,
    pub shared_nodes: Option<Vec<Node>>,
}

pub(super) fn prepare(
    original: &Program,
    parameters: &[Reg],
) -> Result<PreparedFunction, ReductionError> {
    let widths = ValueWidths::analyze(original);
    let width = |reg| {
        if parameters.contains(&reg) {
            Width::U64
        } else {
            widths.width(reg)
        }
    };
    // A presentation copy keeps the executable IR and its checked structure
    // certificate intact. All dependency/view/allocation analyses see the same
    // expressions that will actually be printed.
    let program = presentation_program(original, &width)?;
    let structure = StructuredFunction::recover(original);
    let candidates = structure.as_ref().ok().map(|function| {
        let nodes = presentation_nodes(function.body(), &width);
        // Exact program points are part of suffix equality: memory views
        // are proved at those points. Keep the original presentation tree
        // when the whole bounded pass cannot complete.
        let shared = crate::branch_tail::factor(&nodes);
        (compact(&nodes), shared.map(|nodes| compact(&nodes)))
    });
    let (nodes, shared_nodes) = match candidates {
        Some((nodes, shared_nodes)) => (Some(nodes), shared_nodes),
        None => (None, None),
    };
    Ok(PreparedFunction {
        program,
        widths,
        structure,
        nodes,
        shared_nodes,
    })
}

pub(super) fn is_break(nodes: &[Node]) -> bool {
    matches!(nodes, [Node::Break])
}
pub(super) fn is_continue(nodes: &[Node]) -> bool {
    matches!(nodes, [Node::Continue])
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
