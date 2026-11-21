//! Prepare display expressions and structured candidates without changing the
//! reduced executable IR or its structure certificate.

use crate::control_flow::structure::{Node, StructureError, StructureStats, StructuredFunction};
use crate::control_flow::structure_verify::StructureEvidence;
use crate::dataflow::value_width::ValueWidths;
use crate::model::ir::{Assignment, BinaryOp, Control, Expr, Place, Program, Reg, Width};
use crate::transform::reduce::ReductionError;

use super::{WebRecovery, webs};

pub(super) struct PreparedFunction {
    pub program: Program,
    pub widths: ValueWidths,
    pub structure: Result<StructuredFunction, StructureError>,
    pub nodes: Option<Vec<Node>>,
    pub shared_nodes: Option<Vec<Node>>,
    pub source_evidence: Option<StructureEvidence>,
    pub source_stats: Option<StructureStats>,
    pub web_recovery: WebRecovery,
    pub load_mask_evidence: Option<crate::transform::load_mask::LoadMaskEvidence>,
    pub expression_evidence: Option<crate::model::expression_ir::ExpressionEvidence>,
    pub semantic_evidence: Option<crate::model::semantic_ir::SemanticEvidence>,
    pub ssa_constants: Option<crate::dataflow::ssa_constants::ConstantEvidence>,
    pub known_bits: Option<crate::dataflow::known_bits::BitEvidence>,
}

type CheckedDisplay<E> = (
    Program,
    ValueWidths,
    Result<StructuredFunction, StructureError>,
    E,
);
fn checked_display<E>(
    expanded: Program,
    structured_before: bool,
    evidence: E,
) -> Option<CheckedDisplay<E>> {
    let candidate = crate::transform::display_dce::propose(&expanded)?;
    if !crate::transform::display_dce::validate(&expanded, &candidate) {
        return None;
    }
    let structure = StructuredFunction::recover(&candidate);
    if structured_before && structure.is_err() {
        return None;
    }
    let widths = ValueWidths::analyze(&candidate);
    Some((candidate, widths, structure, evidence))
}

pub(super) fn prepare(
    original: &Program,
    parameters: &[Reg],
) -> Result<PreparedFunction, ReductionError> {
    let selected = webs::select(original);
    let renamed = matches!(selected.recovery, WebRecovery::Applied { .. });
    match prepare_selected(original, parameters, selected) {
        Err(error) if renamed => prepare_original(
            original,
            parameters,
            WebRecovery::RenderingFallback(super::ReadableError::Reduction(error)),
        ),
        result => result,
    }
}

pub(super) fn prepare_original(
    original: &Program,
    parameters: &[Reg],
    recovery: WebRecovery,
) -> Result<PreparedFunction, ReductionError> {
    prepare_selected(
        original,
        parameters,
        webs::keep_original(original, recovery),
    )
}

fn prepare_selected(
    original: &Program,
    parameters: &[Reg],
    selected: webs::SelectedWebs,
) -> Result<PreparedFunction, ReductionError> {
    let input = selected.program.as_ref().unwrap_or(original);
    let masked = crate::transform::load_mask::propose(input, parameters).and_then(|candidate| {
        crate::transform::load_mask::validate(input, &candidate, parameters)
            .ok()
            .map(|evidence| (candidate, evidence))
    });
    let input = masked.as_ref().map_or(input, |(program, _)| program);
    let widths = ValueWidths::analyze(input);
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
    let program = presentation_program(input, &width)?;
    // Each paired rewrite has its own correspondence evidence. Recover a
    // fresh tree from that same program, while retaining the source certificate.
    let structure = if masked.is_some() {
        StructuredFunction::recover(input)
    } else {
        selected.structure
    };
    // SSA facts cross predecessor edges and loop phis. Check the actual
    // constant rewrite and subsequent DCE before rebuilding structure/widths.
    let constants =
        crate::dataflow::ssa_constants::ConstantPlan::analyze(&program).and_then(|plan| {
            let (expanded, evidence) = plan.propose(&program)?;
            checked_display(expanded, structure.is_ok(), evidence)
        });
    let (program, widths, structure, ssa_constants) = match constants {
        Some((program, widths, structure, evidence)) => {
            (program, widths, structure, Some(evidence))
        }
        None => (program, widths, structure, None),
    };
    let bits = crate::dataflow::known_bits::BitPlan::analyze(&program).and_then(|plan| {
        let (expanded, evidence) = plan.propose(&program)?;
        checked_display(expanded, structure.is_ok(), evidence)
    });
    let (program, widths, structure, known_bits) = match bits {
        Some((p, w, s, e)) => (p, w, s, Some(e)),
        None => (program, widths, structure, None),
    };
    // Choose arithmetic before any read/liveness/allocation consumer. Explicit
    // snapshots retain historical numerators; independent DCE removes pure work.
    let arithmetic =
        crate::model::expression_ir::ExpressionPlan::analyze(&program).and_then(|plan| {
            checked_display(plan.lower(&program)?, structure.is_ok(), plan.evidence())
        });
    let (program, widths, structure, expression_evidence) = match arithmetic {
        Some((program, widths, structure, evidence)) => {
            (program, widths, structure, Some(evidence))
        }
        None => (program, widths, structure, None),
    };
    let semantic = crate::model::semantic_ir::SemanticPlan::analyze(&program).and_then(|plan| {
        checked_display(plan.lower(&program)?, structure.is_ok(), plan.evidence())
    });
    let (program, widths, structure, semantic_evidence) = match semantic {
        Some((p, w, s, e)) => (p, w, s, Some(e)),
        None => (program, widths, structure, None),
    };
    let candidates = structure.as_ref().ok().map(|function| {
        let nodes = if expression_evidence.is_some()
            || semantic_evidence.is_some()
            || ssa_constants.is_some()
            || known_bits.is_some()
        {
            function.body().to_vec()
        } else {
            let width = |reg| {
                if parameters.contains(&reg) {
                    Width::U64
                } else {
                    widths.width(reg)
                }
            };
            presentation_nodes(function.body(), &width)
        };
        // Exact program points are part of suffix equality: memory views
        // are proved at those points. Keep the original presentation tree
        // when the whole bounded pass cannot complete.
        let shared = crate::control_flow::branch_tail::factor(&nodes);
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
        source_evidence: selected.source_evidence,
        source_stats: selected.source_stats,
        web_recovery: selected.recovery,
        load_mask_evidence: masked.map(|(_, evidence)| evidence),
        expression_evidence,
        semantic_evidence,
        ssa_constants,
        known_bits,
    })
}

pub(super) fn is_break(nodes: &[Node]) -> bool {
    matches!(nodes, [Node::Break])
}
pub(super) fn is_continue(nodes: &[Node]) -> bool {
    matches!(nodes, [Node::Continue])
}
pub(super) fn invert(condition: &Expr) -> Expr {
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
                address: crate::codegen::presentation::normalize(address, width),
                width: *size,
            },
        },
        value: crate::codegen::presentation::normalize(&a.value, width),
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
                *condition = crate::codegen::presentation::normalize(condition, width);
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
            Node::Evaluate(value) => {
                Node::Evaluate(crate::codegen::presentation::normalize(value, width))
            }
            Node::Return(value) => {
                Node::Return(crate::codegen::presentation::normalize(value, width))
            }
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
                condition: crate::codegen::presentation::normalize(condition, width),
                taken: presentation_nodes(taken, width),
                not_taken: presentation_nodes(not_taken, width),
            },
            Node::Loop(body) => Node::Loop(presentation_nodes(body, width)),
            _ => node.clone(),
        })
        .collect()
}
