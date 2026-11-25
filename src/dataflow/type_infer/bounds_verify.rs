//! Inductive unsigned bounds checked independently of width inference.
//!
//! SSA validation supplies source/edge/read correspondence. This checker then
//! interprets source expressions as unsigned intervals [0, upper] in u128,
//! using possible-bit hulls only where numeric ordering is insufficient.
//! Candidate bounds may be conservative; no fixed-point reconstruction is used.

use crate::dataflow::ssa::{self, Definition, PointValues, SsaFunction};
use crate::dataflow::unsigned_caps::{self, WORD_MAX};
#[cfg(test)]
use crate::dataflow::unsigned_caps::{hull, width};
#[cfg(test)]
use crate::model::ir::{BinaryOp, UnaryOp, Width};
use crate::model::ir::{Control, Expr, Place, Program};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ValidationEvidence {
    pub values: usize,
    /// Register assignments whose resulting unsigned bounds were checked.
    pub assignments: usize,
    /// All phi alternatives, including virtual entry and loop backedges.
    pub phi_inputs: usize,
    /// Source expression nodes, including store addresses and control reads.
    pub expressions: usize,
}

struct Work {
    remaining: usize,
    expressions: usize,
}

impl Work {
    fn take(&mut self, amount: usize) -> Result<(), String> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or("unsigned bound validation work limit")?;
        Ok(())
    }

    fn expression(&mut self) -> Result<(), String> {
        self.take(1)?;
        self.expressions += 1;
        Ok(())
    }
}

pub(super) fn validate(
    source: &Program,
    graph: &SsaFunction,
    bits: &[u8],
) -> Result<ValidationEvidence, String> {
    validate_bounded(source, graph, bits, ssa::MAX_WORK)
}

fn validate_bounded(
    source: &Program,
    graph: &SsaFunction,
    bits: &[u8],
    limit: usize,
) -> Result<ValidationEvidence, String> {
    if graph.values.len() > ssa::MAX_VALUES || bits.len() != graph.values.len() {
        return Err("unsigned bound validation dimensions".into());
    }
    if bits.iter().any(|&n| n > 64) {
        return Err("unsigned bound validation bit count".into());
    }
    // Preflight bounds source depth/nodes and candidate storage before dense
    // allocation or recursive interpretation. This also checks every ordered
    // source read tuple and every phi edge against the original register CFG.
    ssa::validate(source, graph)
        .map_err(|error| format!("unsigned bound validation SSA: {error}"))?;

    let mut work = Work {
        remaining: limit,
        expressions: 0,
    };
    work.take(bits.len())?;
    let caps: Vec<_> = bits
        .iter()
        .map(|&n| unsigned_caps::from_bits(n).unwrap())
        .collect();
    let mut evidence = ValidationEvidence {
        values: graph.values.len(),
        assignments: 0,
        phi_inputs: 0,
        expressions: 0,
    };
    for (index, definition) in graph.values.iter().enumerate() {
        work.take(1)?;
        match definition {
            Definition::Initial { .. } => {
                if caps[index] != WORD_MAX {
                    return Err("unsigned bound validation initial boundary".into());
                }
            }
            Definition::Phi { inputs, .. } => {
                for input in inputs {
                    work.take(1)?;
                    if caps[input.value.0] > caps[index] {
                        return Err("unsigned bound validation phi input".into());
                    }
                    evidence.phi_inputs += 1;
                }
            }
            Definition::Assignment { .. } => {}
        }
    }

    // Walk all validated source points, not just definitions. Loads in store
    // addresses and both Select arms retain their complete syntactic reads.
    for block in &graph.blocks {
        work.take(1)?;
        for point in &block.points {
            work.take(1 + (usize::BITS - source.instructions().len().leading_zeros()) as usize)?;
            let index = source
                .instructions()
                .binary_search_by_key(&point.site.instruction, |instruction| instruction.address)
                .map_err(|_| "unsigned bound validation source instruction")?;
            let instruction = &source.instructions()[index];
            let mut cursor = 0;
            if let Some(assignment_index) = point.site.assignment {
                let assignment = instruction
                    .assignments
                    .get(assignment_index)
                    .ok_or("unsigned bound validation source assignment")?;
                if let Place::Memory { address, .. } = &assignment.destination {
                    upper(address, point, &caps, &mut cursor, &mut work, 1)?;
                }
                let required = upper(&assignment.value, point, &caps, &mut cursor, &mut work, 1)?;
                match assignment.destination {
                    Place::Register(register) => {
                        let id = point
                            .definition
                            .ok_or("unsigned bound validation missing assignment definition")?;
                        if graph.values[id.0]
                            != (Definition::Assignment {
                                site: point.site,
                                register,
                            })
                            || required > caps[id.0]
                        {
                            return Err("unsigned bound validation assignment obligation".into());
                        }
                        evidence.assignments += 1;
                    }
                    Place::Memory { .. } => {
                        if point.definition.is_some() {
                            return Err("unsigned bound validation store definition".into());
                        }
                    }
                }
            } else {
                let expression = match &instruction.control {
                    Control::Branch { condition, .. } | Control::Return(condition) => condition,
                    _ => return Err("unsigned bound validation control point".into()),
                };
                if point.definition.is_some() {
                    return Err("unsigned bound validation control definition".into());
                }
                upper(expression, point, &caps, &mut cursor, &mut work, 1)?;
            }
            if cursor != point.reads.len() {
                return Err("unsigned bound validation extra source reads".into());
            }
        }
    }
    evidence.expressions = work.expressions;
    Ok(evidence)
}

fn upper(
    expression: &Expr,
    point: &PointValues,
    caps: &[u128],
    cursor: &mut usize,
    work: &mut Work,
    depth: usize,
) -> Result<u128, String> {
    work.expression()?;
    if depth > ssa::MAX_DEPTH {
        return Err("unsigned bound validation expression depth".into());
    }
    Ok(match expression {
        Expr::Const(value) => u128::from(*value),
        Expr::Register(register) => {
            let read = point
                .reads
                .get(*cursor)
                .ok_or("unsigned bound validation missing source read")?;
            if read.register != *register {
                return Err("unsigned bound validation source read register".into());
            }
            *cursor += 1;
            *caps
                .get(read.value.0)
                .ok_or("unsigned bound validation source read identity")?
        }
        Expr::Load { address, width } => {
            upper(address, point, caps, cursor, work, depth + 1)?;
            unsigned_caps::load(*width)
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            upper(condition, point, caps, cursor, work, depth + 1)?;
            let taken = upper(taken, point, caps, cursor, work, depth + 1)?;
            let not_taken = upper(not_taken, point, caps, cursor, work, depth + 1)?;
            taken.max(not_taken)
        }
        Expr::Unary(operation, value) => {
            let value = upper(value, point, caps, cursor, work, depth + 1)?;
            unsigned_caps::unary(*operation, value)
        }
        Expr::Binary(operation, left, right) => {
            let a = upper(left, point, caps, cursor, work, depth + 1)?;
            let b = upper(right, point, caps, cursor, work, depth + 1)?;
            let literal = match right.as_ref() {
                Expr::Const(value) => Some(*value),
                _ => None,
            };
            unsigned_caps::binary(*operation, a, b, literal)
        }
    })
}

#[cfg(test)]
mod tests;
