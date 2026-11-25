//! Independently check sign-extension facts and original source observations.
//!
//! Source-checked SSA supplies identities and all predecessor alternatives.
//! Numeric transfer, raw-expression replay and storage aggregation are owned
//! here, separate from the producer's State and SSA fixed-point machinery.

use super::Claim;
use crate::dataflow::ssa::{self, Definition, PointValues, SsaError, SsaFunction};
use crate::model::ir::{Control, Expr, Place, Program, Width};
use std::fmt;

mod kernel;
use kernel::Range;

const MAX_WORK: usize = 32_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValidationError {
    Invalid(&'static str),
    Unavailable(&'static str),
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(reason) => write!(f, "signed storage check invalid: {reason}"),
            Self::Unavailable(reason) => write!(f, "signed storage check unavailable: {reason}"),
        }
    }
}
impl std::error::Error for ValidationError {}
use ValidationError::{Invalid, Unavailable};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ValidationEvidence {
    pub registers: usize,
    pub narrow_registers: usize,
    pub values: usize,
    pub constants: usize,
    pub blocks: usize,
    pub phi_inputs: usize,
    pub assignments: usize,
    pub reads: usize,
    pub expressions: usize,
}

struct Work {
    remaining: usize,
    evidence: ValidationEvidence,
}
impl Work {
    fn take(&mut self, amount: usize) -> Result<(), ValidationError> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or(Unavailable("work limit"))?;
        Ok(())
    }
}

pub(super) fn validate(
    source: &Program,
    graph: &SsaFunction,
    claims: &[Claim],
    widths: &[Width],
) -> Result<ValidationEvidence, ValidationError> {
    validate_bounded(source, graph, claims, widths, MAX_WORK)
}

fn validate_bounded(
    source: &Program,
    graph: &SsaFunction,
    claims: &[Claim],
    widths: &[Width],
    limit: usize,
) -> Result<ValidationEvidence, ValidationError> {
    if claims.len() != graph.values.len() || widths.len() != source.register_count() {
        return Err(Invalid("candidate dimensions"));
    }
    // This independently establishes original def/use order, all phi edges,
    // virtual entry and bounded source syntax before our recursive evaluator.
    ssa::validate(source, graph).map_err(|error| match error {
        SsaError::Malformed(reason) => Invalid(reason),
        SsaError::Unavailable(reason) => Unavailable(reason),
    })?;
    let mut work = Work {
        remaining: limit,
        evidence: ValidationEvidence::default(),
    };
    work.take(claims.len() + widths.len() + source.cfg().blocks().len())?;
    let values: Vec<_> = claims
        .iter()
        .map(|claim| match *claim {
            Claim::Constant(value) => Range::exact(value),
            Claim::Fits(width) => Range::storage(width),
        })
        .collect();
    let storage: Vec<_> = widths.iter().copied().map(Range::storage).collect();
    let mut observed = vec![false; source.register_count()];
    work.evidence.registers = source.register_count();
    work.evidence.narrow_registers = widths.iter().filter(|&&w| w != Width::U64).count();
    work.evidence.values = claims.len();
    work.evidence.constants = claims
        .iter()
        .filter(|c| matches!(c, Claim::Constant(_)))
        .count();
    work.evidence.blocks = graph.blocks.len();
    for (index, definition) in graph.values.iter().enumerate() {
        work.take(1)?;
        match definition {
            Definition::Initial { .. } if values[index] != Range::FULL => {
                return Err(Invalid("arbitrary initial boundary"));
            }
            Definition::Phi { inputs, .. } => {
                for input in inputs {
                    work.take(1)?;
                    if !values[index].contains(values[input.value.0]) {
                        return Err(Invalid("phi alternative sign bound"));
                    }
                    work.evidence.phi_inputs += 1;
                }
            }
            _ => {}
        }
    }

    let cfg = source.cfg();
    let mut blocks = vec![None; cfg.blocks().len()];
    for block in &graph.blocks {
        work.take(1)?;
        let id = cfg.block_at(block.start).ok_or(Invalid("source block"))?;
        blocks[id.index()] = Some(block);
    }
    let mut replay = Replay {
        values: &values,
        storage: &storage,
        observed: &mut observed,
        work: &mut work,
    };
    // Traverse original source order. Graph points provide only validated
    // read IDs; neither producer's expression walk nor observation list is used.
    for block in cfg.blocks() {
        let Some(ssa_block) = blocks[block.id.index()] else {
            continue;
        };
        replay.work.take(1)?;
        let mut points = ssa_block.points.iter();
        for instruction in &source.instructions()[block.instructions.clone()] {
            replay.work.take(1)?;
            for (index, assignment) in instruction.assignments.iter().enumerate() {
                replay.work.take(1)?;
                let point = points.next().ok_or(Invalid("missing source point"))?;
                if point.site.instruction != instruction.address
                    || point.site.assignment != Some(index)
                {
                    return Err(Invalid("source assignment point"));
                }
                let mut cursor = 0;
                if let Place::Memory { address, .. } = &assignment.destination {
                    replay.expression(address, point, &mut cursor, 0)?;
                }
                let actual = replay.expression(&assignment.value, point, &mut cursor, 0)?;
                if let Place::Register(reg) = assignment.destination {
                    let id = point
                        .definition
                        .ok_or(Invalid("missing write definition"))?;
                    if !values[id.0].contains(actual) {
                        return Err(Invalid("assignment sign bound"));
                    }
                    replay.observe(reg.0, actual, false)?;
                    replay.work.evidence.assignments += 1;
                } else if point.definition.is_some() {
                    return Err(Invalid("store defines a register"));
                }
                if cursor != point.reads.len() {
                    return Err(Invalid("extra source reads"));
                }
            }
            if let Control::Branch { condition, .. } | Control::Return(condition) =
                &instruction.control
            {
                let point = points.next().ok_or(Invalid("missing control point"))?;
                if point.site.instruction != instruction.address
                    || point.site.assignment.is_some()
                    || point.definition.is_some()
                {
                    return Err(Invalid("source control point"));
                }
                let mut cursor = 0;
                replay.expression(condition, point, &mut cursor, 0)?;
                if cursor != point.reads.len() {
                    return Err(Invalid("extra control reads"));
                }
            }
        }
        if points.next().is_some() {
            return Err(Invalid("extra source points"));
        }
    }
    for (seen, width) in observed.iter().zip(widths) {
        work.take(1)?;
        if !seen && *width != Width::U64 {
            return Err(Invalid("unobserved storage width"));
        }
    }
    Ok(work.evidence)
}

struct Replay<'a> {
    values: &'a [Range],
    storage: &'a [Range],
    observed: &'a mut [bool],
    work: &'a mut Work,
}
impl Replay<'_> {
    fn observe(
        &mut self,
        register: usize,
        value: Range,
        read: bool,
    ) -> Result<(), ValidationError> {
        self.work.take(1)?;
        if !self.storage[register].contains(value) {
            return Err(Invalid(if read {
                "storage read sign bound"
            } else {
                "storage write sign bound"
            }));
        }
        self.observed[register] = true;
        Ok(())
    }

    fn expression(
        &mut self,
        expression: &Expr,
        point: &PointValues,
        cursor: &mut usize,
        depth: usize,
    ) -> Result<Range, ValidationError> {
        self.work.take(1)?;
        self.work.evidence.expressions += 1;
        if depth > ssa::MAX_DEPTH {
            return Err(Unavailable("expression depth"));
        }
        Ok(match expression {
            Expr::Const(value) => Range::exact(*value),
            Expr::Register(register) => {
                let read = point
                    .reads
                    .get(*cursor)
                    .ok_or(Invalid("missing source read"))?;
                if read.register != *register {
                    return Err(Invalid("source read register"));
                }
                *cursor += 1;
                let value = *self
                    .values
                    .get(read.value.0)
                    .ok_or(Invalid("source read identity"))?;
                self.observe(register.0, value, true)?;
                self.work.evidence.reads += 1;
                value
            }
            Expr::Load { address, width } => {
                self.expression(address, point, cursor, depth + 1)?;
                kernel::load(*width)
            }
            Expr::Unary(operation, value) => {
                let value = self.expression(value, point, cursor, depth + 1)?;
                kernel::unary(*operation, value)
            }
            Expr::Binary(operation, left, right) => {
                let a = self.expression(left, point, cursor, depth + 1)?;
                let b = self.expression(right, point, cursor, depth + 1)?;
                kernel::binary(*operation, a, b)
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let c = self.expression(condition, point, cursor, depth + 1)?;
                let a = self.expression(taken, point, cursor, depth + 1)?;
                let b = self.expression(not_taken, point, cursor, depth + 1)?;
                kernel::select(c, a, b)
            }
        })
    }
}

#[cfg(test)]
mod tests;
