//! Source-bound induction for loop-entry register facts.
//!
//! A pure normalizer defines the conjunction of its assignment fixed points.
//! It is the identity on every state satisfying that conjunction, even if the
//! normalizer itself is not idempotent. Base and feedback queries prove the
//! property at first entry and after one traversal; faults/returns impose no
//! next-entry claim. Feedback witnesses can be globally unreachable.
use super::{
    Error as RegionError, MAX_REGISTERS, Query, Verdict,
    extraction::{self, Region},
};
use crate::model::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg};
use crate::verification::verify::{Solver, UnknownReason};
use std::time::{Duration, Instant};

pub const MODEL_ID: &str = "checked-loop-entry-induction-v1";
pub const MAX_NORMALIZERS: usize = 16;
pub const MAX_TERMS: usize = 1024;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    Limit,
    Normalizer,
    Source,
    Extraction(extraction::ExtractionError),
    Query(RegionError),
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "loop-entry induction: {self:?}")
    }
}
impl std::error::Error for Error {}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Phase {
    Base,
    Feedback,
}
#[derive(Clone, Debug)]
pub struct Problem {
    source: Program,
    header: u64,
    normalizers: Vec<Assignment>,
    base: Query,
    feedback: Query,
    base_region: Option<Region>,
    feedback_region: Region,
}
#[derive(Clone, Debug)]
pub struct Certificate {
    problem: Problem,
}
#[derive(Clone, Debug)]
pub struct Failure {
    pub phase: Phase,
    pub checked: usize,
    pub verdict: Verdict,
}
#[derive(Clone, Debug)]
pub enum Outcome {
    Verified(Box<Certificate>),
    Unproved(Box<Failure>),
}

fn same(a: &Program, b: &Program) -> bool {
    a.register_count() == b.register_count()
        && entry(a) == entry(b)
        && a.instructions() == b.instructions()
}
fn entry(source: &Program) -> u64 {
    source.cfg().block(source.cfg().entry()).start
}
fn check_normalizers(source: &Program, normalizers: &[Assignment]) -> Result<(), Error> {
    if normalizers.is_empty() || normalizers.len() > MAX_NORMALIZERS {
        return Err(Error::Limit);
    }
    let mut pending = Vec::new();
    for assignment in normalizers {
        if !matches!(assignment.destination,Place::Register(Reg(r)) if r<source.register_count()) {
            return Err(Error::Normalizer);
        }
        pending.push((&assignment.value, 0));
    }
    let mut terms = 0;
    while let Some((expr, depth)) = pending.pop() {
        terms += 1;
        if terms > MAX_TERMS || depth > 32 {
            return Err(Error::Limit);
        }
        match expr {
            Expr::Const(_) => {}
            Expr::Register(Reg(r)) if *r < source.register_count() => {}
            Expr::Register(_) | Expr::Load { .. } => return Err(Error::Normalizer),
            Expr::Unary(_, value) => pending.push((value, depth + 1)),
            Expr::Binary(_, a, b) => pending.extend([(&**a, depth + 1), (&**b, depth + 1)]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([
                (&**condition, depth + 1),
                (&**taken, depth + 1),
                (&**not_taken, depth + 1),
            ]),
        }
    }
    Ok(())
}
fn predicate(normalizers: &[Assignment]) -> Expr {
    normalizers
        .iter()
        .map(|a| {
            let Place::Register(reg) = a.destination else {
                unreachable!("normalizer checked");
            };
            Expr::binary(BinaryOp::Eq, Expr::Register(reg), a.value.clone())
        })
        .reduce(|a, b| Expr::binary(BinaryOp::And, a, b))
        .expect("nonempty checked normalizers")
}
fn property(
    source: &Program,
    normalizers: &[Assignment],
    at_entry: bool,
    terminal: u64,
) -> Result<Query, Error> {
    let marker = Reg(source.register_count());
    let mut instructions = source.instructions().to_vec();
    let root = instructions
        .iter_mut()
        .find(|i| i.address == entry(source))
        .ok_or(Error::Source)?;
    if at_entry {
        root.assignments.extend_from_slice(normalizers);
    }
    root.assignments.push(Assignment {
        destination: marker.into(),
        value: Expr::Const(0),
    });
    let left = Program::new(
        entry(source),
        source.register_count() + 1,
        instructions.clone(),
    )
    .map_err(|_| Error::Source)?;
    let last = instructions
        .iter_mut()
        .find(|i| i.address == terminal)
        .ok_or(Error::Source)?;
    if !matches!(last.control, Control::Return(Expr::Const(0))) {
        return Err(Error::Source);
    }
    last.assignments.push(Assignment {
        destination: marker.into(),
        value: Expr::binary(BinaryOp::Eq, predicate(normalizers), Expr::Const(0)),
    });
    let right = Program::new(entry(source), source.register_count() + 1, instructions)
        .map_err(|_| Error::Source)?;
    // Original register/return slots are shared; marker is always initialized.
    let shared: Vec<_> = (0..source.register_count()).map(Reg).collect();
    super::query(&left, &right, &shared, &[marker]).map_err(Error::Query)
}
impl Problem {
    pub fn new(source: &Program, header: u64, normalizers: &[Assignment]) -> Result<Self, Error> {
        if source.register_count() > MAX_REGISTERS - 2 {
            return Err(Error::Limit);
        }
        check_normalizers(source, normalizers)?;
        // Extraction preflights every source expression before any clone.
        let feedback =
            extraction::extract(source, header, &[header], None).map_err(Error::Extraction)?;
        let feedback_query = property(
            feedback.program(),
            normalizers,
            true,
            feedback_terminal(&feedback, header)?,
        )?;
        let (base, base_region) = if entry(source) == header {
            let empty = Program::new(
                0,
                source.register_count() + 1,
                vec![IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(Expr::Const(0)),
                }],
            )
            .map_err(|_| Error::Source)?;
            (property(&empty, normalizers, false, 0)?, None)
        } else {
            let prefix = extraction::extract(source, entry(source), &[header], None)
                .map_err(Error::Extraction)?;
            (
                property(
                    prefix.program(),
                    normalizers,
                    false,
                    feedback_terminal(&prefix, header)?,
                )?,
                Some(prefix),
            )
        };
        Ok(Self {
            source: source.clone(),
            header,
            normalizers: normalizers.to_vec(),
            base,
            feedback: feedback_query,
            base_region,
            feedback_region: feedback,
        })
    }
    pub fn validate(&self) -> Result<(), Error> {
        check::validate(self)
    }
    pub fn source(&self) -> &Program {
        &self.source
    }
    pub fn header(&self) -> u64 {
        self.header
    }
    pub fn normalizers(&self) -> &[Assignment] {
        &self.normalizers
    }
    pub fn query(&self, phase: Phase) -> &Query {
        match phase {
            Phase::Base => &self.base,
            Phase::Feedback => &self.feedback,
        }
    }
    pub fn check(&self, solver: &Solver, budget: Duration) -> Outcome {
        if self.validate().is_err() {
            return Outcome::Unproved(Box::new(Failure {
                phase: Phase::Base,
                checked: 0,
                verdict: Verdict::Unknown(UnknownReason::BoundaryMapping),
            }));
        }
        let deadline = Instant::now() + budget.min(Duration::from_secs(30));
        for (index, phase) in [Phase::Base, Phase::Feedback].into_iter().enumerate() {
            if Instant::now() >= deadline {
                return Outcome::Unproved(Box::new(Failure {
                    phase,
                    checked: index,
                    verdict: Verdict::Unknown(UnknownReason::SolverTimeout),
                }));
            }
            let verdict =
                self.query(phase)
                    .check_script(solver, self.query(phase).smt2(), Some(deadline));
            if verdict != Verdict::EquivalentUnderModel {
                return Outcome::Unproved(Box::new(Failure {
                    phase,
                    checked: index + 1,
                    verdict,
                }));
            }
        }
        Outcome::Verified(Box::new(Certificate {
            problem: self.clone(),
        }))
    }
}
fn feedback_terminal(region: &Region, header: u64) -> Result<u64, Error> {
    // Projection has a single requested stop, with tag0; locate it by its
    // independently validated terminal marker rather than source PC arithmetic.
    region.validate().map_err(Error::Extraction)?;
    if region.continuations() != [header] {
        return Err(Error::Source);
    }
    region
        .program()
        .instructions()
        .iter()
        .find_map(|i| {
            (i.assignments.is_empty() && i.control == Control::Return(Expr::Const(0)))
                .then_some(i.address)
        })
        .ok_or(Error::Source)
}
impl Certificate {
    pub fn problem(&self) -> &Problem {
        &self.problem
    }
    pub fn validate(&self) -> Result<(), Error> {
        self.problem.validate()
    }
    pub fn matches(&self, source: &Program, header: u64) -> bool {
        self.problem.header == header && same(&self.problem.source, source)
    }
    /// Identical instructions under an extended unused namespace have the same
    /// old-register behavior. New slots receive no inferred caps.
    pub fn supports_unused_extension(&self, source: &Program, header: u64) -> bool {
        self.problem.header == header
            && self.problem.source.register_count() <= source.register_count()
            && source.register_count() <= MAX_REGISTERS
            && entry(source) == entry(&self.problem.source)
            && source.instructions() == self.problem.source.instructions()
    }
    pub fn bit_caps(&self, source: &Program, header: u64) -> Result<Vec<u8>, Error> {
        self.validate()?;
        if !self.supports_unused_extension(source, header) {
            return Err(Error::Source);
        }
        let mut caps = vec![64; source.register_count()];
        for assignment in &self.problem.normalizers {
            let Place::Register(reg) = assignment.destination else {
                return Err(Error::Normalizer);
            };
            let Expr::Binary(BinaryOp::And, a, b) = &assignment.value else {
                continue;
            };
            let mask = match (&**a, &**b) {
                (Expr::Register(r), Expr::Const(mask)) | (Expr::Const(mask), Expr::Register(r))
                    if *r == reg =>
                {
                    *mask
                }
                _ => continue,
            };
            if let Some(power) = mask.checked_add(1).filter(|power| power.is_power_of_two()) {
                caps[reg.0] = caps[reg.0].min(power.trailing_zeros() as u8);
            }
        }
        Ok(caps)
    }
}

mod check;
#[cfg(test)]
mod tests;
