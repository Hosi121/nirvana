//! Signed representation bounds over the existing checked SSA fixed point.
//!
//! A bound W means the full U64 equals sign_extend_W(its low word), at every
//! reachable read and write. Entry values remain arbitrary. These are storage
//! invariants, separate from unsigned widths and original source C types.
use super::{
    ssa::{Definition, SsaError, SsaFunction},
    ssa_facts::{self, Domain},
};
use crate::model::ir::{BinaryOp as B, Program, Reg, UnaryOp as U, Width};
use std::sync::Arc;

mod report;
mod verify;
pub use verify::{ValidationError, ValidationEvidence};

/// A retained producer proposal, checked independently against source SSA.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Claim {
    Constant(u64),
    Fits(Width),
}

#[derive(Debug)]
struct Certificate {
    graph: SsaFunction,
    claims: Vec<Claim>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    Bottom,
    Constant(u64),
    Fits(Width),
}

fn constant_width(value: u64) -> Width {
    [Width::U8, Width::U16, Width::U32]
        .into_iter()
        .find(|&w| U::SignExtend(w).evaluate(value) == value)
        .unwrap_or(Width::U64)
}
impl State {
    fn width(self) -> Width {
        match self {
            Self::Constant(n) => constant_width(n),
            Self::Fits(w) => w,
            Self::Bottom => Width::U64,
        }
    }
}
impl Domain for State {
    fn bottom() -> Self {
        Self::Bottom
    }
    fn unknown() -> Self {
        Self::Fits(Width::U64)
    }
    fn constant(n: u64) -> Self {
        Self::Constant(n)
    }
    fn number(self) -> Option<u64> {
        if let Self::Constant(n) = self {
            Some(n)
        } else {
            None
        }
    }
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, v) | (v, Self::Bottom) => v,
            (a, b) if a == b => a,
            (a, b) => Self::Fits(a.width().max(b.width())),
        }
    }
    fn finish(self) -> Self {
        if self == Self::Bottom {
            Self::unknown()
        } else {
            self
        }
    }
    fn valid(self) -> bool {
        self != Self::Bottom
    }
    fn follows_from(self, derived: Self) -> bool {
        if !derived.valid() {
            return false;
        }
        match self {
            Self::Bottom => false,
            Self::Constant(n) => derived.number() == Some(n),
            Self::Fits(w) => derived.width().bits() <= w.bits(),
        }
    }
    fn unary(op: U, value: Self) -> Self {
        if value == Self::Bottom {
            return Self::Bottom;
        }
        if let Some(n) = value.number() {
            return Self::Constant(op.evaluate(n));
        }
        match op {
            U::SignExtend(w) => Self::Fits(w.min(value.width())),
            U::Extract { start, .. } if start >= 64 => Self::Constant(0),
            U::Extract {
                start: 0,
                width: Width::U64,
            } => value,
            U::Extract {
                width: Width::U8, ..
            } => Self::Fits(Width::U16),
            U::Extract {
                width: Width::U16, ..
            } => Self::Fits(Width::U32),
            _ => Self::unknown(),
        }
    }
    fn binary(op: B, a: Self, b: Self) -> Self {
        if a == Self::Bottom || b == Self::Bottom {
            return Self::Bottom;
        }
        if let (Some(a), Some(b)) = (a.number(), b.number()) {
            return Self::Constant(op.evaluate(a, b));
        }
        match op {
            B::And | B::Or | B::Xor => Self::Fits(a.width().max(b.width())),
            B::Eq | B::Ne | B::Ult | B::Ule => Self::Fits(Width::U8),
            B::AShr => Self::Fits(a.width()),
            B::SDiv | B::SRem
                if b.number().is_some_and(|d| {
                    let magnitude = (d as i64).unsigned_abs();
                    2 <= magnitude && magnitude < (1u64 << (a.width().bits() - 1))
                }) =>
            {
                Self::Fits(a.width())
            }
            _ => Self::unknown(),
        }
    }
    fn select(c: Self, t: Self, n: Self) -> Self {
        match c {
            Self::Bottom => Self::Bottom,
            Self::Constant(0) => n,
            Self::Constant(_) => t,
            _ => t.join(n),
        }
    }
    fn load(width: Width) -> Self {
        match width {
            Width::U8 => Self::Fits(Width::U16),
            Width::U16 => Self::Fits(Width::U32),
            _ => Self::unknown(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SignedWidths {
    widths: Vec<Width>,
    certificate: Option<Arc<Certificate>>,
    verification: Result<ValidationEvidence, ValidationError>,
}
impl Default for SignedWidths {
    fn default() -> Self {
        Self::failed(ValidationError::Unavailable("not analyzed"))
    }
}
impl SignedWidths {
    pub fn analyze(source: &Program) -> Self {
        Self::checked(source).unwrap_or_else(Self::failed)
    }
    pub fn width(&self, register: Reg) -> Width {
        self.widths.get(register.0).copied().unwrap_or(Width::U64)
    }

    /// Evidence covers source-entry observations, before signed presentation.
    /// A failure exposes no partial storage or SSA certificate.
    pub fn verification(&self) -> Result<&ValidationEvidence, &ValidationError> {
        self.verification.as_ref()
    }

    pub fn widths(&self) -> Option<&[Width]> {
        self.verification.as_ref().ok()?;
        Some(&self.widths)
    }

    /// The retained source-bound SSA used by the independent checker.
    pub fn ssa(&self) -> Option<&SsaFunction> {
        self.verification.as_ref().ok()?;
        self.certificate
            .as_ref()
            .map(|certificate| &certificate.graph)
    }

    pub fn to_json(&self) -> Result<String, String> {
        report::render(self)
    }

    fn failed(error: ValidationError) -> Self {
        Self {
            widths: Vec::new(),
            certificate: None,
            verification: Err(error),
        }
    }

    fn checked(source: &Program) -> Result<Self, ValidationError> {
        let graph = SsaFunction::build(source)
            .ok_or(ValidationError::Unavailable("SSA construction limit"))?;
        let values = ssa_facts::solve::<State>(source, &graph).map_err(inference_error)?;
        ssa_facts::validate_facts(source, &graph, &values).map_err(inference_error)?;
        let mut observed = vec![None; source.register_count()];
        let mut observe = |reg: Reg, id: super::ssa::ValueId| {
            let width = values[id.0].width();
            observed[reg.0] = Some(observed[reg.0].map_or(width, |old: Width| old.max(width)));
        };
        for block in &graph.blocks {
            for point in &block.points {
                for read in &point.reads {
                    observe(read.register, read.value);
                }
                if let Some(id) = point.definition {
                    let Definition::Assignment { register, .. } = graph.values[id.0] else {
                        return Err(ValidationError::Invalid("inference assignment definition"));
                    };
                    observe(register, id);
                }
            }
        }
        let widths: Vec<_> = observed
            .into_iter()
            .map(|w| w.unwrap_or(Width::U64))
            .collect();
        let claims = values
            .into_iter()
            .map(|value| match value {
                State::Constant(n) => Ok(Claim::Constant(n)),
                State::Fits(width) => Ok(Claim::Fits(width)),
                State::Bottom => Err(ValidationError::Invalid("unfinished inference value")),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let verification = verify::validate(source, &graph, &claims, &widths)?;
        Ok(Self {
            widths,
            certificate: Some(Arc::new(Certificate { graph, claims })),
            verification: Ok(verification),
        })
    }
}

fn inference_error(error: SsaError) -> ValidationError {
    match error {
        SsaError::Unavailable(reason) => ValidationError::Unavailable(reason),
        SsaError::Malformed(reason) => ValidationError::Invalid(reason),
    }
}

/// Recheck the retained proposal against the particular original source.
/// A successful cached result never substitutes for this source-bound check.
pub fn validate(
    source: &Program,
    candidate: &SignedWidths,
) -> Result<ValidationEvidence, ValidationError> {
    candidate.verification.as_ref().map_err(|error| *error)?;
    let certificate = candidate
        .certificate
        .as_ref()
        .ok_or(ValidationError::Invalid("missing retained certificate"))?;
    verify::validate(
        source,
        &certificate.graph,
        &certificate.claims,
        &candidate.widths,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::ir::{Assignment, Control, Expr, IrInstruction};
    fn program(mut assignments: Vec<Assignment>) -> Program {
        assignments.push(Assignment {
            destination: Reg(2).into(),
            value: Expr::binary(B::SDiv, Expr::Register(Reg(1)), Expr::Const(31)),
        });
        Program::new(
            0,
            3,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments,
                control: Control::Return(Expr::Register(Reg(2))),
            }],
        )
        .unwrap()
    }
    #[test]
    fn copied_words_and_extended_divisions_keep_checked_signed_bounds() {
        let p = program(vec![Assignment {
            destination: Reg(1).into(),
            value: Expr::unary(U::SignExtend(Width::U32), Expr::Register(Reg(0))),
        }]);
        let facts = SignedWidths::analyze(&p);
        assert!(facts.verification().is_ok());
        assert_eq!(validate(&p, &facts).as_ref(), facts.verification());
        assert_eq!(facts.width(Reg(0)), Width::U64);
        assert_eq!(facts.width(Reg(1)), Width::U32);
        assert_eq!(facts.width(Reg(2)), Width::U32);
        let mut early = p.instructions().to_vec();
        early[0].assignments.insert(
            0,
            Assignment {
                destination: Reg(2).into(),
                value: Expr::Register(Reg(1)),
            },
        );
        let early = Program::new(0, 3, early).unwrap();
        assert_eq!(SignedWidths::analyze(&early).width(Reg(1)), Width::U64);
    }
    #[test]
    fn initial_values_and_forged_smaller_bounds_are_rejected() {
        let p = program(vec![Assignment {
            destination: Reg(1).into(),
            value: Expr::unary(U::SignExtend(Width::U32), Expr::Register(Reg(0))),
        }]);
        let graph = SsaFunction::build(&p).unwrap();
        let facts = ssa_facts::solve::<State>(&p, &graph).unwrap();
        for (id, definition) in graph.values.iter().enumerate() {
            if matches!(
                definition,
                Definition::Initial { .. }
                    | Definition::Assignment {
                        register: Reg(1),
                        ..
                    }
            ) {
                let mut wrong = facts.clone();
                wrong[id] = State::Fits(Width::U8);
                assert!(ssa_facts::validate_facts(&p, &graph, &wrong).is_err());
            }
        }
    }

    #[test]
    fn retained_proposals_are_rechecked_against_source_and_mutated_claims() {
        let source = program(vec![Assignment {
            destination: Reg(1).into(),
            value: Expr::unary(U::SignExtend(Width::U32), Expr::Register(Reg(0))),
        }]);
        let candidate = SignedWidths::analyze(&source);
        assert!(candidate.verification().is_ok());
        assert!(candidate.ssa().is_some());

        let mut wrong_width = candidate.clone();
        wrong_width.widths[1] = Width::U8;
        assert!(matches!(
            validate(&source, &wrong_width),
            Err(ValidationError::Invalid(_))
        ));

        let original = candidate.certificate.as_ref().unwrap();
        let id = original
            .graph
            .values
            .iter()
            .position(|definition| {
                matches!(
                    definition,
                    Definition::Assignment {
                        register: Reg(1),
                        ..
                    }
                )
            })
            .unwrap();
        let mut claims = original.claims.clone();
        claims[id] = Claim::Constant(0);
        let mut wrong_claim = candidate.clone();
        wrong_claim.certificate = Some(Arc::new(Certificate {
            graph: original.graph.clone(),
            claims,
        }));
        assert!(matches!(
            validate(&source, &wrong_claim),
            Err(ValidationError::Invalid(_))
        ));

        let mut changed = source.instructions().to_vec();
        changed[0].assignments[0].value = Expr::Register(Reg(0));
        let changed = Program::new(0, 3, changed).unwrap();
        assert!(matches!(
            validate(&changed, &candidate),
            Err(ValidationError::Invalid(_))
        ));
    }

    #[test]
    fn resource_failure_retains_reason_and_discards_partial_proposal() {
        let source = Program::new(
            0,
            super::super::ssa::MAX_REGISTERS + 1,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Const(0)),
            }],
        )
        .unwrap();
        let candidate = SignedWidths::analyze(&source);
        assert_eq!(
            candidate.verification(),
            Err(&ValidationError::Unavailable("SSA construction limit"))
        );
        assert!(candidate.widths().is_none());
        assert!(candidate.ssa().is_none());
        assert_eq!(candidate.width(Reg(0)), Width::U64);
        assert_eq!(candidate.width(Reg(usize::MAX)), Width::U64);
        assert_eq!(
            validate(&source, &candidate),
            Err(ValidationError::Unavailable("SSA construction limit"))
        );
        assert!(
            candidate
                .to_json()
                .unwrap()
                .contains("SSA construction limit")
        );
    }
}
