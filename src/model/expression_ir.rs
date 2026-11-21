//! Value-bound arithmetic selection before C liveness and storage allocation.
//!
//! A snapshot captures a pure numerator at its original high-product definition.
//! Selected division/remainder expressions refer to that immutable value ID.
//! Lowering produces ordinary executable IR with certified reciprocal kernels:
//! every subsequent analysis sees all actual reads, including extended lifetimes.
//! The executable input and all its memory operations remain separate and intact.

use std::collections::BTreeMap;

use crate::dataflow::value_graph::{self, Point, Work};
use crate::model::ir::{Assignment, BinaryOp as B, Expr, Place, Program, Reg};
use crate::transform::arithmetic_graph::{ArithmeticFacts, QuotientFact, RemainderFact};
use crate::transform::context_remainder::{ContextEvidence, ContextRemainders};

const MAX_SELECTIONS: usize = 4096;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ValueId(usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArithmeticExpression {
    UnsignedDivide { value: ValueId, divisor: u64 },
    UnsignedRemainder { value: ValueId, divisor: u64 },
}
impl ArithmeticExpression {
    fn parts(self) -> (ValueId, u64) {
        match self {
            Self::UnsignedDivide { value, divisor }
            | Self::UnsignedRemainder { value, divisor } => (value, divisor),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ValueDefinition {
    id: ValueId,
    point: Point,
    expression: Expr,
    /// Some for an explicit snapshot; None for an unchanged operand at its use.
    storage: Option<Reg>,
}
impl ValueDefinition {
    pub fn id(&self) -> ValueId {
        self.id
    }
    pub fn point(&self) -> Point {
        self.point
    }
    pub fn expression(&self) -> &Expr {
        &self.expression
    }
    pub fn storage(&self) -> Option<Reg> {
        self.storage
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Proof {
    Quotient(QuotientFact),
    Remainder {
        quotient: QuotientFact,
        remainder: RemainderFact,
    },
    Context(ContextEvidence),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Selection {
    pub point: Point,
    pub expression: ArithmeticExpression,
    proof: Proof,
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ExpressionEvidence {
    pub snapshots: usize,
    pub divisions: usize,
    pub remainders: usize,
}
#[derive(Clone, Debug)]
pub struct ExpressionPlan {
    values: Vec<ValueDefinition>,
    selections: Vec<Selection>,
}

impl ExpressionPlan {
    pub fn analyze(source: &Program) -> Option<Self> {
        let mut work = Work::new();
        value_graph::preflight(source, &mut work)?;
        let facts = ArithmeticFacts::analyze(source)?;
        let contexts = ContextRemainders::analyze(source)?;
        let mut values = Vec::new();
        let mut selections = Vec::new();
        let mut snapshots = BTreeMap::new();
        let mut quotients = BTreeMap::new();
        let mut fresh = source.register_count();
        for &fact in facts.quotients() {
            work.spend(1)?;
            let value = if let Some(&value) = snapshots.get(&fact.high_definition) {
                value
            } else {
                let expression = source_numerator(source, &fact)?;
                if !value_graph::pure(expression, &mut work)? {
                    return None;
                }
                if fresh >= value_graph::MAX_REGISTERS {
                    return None;
                }
                let id = ValueId(values.len());
                values.push(ValueDefinition {
                    id,
                    point: fact.high_definition,
                    expression: expression.clone(),
                    storage: Some(Reg(fresh)),
                });
                fresh += 1;
                snapshots.insert(fact.high_definition, id);
                id
            };
            quotients.insert(fact.point, (fact, value));
            selections.push(Selection {
                point: fact.point,
                expression: ArithmeticExpression::UnsignedDivide {
                    value,
                    divisor: fact.divisor,
                },
                proof: Proof::Quotient(fact),
            });
        }
        for &remainder in facts.remainders() {
            work.spend(1)?;
            let &(quotient, value) = quotients.get(&remainder.quotient_definition)?;
            selections.push(Selection {
                point: remainder.point,
                expression: ArithmeticExpression::UnsignedRemainder {
                    value,
                    divisor: remainder.divisor,
                },
                proof: Proof::Remainder {
                    quotient,
                    remainder,
                },
            });
        }
        for &proof in contexts.evidence() {
            work.spend(1)?;
            let point = Point {
                instruction: proof.instruction,
                assignment: proof.assignment,
            };
            if selections.iter().any(|s| s.point == point) {
                continue;
            }
            let Expr::Binary(B::Sub, lhs, _) = &at(source, point)?.value else {
                return None;
            };
            if !value_graph::pure(lhs, &mut work)? {
                return None;
            }
            let value = ValueId(values.len());
            values.push(ValueDefinition {
                id: value,
                point,
                expression: (**lhs).clone(),
                storage: None,
            });
            selections.push(Selection {
                point,
                expression: ArithmeticExpression::UnsignedRemainder {
                    value,
                    divisor: proof.divisor,
                },
                proof: Proof::Context(proof),
            });
        }
        if selections.is_empty() || selections.len() > MAX_SELECTIONS {
            return None;
        }
        selections.sort_by_key(|s| s.point);
        let plan = Self { values, selections };
        // A consumer rederives the source facts rather than trusting this plan.
        validate_plan(source, &plan, &mut work)?;
        Some(plan)
    }
    pub fn values(&self) -> &[ValueDefinition] {
        &self.values
    }
    pub fn selections(&self) -> &[Selection] {
        &self.selections
    }
    pub fn evidence(&self) -> ExpressionEvidence {
        ExpressionEvidence {
            snapshots: self.values.iter().filter(|v| v.storage.is_some()).count(),
            divisions: self
                .selections
                .iter()
                .filter(|s| matches!(s.expression, ArithmeticExpression::UnsignedDivide { .. }))
                .count(),
            remainders: self
                .selections
                .iter()
                .filter(|s| matches!(s.expression, ArithmeticExpression::UnsignedRemainder { .. }))
                .count(),
        }
    }
    /// The returned program is the common input to widths, reads and allocation.
    /// Pure dead definitions may subsequently be removed with display_dce.
    pub fn lower(&self, source: &Program) -> Option<Program> {
        let mut work = Work::new();
        value_graph::preflight(source, &mut work)?;
        validate_plan(source, self, &mut work)?;
        let mut instructions = Vec::with_capacity(source.instructions().len());
        for instruction in source.instructions() {
            let mut lowered = instruction.clone();
            lowered.assignments.clear();
            for (assignment, original) in instruction.assignments.iter().enumerate() {
                let point = Point {
                    instruction: instruction.address,
                    assignment,
                };
                for value in &self.values {
                    work.spend(1)?;
                    if value.point == point
                        && let Some(storage) = value.storage
                    {
                        lowered.assignments.push(Assignment {
                            destination: storage.into(),
                            value: clone_pure(&value.expression, &mut work)?,
                        });
                    }
                }
                let mut target = original.clone();
                if let Some(selection) = self.selection(point) {
                    target.value = lower_expression(source, self, selection, &mut work)?;
                }
                lowered.assignments.push(target);
            }
            instructions.push(lowered);
        }
        let count = source
            .register_count()
            .checked_add(self.evidence().snapshots)?;
        let candidate = Program::new(
            source.cfg().block(source.cfg().entry()).start,
            count,
            instructions,
        )
        .ok()?;
        validate(source, self, &candidate).then_some(candidate)
    }
    fn selection(&self, point: Point) -> Option<&Selection> {
        Some(
            &self.selections[self
                .selections
                .binary_search_by_key(&point, |s| s.point)
                .ok()?],
        )
    }
}

/// Check actual lowered instructions, explicit captures, every original effect,
/// all untouched source expressions and source-bound arithmetic certificates.
/// The comparison is performed before recursive AST equality on bounded inputs.
pub fn validate(source: &Program, plan: &ExpressionPlan, candidate: &Program) -> bool {
    verify_lowering(source, plan, candidate).is_some()
}
fn verify_lowering(source: &Program, plan: &ExpressionPlan, candidate: &Program) -> Option<()> {
    let mut work = Work::new();
    value_graph::preflight(source, &mut work)?;
    value_graph::preflight(candidate, &mut work)?;
    validate_plan(source, plan, &mut work)?;
    if candidate.register_count()
        != source
            .register_count()
            .checked_add(plan.evidence().snapshots)?
        || source.cfg().block(source.cfg().entry()).start
            != candidate.cfg().block(candidate.cfg().entry()).start
        || source.instructions().len() != candidate.instructions().len()
    {
        return None;
    }
    for (original, target) in source.instructions().iter().zip(candidate.instructions()) {
        if original.address != target.address
            || original.size != target.size
            || original.control != target.control
        {
            return None;
        }
        let mut cursor = 0;
        for (assignment, original) in original.assignments.iter().enumerate() {
            let point = Point {
                instruction: target.address,
                assignment,
            };
            for value in &plan.values {
                work.spend(1)?;
                if value.point == point
                    && let Some(storage) = value.storage
                {
                    let capture = target.assignments.get(cursor)?;
                    if capture.destination != Place::Register(storage)
                        || capture.value != value.expression
                    {
                        return None;
                    }
                    cursor += 1;
                }
            }
            let actual = target.assignments.get(cursor)?;
            if actual.destination != original.destination {
                return None;
            }
            if let Some(selection) = plan.selection(point) {
                let expected = lower_expression(source, plan, selection, &mut work)?;
                if actual.value != expected {
                    return None;
                }
            } else if actual.value != original.value {
                return None;
            }
            cursor += 1;
        }
        if cursor != target.assignments.len() {
            return None;
        }
    }
    Some(())
}

fn validate_plan(source: &Program, plan: &ExpressionPlan, work: &mut Work) -> Option<()> {
    if plan.selections.is_empty()
        || plan.selections.len() > MAX_SELECTIONS
        || plan.values.len() > MAX_SELECTIONS
    {
        return None;
    }
    // Rebuild once for this consumer, bounding total graph work for all facts.
    let facts = ArithmeticFacts::analyze(source)?;
    let contexts = ContextRemainders::analyze(source)?;
    let mut used = vec![false; plan.values.len()];
    let mut fresh = source.register_count();
    for (index, value) in plan.values.iter().enumerate() {
        work.spend(1)?;
        if value.id != ValueId(index) || !value_graph::pure(&value.expression, work)? {
            return None;
        }
        if let Some(storage) = value.storage {
            if storage != Reg(fresh) || fresh >= value_graph::MAX_REGISTERS {
                return None;
            }
            fresh += 1;
        }
    }
    let mut previous = None;
    for selection in &plan.selections {
        work.spend(1)?;
        if previous.is_some_and(|p| p >= selection.point) {
            return None;
        }
        previous = Some(selection.point);
        let (id, divisor) = selection.expression.parts();
        let value = plan.values.get(id.0)?;
        used[id.0] = true;
        match selection.proof {
            Proof::Quotient(fact) => {
                if !facts.quotients().contains(&fact)
                    || selection.point != fact.point
                    || selection.expression
                        != (ArithmeticExpression::UnsignedDivide {
                            value: id,
                            divisor: fact.divisor,
                        })
                    || value.storage.is_none()
                    || value.point != fact.high_definition
                    || value.expression != *source_numerator(source, &fact)?
                {
                    return None;
                }
            }
            Proof::Remainder {
                quotient,
                remainder,
            } => {
                if !facts.quotients().contains(&quotient)
                    || !facts.remainders().contains(&remainder)
                    || remainder.quotient_definition != quotient.point
                    || selection.point != remainder.point
                    || selection.expression
                        != (ArithmeticExpression::UnsignedRemainder {
                            value: id,
                            divisor: quotient.divisor,
                        })
                    || divisor != remainder.divisor
                    || value.storage.is_none()
                    || value.point != quotient.high_definition
                    || value.expression != *source_numerator(source, &quotient)?
                {
                    return None;
                }
            }
            Proof::Context(proof) => {
                if !contexts.evidence().contains(&proof)
                    || selection.point
                        != (Point {
                            instruction: proof.instruction,
                            assignment: proof.assignment,
                        })
                    || selection.expression
                        != (ArithmeticExpression::UnsignedRemainder {
                            value: id,
                            divisor: proof.divisor,
                        })
                    || value.storage.is_some()
                    || value.point != selection.point
                {
                    return None;
                }
                let Expr::Binary(B::Sub, lhs, _) = &at(source, selection.point)?.value else {
                    return None;
                };
                if value.expression != **lhs {
                    return None;
                }
            }
        }
    }
    used.iter().all(|&v| v).then_some(())
}

fn lower_expression(
    source: &Program,
    plan: &ExpressionPlan,
    selection: &Selection,
    work: &mut Work,
) -> Option<Expr> {
    let (id, _) = selection.expression.parts();
    let value = plan.values.get(id.0)?;
    let operand = match value.storage {
        Some(storage) => Expr::Register(storage),
        None => clone_pure(&value.expression, work)?,
    };
    let quotient = match selection.proof {
        Proof::Quotient(fact) | Proof::Remainder { quotient: fact, .. } => Expr::binary(
            B::Shr,
            Expr::binary(
                B::UMulHigh,
                Expr::Const(fact.certificate.multiplier),
                operand.clone(),
            ),
            Expr::Const(u64::from(fact.certificate.shift)),
        ),
        Proof::Context(proof) => clone_pure(
            &at(
                source,
                Point {
                    instruction: proof.definition_instruction,
                    assignment: proof.definition_assignment,
                },
            )?
            .value,
            work,
        )?,
    };
    match selection.expression {
        ArithmeticExpression::UnsignedDivide { divisor, .. } => {
            let view = crate::transform::division_expr::recognize(&quotient)?;
            (view.divisor == divisor).then_some(quotient)
        }
        ArithmeticExpression::UnsignedRemainder { divisor, .. } => {
            let expression = Expr::binary(
                B::Sub,
                operand,
                Expr::binary(B::Mul, quotient, Expr::Const(divisor)),
            );
            let view = crate::transform::remainder_expr::recognize(&expression)?;
            (view.divisor == divisor).then_some(expression)
        }
    }
}
fn clone_pure(expression: &Expr, work: &mut Work) -> Option<Expr> {
    value_graph::pure(expression, work)?.then(|| expression.clone())
}
fn source_numerator<'a>(source: &'a Program, fact: &QuotientFact) -> Option<&'a Expr> {
    let Expr::Binary(B::UMulHigh, left, right) = &at(source, fact.high_definition)?.value else {
        return None;
    };
    match (&**left, &**right) {
        (Expr::Const(m), value) if *m == fact.certificate.multiplier => Some(value),
        (value, Expr::Const(m)) if *m == fact.certificate.multiplier => Some(value),
        _ => None,
    }
}
fn at(source: &Program, point: Point) -> Option<&Assignment> {
    let index = source
        .instructions()
        .binary_search_by_key(&point.instruction, |i| i.address)
        .ok()?;
    source.instructions()[index]
        .assignments
        .get(point.assignment)
}
