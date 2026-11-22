//! Source-bound semantic values materialized before storage allocation.
//!
//! Operations name immutable, block-local values and their first source site.
//! Pure input snapshots retain historical values; original memory operations,
//! register writes and instruction boundaries stay in place. Validation checks
//! every changed source subtree against an available certified value.
//! Lowered execution starts at the original CFG entry; full state comparison
//! projects registers onto the original prefix. Fresh captures are internal.
use crate::dataflow::value_graph::{self, BlockValues, Point, ValueGraph, ValueId, Work};
use crate::model::ir::{Assignment, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use crate::transform::signed_division_expr::SignedDivisionEvidence;
use std::collections::{BTreeMap, BTreeSet};

mod signed;
mod value;
mod word;
const MAX_CAPTURES: usize = 4096;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArithmeticKind {
    SignedDivide64,
    SignedRemainder64,
    SignedDivide(Width),
    SignedRemainder(Width),
    /// Signed word input; the mathematical result is sign-extended to U64.
    SignedDivideExtended(Width),
    SignedRemainderExtended(Width),
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SemanticEvidence {
    pub inputs: usize,
    pub divisions: usize,
    pub remainders: usize,
    pub replaced_subtrees: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Equation {
    block: u64,
    result: ValueId,
    point: Point,
    input: ValueId,
    input_point: Point,
    kind: ArithmeticKind,
    divisor: i64,
    evidence: SignedDivisionEvidence,
}

impl Equation {
    fn lower(self, input: Reg) -> Expr {
        use crate::model::ir::BinaryOp as B;
        let (op, width, project) = match self.kind {
            ArithmeticKind::SignedDivide64 => (B::SDiv, None, false),
            ArithmeticKind::SignedRemainder64 => (B::SRem, None, false),
            ArithmeticKind::SignedDivide(w) => (B::SDiv, Some(w), true),
            ArithmeticKind::SignedRemainder(w) => (B::SRem, Some(w), true),
            ArithmeticKind::SignedDivideExtended(w) => (B::SDiv, Some(w), false),
            ArithmeticKind::SignedRemainderExtended(w) => (B::SRem, Some(w), false),
        };
        let value = if let Some(w) = width {
            Expr::unary(
                crate::model::ir::UnaryOp::SignExtend(w),
                Expr::Register(input),
            )
        } else {
            Expr::Register(input)
        };
        let result = Expr::binary(op, value, Expr::Const(self.divisor as u64));
        if let Some(w) = width.filter(|_| project) {
            Expr::binary(B::And, result, Expr::Const(w.mask()))
        } else {
            result
        }
    }
}

#[derive(Clone, Debug)]
enum Proof {
    Input(Expr),
    Operation { equation: Equation, input: Reg },
}
#[derive(Clone, Debug)]
struct Capture {
    block: u64,
    value: ValueId,
    point: Point,
    storage: Reg,
    proof: Proof,
}
impl Capture {
    fn expression(&self) -> Expr {
        match &self.proof {
            Proof::Input(expression) => expression.clone(),
            Proof::Operation { equation, input } => equation.lower(*input),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SemanticPlan {
    captures: Vec<Capture>,
    evidence: SemanticEvidence,
}

impl SemanticPlan {
    pub fn analyze(source: &Program) -> Option<Self> {
        let mut work = Work::new();
        value_graph::preflight(source, &mut work)?;
        if !source.uses_operator(crate::model::ir::BinaryOp::SMulHigh) && !word::has_kernel(source)
        {
            return None;
        }
        let graph = ValueGraph::build_with_control(source)?;
        let equations = equations(source, &graph, &mut work)?;
        if equations.is_empty() {
            return None;
        }
        let mut inputs: BTreeMap<(u64, ValueId), Point> = BTreeMap::new();
        for e in &equations {
            inputs
                .entry((e.block, e.input))
                .and_modify(|p| *p = (*p).min(e.input_point))
                .or_insert(e.input_point);
        }
        let mut captures = Vec::new();
        let mut input_registers = BTreeMap::new();
        for ((block, id), point) in inputs {
            let block_values = graph.block(block)?;
            let expression =
                value::snapshot(block_values, id, point, source.register_count(), &mut work)?;
            let storage = fresh(source, &captures)?;
            input_registers.insert((block, id), storage);
            captures.push(Capture {
                block,
                value: id,
                point,
                storage,
                proof: Proof::Input(expression),
            });
        }
        for equation in equations {
            let input = *input_registers.get(&(equation.block, equation.input))?;
            let storage = fresh(source, &captures)?;
            captures.push(Capture {
                block: equation.block,
                value: equation.result,
                point: equation.point,
                storage,
                proof: Proof::Operation { equation, input },
            });
        }
        captures.sort_by_key(|c| {
            (
                c.point,
                usize::from(matches!(c.proof, Proof::Operation { .. })),
                c.storage.0,
            )
        });
        let evidence = counts(&captures);
        let mut plan = Self { captures, evidence };
        let (_, count) = plan.construct(source, &graph, &mut work)?;
        if count == 0 {
            return None;
        }
        plan.evidence.replaced_subtrees = count;
        validate_plan(source, &plan, &graph, &mut work)?;
        Some(plan)
    }

    pub fn evidence(&self) -> SemanticEvidence {
        self.evidence
    }

    pub fn lower(&self, source: &Program) -> Option<Program> {
        let mut work = Work::new();
        value_graph::preflight(source, &mut work)?;
        let graph = ValueGraph::build_with_control(source)?;
        validate_plan(source, self, &graph, &mut work)?;
        let (candidate, count) = self.construct(source, &graph, &mut work)?;
        if count != self.evidence.replaced_subtrees || !validate(source, self, &candidate) {
            return None;
        }
        Some(candidate)
    }

    fn at(&self, point: Point) -> &[Capture] {
        let a = self.captures.partition_point(|c| c.point < point);
        let b = self.captures.partition_point(|c| c.point <= point);
        &self.captures[a..b]
    }

    fn construct(
        &self,
        source: &Program,
        graph: &ValueGraph,
        work: &mut Work,
    ) -> Option<(Program, usize)> {
        let mut instructions = Vec::new();
        let mut replaced = 0;
        for original in source.instructions() {
            let block = block_at(source, graph, original.address);
            let mut assignments = Vec::new();
            for (index, a) in original.assignments.iter().enumerate() {
                let point = Point {
                    instruction: original.address,
                    assignment: index,
                };
                for capture in self.at(point) {
                    assignments.push(Assignment {
                        destination: capture.storage.into(),
                        value: capture.expression(),
                    });
                }
                let destination = match &a.destination {
                    Place::Memory { address, width } => Place::Memory {
                        address: value::rewrite(address, block, point, self, work, &mut replaced)?,
                        width: *width,
                    },
                    p => p.clone(),
                };
                assignments.push(Assignment {
                    destination,
                    value: value::rewrite(&a.value, block, point, self, work, &mut replaced)?,
                });
            }
            let point = Point {
                instruction: original.address,
                assignment: original.assignments.len(),
            };
            for capture in self.at(point) {
                assignments.push(Assignment {
                    destination: capture.storage.into(),
                    value: capture.expression(),
                });
            }
            let control = match &original.control {
                Control::Branch { condition, target } => Control::Branch {
                    condition: value::rewrite(condition, block, point, self, work, &mut replaced)?,
                    target: *target,
                },
                Control::Return(e) => {
                    Control::Return(value::rewrite(e, block, point, self, work, &mut replaced)?)
                }
                c => c.clone(),
            };
            instructions.push(IrInstruction {
                address: original.address,
                size: original.size,
                assignments,
                control,
            });
        }
        let count = source.register_count().checked_add(self.captures.len())?;
        let candidate = Program::new(
            source.cfg().block(source.cfg().entry()).start,
            count,
            instructions,
        )
        .ok()?;
        Some((candidate, replaced))
    }
}

fn fresh(source: &Program, captures: &[Capture]) -> Option<Reg> {
    let n = source.register_count().checked_add(captures.len())?;
    (captures.len() < MAX_CAPTURES && n < value_graph::MAX_REGISTERS).then_some(Reg(n))
}

fn counts(captures: &[Capture]) -> SemanticEvidence {
    let mut evidence = SemanticEvidence::default();
    for c in captures {
        match c.proof {
            Proof::Input(_) => evidence.inputs += 1,
            Proof::Operation { equation, .. } => match equation.kind {
                ArithmeticKind::SignedDivide64
                | ArithmeticKind::SignedDivide(_)
                | ArithmeticKind::SignedDivideExtended(_) => evidence.divisions += 1,
                ArithmeticKind::SignedRemainder64
                | ArithmeticKind::SignedRemainder(_)
                | ArithmeticKind::SignedRemainderExtended(_) => evidence.remainders += 1,
            },
        }
    }
    evidence
}

fn equations(source: &Program, graph: &ValueGraph, work: &mut Work) -> Option<Vec<Equation>> {
    let mut equations = signed::collect(graph, work)?;
    equations.extend(word::collect(source, graph, work)?);
    if equations.len() > MAX_CAPTURES {
        return None;
    }
    equations.sort_by_key(|e| (e.block, e.result));
    Some(equations)
}

fn block_at<'a>(source: &Program, graph: &'a ValueGraph, address: u64) -> Option<&'a BlockValues> {
    let index = source
        .instructions()
        .binary_search_by_key(&address, |i| i.address)
        .ok()?;
    let blocks = source.cfg().blocks();
    let position = blocks.partition_point(|b| b.instructions.start <= index);
    let block = blocks.get(position.checked_sub(1)?)?;
    if !block.instructions.contains(&index) {
        return None;
    }
    graph.block(block.start)
}

fn available(block: &BlockValues, capture: &Capture, point: Point) -> bool {
    capture.block == block.start()
        && block
            .order(capture.point)
            .zip(block.order(point))
            .is_some_and(|(a, b)| a <= b)
}

fn validate_plan(
    source: &Program,
    plan: &SemanticPlan,
    graph: &ValueGraph,
    work: &mut Work,
) -> Option<()> {
    if plan.captures.is_empty() || plan.captures.len() > MAX_CAPTURES {
        return None;
    }
    let mut evidence = counts(&plan.captures);
    evidence.replaced_subtrees = plan.evidence.replaced_subtrees;
    if evidence != plan.evidence || evidence.replaced_subtrees == 0 {
        return None;
    }
    let equations = equations(source, graph, work)?;
    work.spend(equations.len().checked_add(plan.captures.len())?)?;
    let equations: BTreeMap<_, _> = equations.iter().map(|e| ((e.block, e.result), e)).collect();
    let by_register: BTreeMap<_, _> = plan.captures.iter().map(|c| (c.storage.0, c)).collect();
    let mut registers = BTreeSet::new();
    let mut previous = None;
    for c in &plan.captures {
        work.spend(1)?;
        let key = (
            c.point,
            usize::from(matches!(c.proof, Proof::Operation { .. })),
            c.storage.0,
        );
        if previous.is_some_and(|p| p >= key) || !registers.insert(c.storage.0) {
            return None;
        }
        previous = Some(key);
        let block = graph.block(c.block)?;
        match &c.proof {
            Proof::Input(e) => {
                if !value_graph::pure(e, work)?
                    || block.value_of(e, c.point, work)? != Some(c.value)
                {
                    return None;
                }
            }
            Proof::Operation { equation, input } => {
                if equations.get(&(equation.block, equation.result)).copied() != Some(equation)
                    || c.block != equation.block
                    || c.point != equation.point
                    || c.value != equation.result
                {
                    return None;
                }
                let captured = by_register.get(&input.0)?;
                if captured.value != equation.input
                    || !matches!(captured.proof, Proof::Input(_))
                    || !available(block, captured, c.point)
                {
                    return None;
                }
            }
        }
    }
    let expected =
        source.register_count()..source.register_count().checked_add(plan.captures.len())?;
    if !registers.into_iter().eq(expected) {
        return None;
    }
    Some(())
}

/// Check source identities and effects independently of the rewrite builder.
pub fn validate(source: &Program, plan: &SemanticPlan, candidate: &Program) -> bool {
    fn check(source: &Program, plan: &SemanticPlan, candidate: &Program) -> Option<()> {
        let mut work = Work::new();
        value_graph::preflight(source, &mut work)?;
        value_graph::preflight(candidate, &mut work)?;
        let graph = ValueGraph::build_with_control(source)?;
        validate_plan(source, plan, &graph, &mut work)?;
        if candidate.register_count() != source.register_count().checked_add(plan.captures.len())?
            || candidate.cfg().block(candidate.cfg().entry()).start
                != source.cfg().block(source.cfg().entry()).start
            || source.instructions().len() != candidate.instructions().len()
        {
            return None;
        }
        let mut replaced = 0;
        for (a, b) in source.instructions().iter().zip(candidate.instructions()) {
            if a.address != b.address || a.size != b.size {
                return None;
            }
            let block = block_at(source, &graph, a.address);
            let mut cursor = 0;
            for (index, assignment) in a.assignments.iter().enumerate() {
                let point = Point {
                    instruction: a.address,
                    assignment: index,
                };
                for c in plan.at(point) {
                    let actual = b.assignments.get(cursor)?;
                    if actual.destination != Place::Register(c.storage)
                        || actual.value != c.expression()
                    {
                        return None;
                    }
                    cursor += 1;
                }
                let actual = b.assignments.get(cursor)?;
                match (&assignment.destination, &actual.destination) {
                    (Place::Register(x), Place::Register(y)) if x == y => {}
                    (
                        Place::Memory {
                            address: x,
                            width: a,
                        },
                        Place::Memory {
                            address: y,
                            width: b,
                        },
                    ) if a == b => {
                        value::verify(x, y, block, point, plan, &mut work, &mut replaced)?
                    }
                    _ => return None,
                }
                value::verify(
                    &assignment.value,
                    &actual.value,
                    block,
                    point,
                    plan,
                    &mut work,
                    &mut replaced,
                )?;
                cursor += 1;
            }
            let point = Point {
                instruction: a.address,
                assignment: a.assignments.len(),
            };
            for c in plan.at(point) {
                let actual = b.assignments.get(cursor)?;
                if actual.destination != Place::Register(c.storage)
                    || actual.value != c.expression()
                {
                    return None;
                }
                cursor += 1;
            }
            if cursor != b.assignments.len() {
                return None;
            }
            match (&a.control, &b.control) {
                (
                    Control::Branch {
                        condition: x,
                        target: a,
                    },
                    Control::Branch {
                        condition: y,
                        target: b,
                    },
                ) if a == b => value::verify(x, y, block, point, plan, &mut work, &mut replaced)?,
                (Control::Return(x), Control::Return(y)) => {
                    value::verify(x, y, block, point, plan, &mut work, &mut replaced)?
                }
                (x, y) if x == y => {}
                _ => return None,
            }
        }
        (replaced == plan.evidence.replaced_subtrees).then_some(())
    }
    check(source, plan, candidate).is_some()
}
