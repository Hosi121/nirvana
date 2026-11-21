//! Point-bound remainder views for a materialized, certified quotient.
//!
//! Facts are fresh for each basic block. This never rewrites IR, propagates a
//! load, or equates C storage names. All queries are assignment-RHS-only and
//! must pass the exact selected display Program and a structurally equal RHS.
use crate::model::ir::{Assignment, BinaryOp, Control, Expr, Place, Program, Reg};
use crate::{
    transform::add_division_expr, transform::division_expr, transform::narrow_division_expr,
};
use std::collections::{BTreeMap, BTreeSet};

const MAX_REGISTERS: usize = 4096;
const MAX_INSTRUCTIONS: usize = 16384;
const MAX_ASSIGNMENTS: usize = 16384;
const MAX_NODES: usize = 65536;
const MAX_DEPTH: usize = 128;
const MAX_FACTS: usize = 4096;
const MAX_DEPENDENCIES: usize = 65536;
const MAX_CANDIDATES: usize = 4096;
const MAX_WORK: usize = 2_000_000;

/// Quotient proof kinds understood by this point-aware context pass.
/// This does not extend the raw, inlined remainder expression matcher.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ContextQuotientEvidence {
    High(division_expr::DivisionEvidence),
    Narrow(narrow_division_expr::NarrowDivisionEvidence),
    Add(add_division_expr::AddDivisionEvidence),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Keeper {
    pub instruction: u64,
    pub assignment: usize,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ContextEvidence {
    pub block_start: u64,
    pub instruction: u64,
    pub assignment: usize,
    pub definition_instruction: u64,
    pub definition_assignment: usize,
    pub quotient: Reg,
    pub divisor: u64,
    /// Numeric interval bound, not a possible-one bitmask.
    pub maximum_remainder: u64,
    pub certificate: ContextQuotientEvidence,
    /// Exact preceding Store RHS Register(q), in the same definition generation.
    pub keeper: Keeper,
}
#[derive(Clone, Copy, Debug)]
pub struct ContextView<'a> {
    pub value: &'a Expr,
    pub divisor: u64,
    pub maximum_remainder: u64,
    pub quotient: Reg,
}
#[derive(Clone, Debug)]
pub struct ContextRemainders {
    evidence: Vec<ContextEvidence>,
}

struct Work(usize);
impl Work {
    fn spend(&mut self, n: usize) -> Option<()> {
        self.0 = self.0.checked_sub(n)?;
        Some(())
    }
}
struct Fact<'a> {
    point: (u64, usize),
    value: &'a Expr,
    divisor: u64,
    maximum: u64,
    certificate: ContextQuotientEvidence,
    dependencies: BTreeSet<usize>,
    keeper: Option<Keeper>,
}

impl ContextRemainders {
    pub fn analyze(program: &Program) -> Option<Self> {
        let mut work = Work(MAX_WORK);
        preflight(program, &mut work)?;
        let mut evidence = Vec::new();
        for id in program.cfg().reachable_blocks() {
            let block = program.cfg().block(id);
            let mut facts: BTreeMap<usize, Fact<'_>> = BTreeMap::new();
            let mut members = 0usize;
            for instruction in &program.instructions()[block.instructions.clone()] {
                for (index, assignment) in instruction.assignments.iter().enumerate() {
                    work.spend(1)?;
                    if matches!(assignment.destination, Place::Memory { .. })
                        && let Expr::Register(q) = assignment.value
                        && let Some(fact) = facts.get_mut(&q.0)
                    {
                        fact.keeper = Some(Keeper {
                            instruction: instruction.address,
                            assignment: index,
                        });
                    }
                    if let Some((value, quotient, divisor)) = use_shape(&assignment.value)
                        && let Some(fact) = facts.get(&quotient.0)
                        && let Some(keeper) = fact.keeper
                        && divisor == fact.divisor
                        && same(value, fact.value, &mut work)?
                    {
                        let proof = ContextEvidence {
                            block_start: block.start,
                            instruction: instruction.address,
                            assignment: index,
                            definition_instruction: fact.point.0,
                            definition_assignment: fact.point.1,
                            quotient,
                            divisor,
                            maximum_remainder: fact.maximum.min(divisor - 1),
                            certificate: fact.certificate,
                            keeper,
                        };
                        validate_inner(program, &proof, &mut work)?;
                        evidence.push(proof);
                        if evidence.len() > MAX_CANDIDATES {
                            return None;
                        }
                    }
                    if let Place::Register(destination) = assignment.destination {
                        work.spend(facts.len())?;
                        facts.retain(|&q, f| {
                            let keep =
                                q != destination.0 && !f.dependencies.contains(&destination.0);
                            if !keep {
                                members -= f.dependencies.len();
                            }
                            keep
                        });
                        let count = expression_nodes(&assignment.value, &mut work)?;
                        work.spend(count.checked_mul(4)?.checked_add(256)?)?;
                        if add_division_expr::has_kernel_shape(&assignment.value) {
                            // Account for the extra bounded reciprocal-add
                            // matcher/validator passes, without changing the
                            // existing High/Narrow-only resource fallback.
                            work.spend(count.checked_mul(4)?.checked_add(256)?)?;
                        }
                        if let Some((value, divisor, maximum, certificate)) =
                            definition(&assignment.value)
                        {
                            let dependencies = registers(value, &mut work)?;
                            // RHS uses the old destination. That value is no
                            // longer denoted by its raw register after this write.
                            if dependencies.contains(&destination.0) {
                                continue;
                            }
                            members = members.checked_add(dependencies.len())?;
                            if members > MAX_DEPENDENCIES || facts.len() >= MAX_FACTS {
                                return None;
                            }
                            facts.insert(
                                destination.0,
                                Fact {
                                    point: (instruction.address, index),
                                    value,
                                    divisor,
                                    maximum,
                                    certificate,
                                    dependencies,
                                    keeper: None,
                                },
                            );
                        }
                    }
                }
            }
        }
        evidence.sort_by_key(|p| (p.instruction, p.assignment));
        Some(Self { evidence })
    }
    pub fn evidence(&self) -> &[ContextEvidence] {
        &self.evidence
    }
    /// Call only for the whole source assignment RHS, before compound-update
    /// extraction. Revalidate actual Program provenance, then bind its clone.
    pub fn view<'a>(
        &self,
        program: &'a Program,
        instruction: u64,
        assignment: usize,
        rendered: &Expr,
    ) -> Option<ContextView<'a>> {
        let proof = &self.evidence[self
            .evidence
            .binary_search_by_key(&(instruction, assignment), |p| {
                (p.instruction, p.assignment)
            })
            .ok()?];
        let mut work = Work(MAX_WORK);
        preflight(program, &mut work)?;
        let value = validate_inner(program, proof, &mut work)?;
        bounded_expression(rendered, program.register_count(), &mut 0, &mut work)?;
        let (_, source) = assignment_at(program, instruction, assignment)?;
        if !same(&source.value, rendered, &mut work)? {
            return None;
        }
        Some(ContextView {
            value,
            divisor: proof.divisor,
            maximum_remainder: proof.maximum_remainder,
            quotient: proof.quotient,
        })
    }
}

/// Independent source/certificate/intervening-write/keeper verification.
pub fn validate(program: &Program, proof: &ContextEvidence) -> bool {
    let mut work = Work(MAX_WORK);
    preflight(program, &mut work).is_some() && validate_inner(program, proof, &mut work).is_some()
}
fn validate_inner<'a>(
    program: &'a Program,
    p: &ContextEvidence,
    work: &mut Work,
) -> Option<&'a Expr> {
    if p.divisor < 2 || p.quotient.0 >= program.register_count() {
        return None;
    }
    let id = program.cfg().block_at(p.block_start)?;
    work.spend(program.cfg().blocks().len())?;
    if !program.cfg().reachable_blocks().contains(&id) {
        return None;
    }
    let block = program.cfg().block(id);
    let (di, def) = assignment_at(program, p.definition_instruction, p.definition_assignment)?;
    let (ui, use_) = assignment_at(program, p.instruction, p.assignment)?;
    if !block.instructions.contains(&di)
        || !block.instructions.contains(&ui)
        || (di, p.definition_assignment) >= (ui, p.assignment)
    {
        return None;
    }
    if def.destination != Place::Register(p.quotient) {
        return None;
    }
    let (value, q, d) = use_shape(&use_.value)?;
    if q != p.quotient || d != p.divisor {
        return None;
    }
    let (dividend, maximum) = verify_definition(&def.value, p.divisor, p.certificate, work)?;
    let deps = registers(dividend, work)?;
    if deps.contains(&p.quotient.0) || !same(value, dividend, work)? {
        return None;
    }
    if p.maximum_remainder != maximum.min(p.divisor - 1) {
        return None;
    }
    for index in di..=ui {
        work.spend(1)?;
        let ins = &program.instructions()[index];
        let start = if index == di {
            p.definition_assignment + 1
        } else {
            0
        };
        let end = if index == ui {
            p.assignment
        } else {
            ins.assignments.len()
        };
        for a in ins.assignments.get(start..end)? {
            work.spend(1)?;
            if let Place::Register(reg) = a.destination
                && (reg == p.quotient || deps.contains(&reg.0))
            {
                return None;
            }
        }
    }
    // Keep an actual value read in C, rather than a dead assignment, an
    // address view, or a guard which another display pass could erase.
    let (ki, keeper) = assignment_at(program, p.keeper.instruction, p.keeper.assignment)?;
    if !block.instructions.contains(&ki)
        || (ki, p.keeper.assignment) <= (di, p.definition_assignment)
        || (ki, p.keeper.assignment) >= (ui, p.assignment)
    {
        return None;
    }
    if !matches!(keeper.destination, Place::Memory { .. })
        || !matches!(keeper.value,Expr::Register(reg)if reg==p.quotient)
    {
        return None;
    }
    Some(value)
}
fn definition(e: &Expr) -> Option<(&Expr, u64, u64, ContextQuotientEvidence)> {
    if add_division_expr::has_kernel_shape(e) {
        let v = add_division_expr::recognize(e)?;
        return Some((
            v.value,
            v.divisor,
            u64::MAX,
            ContextQuotientEvidence::Add(v.evidence),
        ));
    }
    if let Some(v) = division_expr::recognize(e) {
        Some((
            v.value,
            v.divisor,
            u64::MAX,
            ContextQuotientEvidence::High(v.evidence),
        ))
    } else {
        let v = narrow_division_expr::recognize(e)?;
        Some((
            v.value,
            v.divisor,
            v.evidence.maximum,
            ContextQuotientEvidence::Narrow(v.evidence),
        ))
    }
}
fn verify_definition<'a>(
    e: &'a Expr,
    d: u64,
    certificate: ContextQuotientEvidence,
    work: &mut Work,
) -> Option<(&'a Expr, u64)> {
    if let ContextQuotientEvidence::Add(evidence) = certificate {
        let count = expression_nodes(e, work)?;
        work.spend(count.checked_mul(4)?.checked_add(256)?)?;
        let Expr::Binary(BinaryOp::Shr, average, _) = e else {
            return None;
        };
        let Expr::Binary(BinaryOp::Add, a, b) = &**average else {
            return None;
        };
        // Recover an actual source operand independently of the proposer.
        // The upstream validator binds its pointer, both high products,
        // literal shifts/multiplier, divisor and every certificate field.
        for half in [&**a, &**b] {
            work.spend(1)?;
            let Expr::Binary(BinaryOp::Shr, difference, _) = half else {
                continue;
            };
            let Expr::Binary(BinaryOp::Sub, value, _) = &**difference else {
                continue;
            };
            if add_division_expr::validate(
                e,
                &add_division_expr::AddDivisionView {
                    value,
                    divisor: d,
                    evidence,
                },
            ) {
                return Some((value, u64::MAX));
            }
        }
        return None;
    }
    let product = match (certificate, e) {
        (ContextQuotientEvidence::High(_), Expr::Binary(BinaryOp::Shr, p, _))
        | (ContextQuotientEvidence::Narrow(_), Expr::Binary(BinaryOp::Shr, p, _)) => &**p,
        (ContextQuotientEvidence::High(_), p) => p,
        _ => return None,
    };
    let (a, b, m, maximum) = match (certificate, product) {
        (ContextQuotientEvidence::High(c), Expr::Binary(BinaryOp::UMulHigh, a, b)) => {
            (&**a, &**b, c.multiplier, u64::MAX)
        }
        (ContextQuotientEvidence::Narrow(c), Expr::Binary(BinaryOp::Mul, a, b)) => {
            (&**a, &**b, c.multiplier, c.maximum)
        }
        _ => return None,
    };
    for (value, factor) in [(a, b), (b, a)] {
        work.spend(1)?;
        if !matches!(factor,Expr::Const(x)if *x==m) {
            continue;
        }
        let valid = match certificate {
            ContextQuotientEvidence::High(evidence) => division_expr::validate(
                e,
                &division_expr::DivisionView {
                    value,
                    divisor: d,
                    evidence,
                },
            ),
            ContextQuotientEvidence::Narrow(evidence) => narrow_division_expr::validate(
                e,
                &narrow_division_expr::NarrowDivisionView {
                    value,
                    divisor: d,
                    evidence,
                },
            ),
            ContextQuotientEvidence::Add(_) => return None,
        };
        if valid {
            return Some((value, maximum));
        }
    }
    None
}
fn use_shape(e: &Expr) -> Option<(&Expr, Reg, u64)> {
    let Expr::Binary(BinaryOp::Sub, x, product) = e else {
        return None;
    };
    let (q, d) = if let Some(pair) = direct_product(product) {
        pair
    } else {
        // In modulo-2^64 arithmetic q*c-q == q*(c-1), even if
        // q*c or q<<k wraps. A literal shift scale is 2^k.
        // The quotient certificate then proves q*(c-1)
        // <=X, so the final product/subtraction are ordinary integers.
        let Expr::Binary(BinaryOp::Sub, multiple, subtrahend) = &**product else {
            return None;
        };
        let Expr::Register(other) = &**subtrahend else {
            return None;
        };
        let (q, scale) = direct_product(multiple).or_else(|| shifted_product(multiple))?;
        if q != *other {
            return None;
        }
        (q, scale.checked_sub(1)?)
    };
    (d >= 2).then_some((x, q, d))
}
fn direct_product(e: &Expr) -> Option<(Reg, u64)> {
    let Expr::Binary(BinaryOp::Mul, a, b) = e else {
        return None;
    };
    match (&**a, &**b) {
        (Expr::Register(q), Expr::Const(d)) | (Expr::Const(d), Expr::Register(q)) => Some((*q, *d)),
        _ => None,
    }
}

fn shifted_product(e: &Expr) -> Option<(Reg, u64)> {
    let Expr::Binary(BinaryOp::Shl, value, count) = e else {
        return None;
    };
    let (Expr::Register(q), Expr::Const(shift @ 2..=63)) = (&**value, &**count) else {
        return None;
    };
    Some((*q, 1_u64.checked_shl(*shift as u32)?))
}
fn instruction_at(program: &Program, pc: u64) -> Option<(usize, &crate::model::ir::IrInstruction)> {
    let i = program
        .instructions()
        .binary_search_by_key(&pc, |i| i.address)
        .ok()?;
    Some((i, &program.instructions()[i]))
}
fn assignment_at(program: &Program, pc: u64, a: usize) -> Option<(usize, &Assignment)> {
    let (i, ins) = instruction_at(program, pc)?;
    Some((i, ins.assignments.get(a)?))
}
fn registers(e: &Expr, work: &mut Work) -> Option<BTreeSet<usize>> {
    let mut s = vec![e];
    let mut out = BTreeSet::new();
    while let Some(e) = s.pop() {
        work.spend(1)?;
        match e {
            Expr::Register(r) => {
                out.insert(r.0);
            }
            Expr::Const(_) => {}
            Expr::Binary(_, a, b) => s.extend([&**a, &**b]),
            Expr::Load { address, .. } => s.push(address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => s.extend([&**condition, &**taken, &**not_taken]),
        }
    }
    Some(out)
}
fn expression_nodes(e: &Expr, work: &mut Work) -> Option<usize> {
    let mut n = 0;
    bounded_expression(e, usize::MAX, &mut n, work)?;
    Some(n)
}
fn bounded_expression(e: &Expr, count: usize, nodes: &mut usize, work: &mut Work) -> Option<()> {
    let mut s = vec![(e, 1)];
    while let Some((e, d)) = s.pop() {
        work.spend(1)?;
        *nodes += 1;
        if *nodes > MAX_NODES || d > MAX_DEPTH {
            return None;
        }
        match e {
            Expr::Register(r) if r.0 >= count => return None,
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Binary(_, a, b) => s.extend([(&**a, d + 1), (&**b, d + 1)]),
            Expr::Load { address, .. } => s.push((address, d + 1)),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => s.extend([
                (&**condition, d + 1),
                (&**taken, d + 1),
                (&**not_taken, d + 1),
            ]),
        }
    }
    Some(())
}
fn preflight(p: &Program, w: &mut Work) -> Option<()> {
    if p.register_count() > MAX_REGISTERS || p.instructions().len() > MAX_INSTRUCTIONS {
        return None;
    }
    let mut nodes = 0;
    let mut assigns = 0;
    for i in p.instructions() {
        w.spend(1)?;
        assigns += i.assignments.len();
        if assigns > MAX_ASSIGNMENTS {
            return None;
        }
        for a in &i.assignments {
            if let Place::Register(r) = a.destination
                && r.0 >= p.register_count()
            {
                return None;
            }
            if let Place::Memory { address, .. } = &a.destination {
                bounded_expression(address, p.register_count(), &mut nodes, w)?;
            }
            bounded_expression(&a.value, p.register_count(), &mut nodes, w)?;
        }
        match &i.control {
            Control::Branch { condition, .. } | Control::Return(condition) => {
                bounded_expression(condition, p.register_count(), &mut nodes, w)?
            }
            _ => {}
        }
    }
    Some(())
}
fn same(a: &Expr, b: &Expr, w: &mut Work) -> Option<bool> {
    let mut s = vec![(a, b)];
    while let Some((a, b)) = s.pop() {
        w.spend(1)?;
        match (a, b) {
            (Expr::Const(a), Expr::Const(b)) if a == b => {}
            (Expr::Register(a), Expr::Register(b)) if a == b => {}
            (Expr::Binary(a, al, ar), Expr::Binary(b, bl, br)) if a == b => {
                s.extend([(&**al, &**bl), (&**ar, &**br)])
            }
            (
                Expr::Select {
                    condition: a,
                    taken: at,
                    not_taken: an,
                },
                Expr::Select {
                    condition: b,
                    taken: bt,
                    not_taken: bn,
                },
            ) => s.extend([(&**a, &**b), (&**at, &**bt), (&**an, &**bn)]),
            _ => return Some(false),
        }
    }
    Some(true)
}
