//! Source-bound arithmetic facts for a display plan built before allocation.
//!
//! A fact names real sequential definitions, rather than a register spelling at
//! a later use. Immutable block-local value IDs preserve historical numerator,
//! high-product and quotient values through copies and overwrites. No source
//! expression is cloned and no memory read is reconstructed by this analysis.
use crate::division_expr::{self, DivisionEvidence, DivisionView};
use crate::ir::{Assignment, BinaryOp as B, Expr, Place, Program, Reg};
use crate::value_graph::{self, BlockValues, Point, ValueGraph, ValueId, ValueNode, Work};
use std::collections::BTreeMap;

const MAX_FACTS: usize = 4096;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct QuotientFact {
    pub block_start: u64,
    pub point: Point,
    pub high_definition: Point,
    pub quotient: Reg,
    pub high_register: Reg,
    pub divisor: u64,
    pub certificate: DivisionEvidence,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RemainderFact {
    pub block_start: u64,
    pub point: Point,
    pub quotient_definition: Point,
    pub divisor: u64,
}
#[derive(Clone, Debug)]
pub struct ArithmeticFacts {
    quotients: Vec<QuotientFact>,
    remainders: Vec<RemainderFact>,
}
struct Source<'a> {
    point: Point,
    high_definition: Point,
    quotient_register: Reg,
    high_register: Reg,
    quotient: ValueId,
    high: ValueId,
    numerator: ValueId,
    value: &'a Expr,
    multiplier: u64,
    shift: u32,
}
struct Packet {
    fact: QuotientFact,
    quotient: ValueId,
    high: ValueId,
    numerator: ValueId,
}
impl ArithmeticFacts {
    /// Resource exhaustion declines the entire plan, including earlier facts.
    pub fn analyze(program: &Program) -> Option<Self> {
        let mut work = Work::new();
        value_graph::preflight(program, &mut work)?;
        let graph = ValueGraph::build(program)?;
        let mut quotients = Vec::new();
        let mut remainders = Vec::new();
        for block in graph.blocks() {
            let mut packets = Vec::new();
            for rhs in block.points() {
                work.spend(1)?;
                if let Some(packet) = recognize(program, block, rhs.point, &mut work)? {
                    if quotients.len() == MAX_FACTS {
                        return None;
                    }
                    quotients.push(packet.fact);
                    packets.push(packet);
                }
            }
            for rhs in block.points() {
                work.spend(1)?;
                let source = assignment_at(program, rhs.point)?;
                if !matches!(source.value, Expr::Binary(B::Sub, _, _)) {
                    continue;
                }
                if !value_graph::pure(&source.value, &mut work)? {
                    continue;
                }
                let ValueNode::Binary(B::Sub, lhs, product) = block.node(rhs.value)? else {
                    continue;
                };
                for packet in &packets {
                    work.spend(1)?;
                    if lhs != packet.numerator
                        || block.order(packet.fact.point)? >= block.order(rhs.point)?
                    {
                        continue;
                    }
                    if coefficient(block, product, packet, 1, &mut BTreeMap::new(), &mut work)?
                        != Some(packet.fact.divisor)
                    {
                        continue;
                    }
                    if remainders.len() == MAX_FACTS {
                        return None;
                    }
                    remainders.push(RemainderFact {
                        block_start: block.start(),
                        point: rhs.point,
                        quotient_definition: packet.fact.point,
                        divisor: packet.fact.divisor,
                    });
                    break;
                }
            }
        }
        quotients.sort_by_key(|p| p.point);
        remainders.sort_by_key(|p| p.point);
        Some(Self {
            quotients,
            remainders,
        })
    }
    pub fn quotients(&self) -> &[QuotientFact] {
        &self.quotients
    }
    pub fn remainders(&self) -> &[RemainderFact] {
        &self.remainders
    }
}

/// Rebuild source values and recompute the certificate, trusting no fact field.
pub fn validate_quotient(program: &Program, fact: &QuotientFact) -> bool {
    checked_numerator(program, fact).is_some()
}
/// Borrow the actual high-product operand, after independently checking source.
/// The caller must capture it at `high_definition`, never reevaluate it later.
pub fn numerator<'a>(program: &'a Program, fact: &QuotientFact) -> Option<&'a Expr> {
    checked_numerator(program, fact)
}
fn checked_numerator<'a>(program: &'a Program, fact: &QuotientFact) -> Option<&'a Expr> {
    let mut work = Work::new();
    value_graph::preflight(program, &mut work)?;
    let graph = ValueGraph::build(program)?;
    let block = graph.block(fact.block_start)?;
    for source in sources(program, block, fact.point, &mut work)?? {
        if source.high_definition == fact.high_definition
            && source.quotient_register == fact.quotient
            && source.high_register == fact.high_register
            && source.multiplier == fact.certificate.multiplier
            && source.shift == fact.certificate.shift
            && certificate_valid(
                source.multiplier,
                source.shift,
                fact.divisor,
                fact.certificate,
            )
        {
            return Some(source.value);
        }
    }
    None
}

/// Independently rederive the named quotient and validate this whole RHS.
pub fn validate_remainder(program: &Program, fact: &RemainderFact) -> bool {
    verify_remainder(program, fact).is_some()
}
fn verify_remainder(program: &Program, fact: &RemainderFact) -> Option<()> {
    let mut work = Work::new();
    value_graph::preflight(program, &mut work)?;
    let graph = ValueGraph::build(program)?;
    let block = graph.block(fact.block_start)?;
    if block.order(fact.quotient_definition)? >= block.order(fact.point)? {
        return None;
    }
    let source = assignment_at(program, fact.point)?;
    if !value_graph::pure(&source.value, &mut work)? {
        return None;
    }
    if !matches!(source.value, Expr::Binary(B::Sub, _, _)) {
        return None;
    }
    let ValueNode::Binary(B::Sub, lhs, product) = block.node(block.rhs(fact.point)?)? else {
        return None;
    };
    let packet = recognize(program, block, fact.quotient_definition, &mut work)??;
    if packet.fact.divisor != fact.divisor || packet.numerator != lhs {
        return None;
    }
    (coefficient(block, product, &packet, 1, &mut BTreeMap::new(), &mut work)?
        == Some(fact.divisor))
    .then_some(())
}

fn recognize(
    program: &Program,
    block: &BlockValues,
    point: Point,
    work: &mut Work,
) -> Option<Option<Packet>> {
    let Some(sources) = sources(program, block, point, work)? else {
        return Some(None);
    };
    for source in sources {
        // The virtual tree is fixed-size; the original numerator is never
        // cloned. The all-u64 proof holds for any captured numerator value.
        work.spend(32)?;
        let virtual_q = virtual_quotient(source.multiplier, source.shift);
        let Some(view) = division_expr::recognize(&virtual_q) else {
            continue;
        };
        if !certificate_valid(source.multiplier, source.shift, view.divisor, view.evidence) {
            continue;
        }
        return Some(Some(Packet {
            fact: QuotientFact {
                block_start: block.start(),
                point: source.point,
                high_definition: source.high_definition,
                quotient: source.quotient_register,
                high_register: source.high_register,
                divisor: view.divisor,
                certificate: view.evidence,
            },
            quotient: source.quotient,
            high: source.high,
            numerator: source.numerator,
        }));
    }
    Some(None)
}
// The outer Option denotes a resource failure; an unsupported source is an
// ordinary declined candidate. All raw syntax has passed iterative preflight.
fn sources<'a>(
    program: &'a Program,
    block: &BlockValues,
    point: Point,
    work: &mut Work,
) -> Option<Option<Vec<Source<'a>>>> {
    work.spend(1)?;
    let Some(quotient) = block.rhs(point) else {
        return Some(None);
    };
    let Some(source) = assignment_at(program, point) else {
        return Some(None);
    };
    let Place::Register(q) = source.destination else {
        return Some(None);
    };
    let Expr::Binary(B::Shr, high_source, shift_source) = &source.value else {
        return Some(None);
    };
    let (Expr::Register(h), Expr::Const(shift @ 0..=63)) = (&**high_source, &**shift_source) else {
        return Some(None);
    };
    let Some(definition) = block.definition_before(*h, point) else {
        return Some(None);
    };
    let high = definition.value;
    let Some(high_source) = assignment_at(program, definition.point) else {
        return Some(None);
    };
    if high_source.destination != Place::Register(*h) {
        return Some(None);
    }
    let Expr::Binary(B::UMulHigh, left, right) = &high_source.value else {
        return Some(None);
    };
    let Some(ValueNode::Binary(B::UMulHigh, a, b)) = block.node(high) else {
        return Some(None);
    };
    let mut out = Vec::new();
    for (constant, value, numerator) in [(&**left, &**right, b), (&**right, &**left, a)] {
        let Expr::Const(multiplier) = constant else {
            continue;
        };
        if !value_graph::pure(value, work)? {
            continue;
        }
        out.push(Source {
            point,
            high_definition: definition.point,
            quotient_register: q,
            high_register: *h,
            quotient,
            high,
            numerator,
            value,
            multiplier: *multiplier,
            shift: *shift as u32,
        });
    }
    Some(Some(out))
}
fn virtual_quotient(multiplier: u64, shift: u32) -> Expr {
    Expr::binary(
        B::Shr,
        Expr::binary(B::UMulHigh, Expr::Const(multiplier), Expr::Register(Reg(0))),
        Expr::Const(u64::from(shift)),
    )
}
fn certificate_valid(
    multiplier: u64,
    shift: u32,
    divisor: u64,
    evidence: DivisionEvidence,
) -> bool {
    let tree = virtual_quotient(multiplier, shift);
    let Expr::Binary(B::Shr, high, _) = &tree else {
        return false;
    };
    let Expr::Binary(B::UMulHigh, _, value) = &**high else {
        return false;
    };
    division_expr::validate(
        &tree,
        &DivisionView {
            value,
            divisor,
            evidence,
        },
    )
}

/// Every rule is an identity modulo 2^64. Coefficients are checked nonnegative
/// integers; the certified final divisor ensures Q*d <= the captured numerator.
fn coefficient(
    block: &BlockValues,
    id: ValueId,
    packet: &Packet,
    depth: usize,
    memo: &mut BTreeMap<ValueId, Option<u64>>,
    work: &mut Work,
) -> Option<Option<u64>> {
    work.spend(1)?;
    if depth > value_graph::MAX_DEPTH {
        return None;
    }
    if id == packet.quotient {
        return Some(Some(1));
    }
    if let Some(value) = memo.get(&id) {
        return Some(*value);
    }
    let value = match block.node(id)? {
        ValueNode::Constant(0) => Some(0),
        ValueNode::Binary(B::And, a, b) => {
            let mask = u64::MAX << packet.fact.certificate.shift;
            [(a, b), (b, a)]
                .into_iter()
                .any(|(high, constant)| {
                    high == packet.high && block.node(constant) == Some(ValueNode::Constant(mask))
                })
                .then_some(1u64 << packet.fact.certificate.shift)
        }
        ValueNode::Binary(op @ (B::Add | B::Sub), a, b) => {
            match (
                coefficient(block, a, packet, depth + 1, memo, work)?,
                coefficient(block, b, packet, depth + 1, memo, work)?,
            ) {
                (Some(a), Some(b)) if op == B::Add => a.checked_add(b),
                (Some(a), Some(b)) => a.checked_sub(b),
                _ => None,
            }
        }
        ValueNode::Binary(B::Mul, a, b) => {
            let mut value = None;
            for (constant, child) in [(a, b), (b, a)] {
                if let Some(ValueNode::Constant(scale)) = block.node(constant) {
                    value = coefficient(block, child, packet, depth + 1, memo, work)?
                        .and_then(|c| c.checked_mul(scale));
                    break;
                }
            }
            value
        }
        ValueNode::Binary(B::Shl, value, shift) => {
            if let Some(ValueNode::Constant(shift @ 0..=63)) = block.node(shift) {
                coefficient(block, value, packet, depth + 1, memo, work)?
                    .and_then(|c| c.checked_mul(1u64 << shift))
            } else {
                None
            }
        }
        _ => None,
    };
    memo.insert(id, value);
    Some(value)
}
fn assignment_at(program: &Program, point: Point) -> Option<&Assignment> {
    let index = program
        .instructions()
        .binary_search_by_key(&point.instruction, |i| i.address)
        .ok()?;
    program.instructions()[index]
        .assignments
        .get(point.assignment)
}
