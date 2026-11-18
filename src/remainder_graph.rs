//! Point-bound remainder display views through materialized high products.
//!
//! The source IR and every memory operation stay untouched. A certified virtual
//! quotient uses the original subtraction lhs; block-local immutable value IDs
//! connect it to the real high product. Product coefficients are identities in
//! Z/(2^64), and the division certificate proves the final Q*d <= X.
use crate::division_expr::{self, DivisionEvidence, DivisionView};
use crate::ir::{Assignment, BinaryOp as B, Expr, Place, Program, Reg};
use crate::value_graph::{self, BlockValues, Point, ValueGraph, ValueId, ValueNode, Work};
use std::collections::BTreeSet;

const MAX_EVIDENCE: usize = 4096;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Keeper {
    pub instruction: u64,
    pub assignment: usize,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GraphEvidence {
    pub block_start: u64,
    pub instruction: u64,
    pub assignment: usize,
    pub definition_instruction: u64,
    pub definition_assignment: usize,
    pub quotient: Reg,
    pub divisor: u64,
    pub maximum_remainder: u64,
    pub certificate: DivisionEvidence,
    pub keeper: Keeper,
}
#[derive(Clone, Copy, Debug)]
pub struct GraphView<'a> {
    pub value: &'a Expr,
    pub divisor: u64,
    pub maximum_remainder: u64,
    pub quotient: Reg,
}
#[derive(Clone, Debug)]
pub struct GraphRemainders {
    evidence: Vec<GraphEvidence>,
}
struct Packet {
    definition: Point,
    quotient: ValueId,
    high: ValueId,
    high_register: Reg,
    numerator: ValueId,
    multiplier: u64,
    shift: u32,
}
impl GraphRemainders {
    pub fn analyze(program: &Program) -> Option<Self> {
        let graph = ValueGraph::build(program)?;
        let mut work = Work::new();
        let mut evidence = Vec::new();
        for block in graph.blocks() {
            for rhs in block.points() {
                work.spend(1)?;
                let source = assignment_at(program, rhs.point)?;
                let Expr::Binary(B::Sub, lhs, product) = &source.value else {
                    continue;
                };
                if !value_graph::pure(&source.value, &mut work)? {
                    continue;
                }
                let ValueNode::Binary(B::Sub, numerator, product_id) = block.node(rhs.value)?
                else {
                    continue;
                };
                for q in raw_registers(product, &mut work)? {
                    let Some(packet) = packet(program, block, rhs.point, q) else {
                        continue;
                    };
                    if packet.numerator != numerator
                        || !preserved_product_reads(
                            block, rhs.point, product, q, &packet, &mut work,
                        )?
                    {
                        continue;
                    }
                    let Some(coefficient) = coefficient(block, product_id, &packet, 1, &mut work)?
                    else {
                        continue;
                    };
                    if coefficient < 2 {
                        continue;
                    }
                    let virtual_q = virtual_quotient(lhs, packet.multiplier, packet.shift);
                    work.spend(4 * division_expr::MAX_NODES + 512)?;
                    let Some(view) = division_expr::recognize(&virtual_q) else {
                        continue;
                    };
                    if view.divisor != coefficient {
                        continue;
                    }
                    let Some(keeper) =
                        find_keeper(program, block, packet.definition, rhs.point, q, &mut work)?
                    else {
                        continue;
                    };
                    let proof = GraphEvidence {
                        block_start: block.start(),
                        instruction: rhs.point.instruction,
                        assignment: rhs.point.assignment,
                        definition_instruction: packet.definition.instruction,
                        definition_assignment: packet.definition.assignment,
                        quotient: q,
                        divisor: coefficient,
                        maximum_remainder: coefficient - 1,
                        certificate: view.evidence,
                        keeper,
                    };
                    // This check reparses actual source and certificate; it does
                    // not trust candidate values or virtual-tree pointer identity.
                    verify_with_graph(program, &graph, &proof, &mut work)?;
                    evidence.push(proof);
                    if evidence.len() > MAX_EVIDENCE {
                        return None;
                    }
                    break;
                }
            }
        }
        evidence.sort_by_key(|p| (p.instruction, p.assignment));
        Some(Self { evidence })
    }
    pub fn evidence(&self) -> &[GraphEvidence] {
        &self.evidence
    }
    /// Only the whole assignment RHS, before compound-update extraction.
    pub fn view<'a>(
        &self,
        program: &'a Program,
        instruction: u64,
        assignment: usize,
        rendered: &Expr,
    ) -> Option<GraphView<'a>> {
        let proof = &self.evidence[self
            .evidence
            .binary_search_by_key(&(instruction, assignment), |p| {
                (p.instruction, p.assignment)
            })
            .ok()?];
        let graph = ValueGraph::build(program)?;
        let mut work = Work::new();
        // Bound this possibly unrelated clone before structural comparison.
        if !value_graph::pure(rendered, &mut work)? {
            return None;
        }
        let source = assignment_at(
            program,
            Point {
                instruction,
                assignment,
            },
        )?;
        let lhs = verify_with_graph(program, &graph, proof, &mut work)?;
        if source.value != *rendered {
            return None;
        }
        Some(GraphView {
            value: lhs,
            divisor: proof.divisor,
            maximum_remainder: proof.maximum_remainder,
            quotient: proof.quotient,
        })
    }
}
/// Rebuild actual source value numbers and independently check all evidence.
pub fn validate(program: &Program, proof: &GraphEvidence) -> bool {
    let Some(graph) = ValueGraph::build(program) else {
        return false;
    };
    verify_with_graph(program, &graph, proof, &mut Work::new()).is_some()
}
fn verify_with_graph<'a>(
    program: &'a Program,
    graph: &ValueGraph,
    p: &GraphEvidence,
    work: &mut Work,
) -> Option<&'a Expr> {
    work.spend(1)?;
    if p.divisor < 2 || p.maximum_remainder != p.divisor - 1 {
        return None;
    }
    let block = graph.block(p.block_start)?;
    let point = Point {
        instruction: p.instruction,
        assignment: p.assignment,
    };
    let source = assignment_at(program, point)?;
    if !value_graph::pure(&source.value, work)? {
        return None;
    }
    let Expr::Binary(B::Sub, lhs, product) = &source.value else {
        return None;
    };
    let ValueNode::Binary(B::Sub, lhs_id, product_id) = block.node(block.rhs(point)?)? else {
        return None;
    };
    if !raw_registers(product, work)?.contains(&p.quotient) {
        return None;
    }
    let packet = packet(program, block, point, p.quotient)?;
    if packet.definition
        != (Point {
            instruction: p.definition_instruction,
            assignment: p.definition_assignment,
        })
        || packet.numerator != lhs_id
        || packet.multiplier != p.certificate.multiplier
        || packet.shift != p.certificate.shift
        || !preserved_product_reads(block, point, product, p.quotient, &packet, work)?
    {
        return None;
    }
    if coefficient(block, product_id, &packet, 1, work)?? != p.divisor {
        return None;
    }
    let keeper_point = Point {
        instruction: p.keeper.instruction,
        assignment: p.keeper.assignment,
    };
    if !(block.order(packet.definition)? < block.order(keeper_point)?
        && block.order(keeper_point)? < block.order(point)?)
    {
        return None;
    }
    let keeper = assignment_at(program, keeper_point)?;
    if !matches!(keeper.destination, Place::Memory { .. })
        || keeper.value != Expr::Register(p.quotient)
        || block.definition_before(p.quotient, keeper_point)?.point != packet.definition
    {
        return None;
    }
    let virtual_q = virtual_quotient(lhs, packet.multiplier, packet.shift);
    let Expr::Binary(B::Shr, high, _) = &virtual_q else {
        return None;
    };
    let Expr::Binary(B::UMulHigh, _, value) = &**high else {
        return None;
    };
    work.spend(4 * division_expr::MAX_NODES + 512)?;
    if !division_expr::validate(
        &virtual_q,
        &DivisionView {
            value,
            divisor: p.divisor,
            evidence: p.certificate,
        },
    ) {
        return None;
    }
    Some(lhs)
}
fn packet(program: &Program, block: &BlockValues, point: Point, q: Reg) -> Option<Packet> {
    let definition = block.definition_before(q, point)?;
    let qvalue = block.value_before(q, point)?;
    let ValueNode::Binary(B::Shr, high, shift_id) = block.node(qvalue)? else {
        return None;
    };
    let ValueNode::Constant(shift @ 0..=63) = block.node(shift_id)? else {
        return None;
    };
    // Restrict the new path to an actual materialized-high/shift packet. This
    // preserves a real read of H in the original Q computation.
    let source = assignment_at(program, definition.point)?;
    let Expr::Binary(B::Shr, high_source, shift_source) = &source.value else {
        return None;
    };
    let (Expr::Register(h), Expr::Const(s)) = (&**high_source, &**shift_source) else {
        return None;
    };
    if *s != shift || block.value_before(*h, definition.point)? != high {
        return None;
    }
    let ValueNode::Binary(B::UMulHigh, a, b) = block.node(high)? else {
        return None;
    };
    for (constant, numerator) in [(a, b), (b, a)] {
        if let Some(ValueNode::Constant(multiplier)) = block.node(constant) {
            return Some(Packet {
                definition: definition.point,
                quotient: qvalue,
                high,
                high_register: *h,
                numerator,
                multiplier,
                shift: shift as u32,
            });
        }
    }
    None
}
/// Normalize to a nonnegative checked coefficient of Q. Every accepted rule
/// holds modulo 2^64; only the certified final coefficient becomes an integer
/// product. Unsupported and oversized expressions decline conservatively.
fn coefficient(
    block: &BlockValues,
    id: ValueId,
    packet: &Packet,
    depth: usize,
    work: &mut Work,
) -> Option<Option<u64>> {
    work.spend(1)?;
    if depth > value_graph::MAX_DEPTH {
        return None;
    }
    if id == packet.quotient {
        return Some(Some(1));
    }
    let value = match block.node(id)? {
        ValueNode::Constant(0) => Some(0),
        ValueNode::Binary(B::And, a, b) => {
            let mask = u64::MAX.checked_shl(packet.shift)?;
            if [(a, b), (b, a)].into_iter().any(|(high, constant)| {
                high == packet.high && block.node(constant) == Some(ValueNode::Constant(mask))
            }) {
                Some(1u64.checked_shl(packet.shift)?)
            } else {
                None
            }
        }
        ValueNode::Binary(op @ (B::Add | B::Sub), a, b) => {
            match (
                coefficient(block, a, packet, depth + 1, work)?,
                coefficient(block, b, packet, depth + 1, work)?,
            ) {
                (Some(a), Some(b)) => {
                    if op == B::Add {
                        a.checked_add(b)
                    } else {
                        a.checked_sub(b)
                    }
                }
                _ => None,
            }
        }
        ValueNode::Binary(B::Mul, a, b) => {
            let mut result = None;
            for (constant, value) in [(a, b), (b, a)] {
                if let Some(ValueNode::Constant(scale)) = block.node(constant) {
                    result = coefficient(block, value, packet, depth + 1, work)?
                        .and_then(|n| n.checked_mul(scale));
                    break;
                }
            }
            result
        }
        ValueNode::Binary(B::Shl, value, shift) => {
            if let Some(ValueNode::Constant(shift @ 0..=63)) = block.node(shift) {
                coefficient(block, value, packet, depth + 1, work)?
                    .and_then(|n| n.checked_mul(1u64 << shift))
            } else {
                None
            }
        }
        _ => None,
    };
    Some(value)
}
fn find_keeper(
    program: &Program,
    block: &BlockValues,
    definition: Point,
    use_: Point,
    q: Reg,
    work: &mut Work,
) -> Option<Option<Keeper>> {
    let mut found = None;
    for rhs in &block.points()[block.order(definition)? + 1..block.order(use_)?] {
        work.spend(1)?;
        let source = assignment_at(program, rhs.point)?;
        if matches!(source.destination, Place::Memory { .. }) && source.value == Expr::Register(q) {
            found = Some(Keeper {
                instruction: rhs.point.instruction,
                assignment: rhs.point.assignment,
            });
        }
    }
    Some(found)
}
fn raw_registers(e: &Expr, work: &mut Work) -> Option<Vec<Reg>> {
    // Reg intentionally has no ordering contract. Collect numeric raw IDs.
    let mut ids = BTreeSet::new();
    let mut pending = vec![e];
    while let Some(e) = pending.pop() {
        work.spend(1)?;
        match e {
            Expr::Register(r) => {
                ids.insert(r.0);
            }
            Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            _ => {}
        }
    }
    Some(ids.into_iter().map(Reg).collect())
}
// Removing the product must not orphan a materialized intermediate. Q has
// its exact Store keeper. The only other allowed raw register is the actual H
// register read by Q, still denoting that same immutable high value at this use.
fn preserved_product_reads(
    block: &BlockValues,
    point: Point,
    product: &Expr,
    q: Reg,
    packet: &Packet,
    work: &mut Work,
) -> Option<bool> {
    for reg in raw_registers(product, work)? {
        if reg != q
            && (reg != packet.high_register || block.value_before(reg, point) != Some(packet.high))
        {
            return Some(false);
        }
    }
    Some(true)
}
fn virtual_quotient(lhs: &Expr, multiplier: u64, shift: u32) -> Expr {
    Expr::binary(
        B::Shr,
        Expr::binary(B::UMulHigh, Expr::Const(multiplier), lhs.clone()),
        Expr::Const(u64::from(shift)),
    )
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
