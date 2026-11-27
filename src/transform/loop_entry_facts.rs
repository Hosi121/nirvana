//! Bounded, advisory entry predicates for modular lane loops.
//!
//! Source SSA suggests an index, trip bound and mask. Neither interval analysis
//! nor syntax matching establishes a fact: the source induction checker must
//! prove every proposed predicate before a recovery may use it.
use super::rolled_loop::Proposal;
use crate::dataflow::{
    lane_patterns::{Discovery, PatternExpr},
    ssa::{Definition, RegisterValue, Site, ValueId},
};
use crate::model::ir::{Assignment, BinaryOp, Control, Expr, Reg, UnaryOp};
use crate::verification::block_verify::region::invariants::{Error, Problem};
use std::collections::BTreeMap;

#[cfg(test)]
mod tests;

/// Propose one predicate for a unit-step loop bounded by a modular lane mask.
/// Unsupported controls, unknown limits and exhausted searches stay absent.
pub fn propose(base: &Proposal) -> Result<Option<Problem>, Error> {
    let discovery = base.discovery();
    let mut indices = Vec::new();
    modular_indices(&base.lane_group().load_address, &mut indices, 0);
    for (value, mask) in indices {
        let Some(Definition::Phi {
            block, register, ..
        }) = discovery.ssa().values.get(value.0)
        else {
            continue;
        };
        if *block != base.envelope().header {
            continue;
        }
        let Some(limit) = latch_limit(base, value) else {
            continue;
        };
        if limit == *register {
            continue;
        }
        let latch = latch_site(base).expect("latch_limit checked the site");
        let Some(limit_value) = discovery.read_identity(latch, limit) else {
            continue;
        };
        let mut bounds = Bounds {
            discovery,
            source: base.source(),
            remaining: 512,
            cache: BTreeMap::new(),
        };
        let Some((low, high)) = bounds.value(limit_value, 0) else {
            continue;
        };
        if high == 0 || high > mask + 1 {
            continue;
        }
        let low = low.max(1);
        let r = Expr::Register;
        let c = Expr::Const;
        let b = Expr::binary;
        let clamp_low = Expr::select(b(BinaryOp::Ult, r(limit), c(low)), c(low), r(limit));
        let normalizers = [
            Assignment {
                destination: limit.into(),
                value: Expr::select(
                    b(BinaryOp::Ult, c(high), clamp_low.clone()),
                    c(high),
                    clamp_low,
                ),
            },
            Assignment {
                destination: (*register).into(),
                value: Expr::select(
                    b(BinaryOp::Ult, r(*register), r(limit)),
                    r(*register),
                    b(BinaryOp::Sub, r(limit), c(1)),
                ),
            },
            Assignment {
                destination: (*register).into(),
                value: b(BinaryOp::And, r(*register), c(mask)),
            },
        ];
        return Problem::new(base.source(), *block, &normalizers).map(Some);
    }
    Ok(None)
}

fn modular_indices(e: &PatternExpr, found: &mut Vec<(ValueId, u64)>, depth: usize) {
    if depth >= 32 || found.len() >= 16 {
        return;
    }
    if let PatternExpr::Binary(BinaryOp::And, a, z) = e {
        for (masked, constant) in [(a, z), (z, a)] {
            let PatternExpr::Constant(mask) = **constant else {
                continue;
            };
            if mask == 0 || mask == u64::MAX || !(mask + 1).is_power_of_two() {
                continue;
            }
            if let PatternExpr::Binary(BinaryOp::Add, left, right) = &**masked {
                for (index, lane) in [(left, right), (right, left)] {
                    if let (PatternExpr::Value(value), PatternExpr::Lane) = (&**index, &**lane) {
                        found.push((*value, mask));
                    }
                }
            }
        }
    }
    match e {
        PatternExpr::Unary(_, x) => modular_indices(x, found, depth + 1),
        PatternExpr::Binary(_, a, z) => {
            modular_indices(a, found, depth + 1);
            modular_indices(z, found, depth + 1);
        }
        PatternExpr::Select(c, a, z) => {
            modular_indices(c, found, depth + 1);
            modular_indices(a, found, depth + 1);
            modular_indices(z, found, depth + 1);
        }
        _ => {}
    }
}
fn latch_site(base: &Proposal) -> Option<Site> {
    let block = base.source().cfg().block_at(base.envelope().latch)?;
    let range = &base.source().cfg().block(block).instructions;
    Some(Site {
        instruction: base
            .source()
            .instructions()
            .get(range.end.checked_sub(1)?)?
            .address,
        assignment: None,
    })
}
fn latch_limit(base: &Proposal, index: ValueId) -> Option<Reg> {
    let site = latch_site(base)?;
    let ins = base
        .source()
        .instructions()
        .iter()
        .find(|i| i.address == site.instruction)?;
    let Control::Branch {
        condition: Expr::Binary(BinaryOp::Ne, a, z),
        target,
    } = &ins.control
    else {
        return None;
    };
    if *target != base.envelope().header {
        return None;
    }
    let (Expr::Register(a), Expr::Register(z)) = (&**a, &**z) else {
        return None;
    };
    for (&next, &limit) in [(a, z), (z, a)] {
        let Some(mut e) = base.discovery().register_expression(site, next) else {
            continue;
        };
        if let PatternExpr::Unary(UnaryOp::Extract { start: 0, .. }, inner) = e {
            e = *inner;
        }
        if let PatternExpr::Binary(BinaryOp::Add, left, right) = e {
            for (a, z) in [(&*left, &*right), (&*right, &*left)] {
                if matches!((a,z),(PatternExpr::Value(v),PatternExpr::Constant(1)) if *v==index) {
                    return Some(limit);
                }
            }
        }
    }
    None
}

type Interval = (u64, u64);
struct Bounds<'a> {
    discovery: &'a Discovery,
    source: &'a crate::model::ir::Program,
    remaining: usize,
    cache: BTreeMap<ValueId, Interval>,
}
impl Bounds<'_> {
    fn value(&mut self, value: ValueId, depth: usize) -> Option<Interval> {
        self.remaining = self.remaining.checked_sub(1)?;
        if depth >= 32 {
            return None;
        }
        let value = self.discovery.value_identity(value)?;
        if let Some(&range) = self.cache.get(&value) {
            return Some(range);
        }
        let range = match self.discovery.ssa().values.get(value.0)? {
            Definition::Initial { .. } | Definition::Phi { .. } => (0, u64::MAX),
            Definition::Assignment { site, .. } => {
                let assignment = self
                    .source
                    .instructions()
                    .iter()
                    .find(|i| i.address == site.instruction)?
                    .assignments
                    .get(site.assignment?)?;
                let reads = &self.discovery.ssa().point(*site)?.reads;
                let mut cursor = 0;
                let range = self.expr(&assignment.value, reads, &mut cursor, depth + 1)?;
                if cursor != reads.len() {
                    return None;
                }
                range
            }
        };
        self.cache.insert(value, range);
        Some(range)
    }
    fn expr(
        &mut self,
        e: &Expr,
        reads: &[RegisterValue],
        cursor: &mut usize,
        depth: usize,
    ) -> Option<Interval> {
        self.remaining = self.remaining.checked_sub(1)?;
        if depth >= 32 {
            return None;
        }
        Some(match e {
            Expr::Const(n) => (*n, *n),
            Expr::Register(r) => {
                let read = reads.get(*cursor)?;
                *cursor += 1;
                if read.register != *r {
                    return None;
                }
                self.value(read.value, depth + 1)?
            }
            Expr::Load { address, width } => {
                self.expr(address, reads, cursor, depth + 1)?;
                (0, width.mask())
            }
            Expr::Unary(op, x) => {
                let (lo, hi) = self.expr(x, reads, cursor, depth + 1)?;
                match op {
                    UnaryOp::Extract { start: 0, width } if hi <= width.mask() => (lo, hi),
                    UnaryOp::Extract { width, .. } => (0, width.mask()),
                    _ => (0, u64::MAX),
                }
            }
            Expr::Binary(op, a, z) => {
                let a = self.expr(a, reads, cursor, depth + 1)?;
                let z = self.expr(z, reads, cursor, depth + 1)?;
                match op {
                    BinaryOp::And => (0, a.1.min(z.1)),
                    BinaryOp::Add => match (a.0.checked_add(z.0), a.1.checked_add(z.1)) {
                        (Some(lo), Some(hi)) => (lo, hi),
                        _ => (0, u64::MAX),
                    },
                    BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule => (0, 1),
                    _ => (0, u64::MAX),
                }
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                self.expr(condition, reads, cursor, depth + 1)?;
                let a = self.expr(taken, reads, cursor, depth + 1)?;
                let z = self.expr(not_taken, reads, cursor, depth + 1)?;
                (a.0.min(z.0), a.1.max(z.1))
            }
        })
    }
}
