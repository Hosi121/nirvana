//! Signed representation bounds over the existing checked SSA fixed point.
//!
//! A bound W means the full U64 equals sign_extend_W(its low word), at every
//! reachable read and write. Entry values remain arbitrary. These are storage
//! invariants, separate from unsigned widths and original source C types.
use super::{
    ssa::{Definition, SsaFunction},
    ssa_facts::{self, Domain},
};
use crate::model::ir::{BinaryOp as B, Program, Reg, UnaryOp as U, Width};

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

#[derive(Clone, Debug, Default)]
pub struct SignedWidths {
    widths: Vec<Width>,
}
impl SignedWidths {
    pub fn analyze(source: &Program) -> Self {
        Self::checked(source).unwrap_or_default()
    }
    pub fn width(&self, register: Reg) -> Width {
        self.widths.get(register.0).copied().unwrap_or(Width::U64)
    }
    fn checked(source: &Program) -> Option<Self> {
        let graph = SsaFunction::build(source)?;
        let values = ssa_facts::solve::<State>(source, &graph).ok()?;
        ssa_facts::validate_facts(source, &graph, &values).ok()?;
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
                        return None;
                    };
                    observe(register, id);
                }
            }
        }
        Some(Self {
            widths: observed
                .into_iter()
                .map(|w| w.unwrap_or(Width::U64))
                .collect(),
        })
    }
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
}
