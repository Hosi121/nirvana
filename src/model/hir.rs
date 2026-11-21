//! Explicit named views of checked guest memory.
//!
//! Views describe addresses, not allocations or host pointers. Names carry no
//! aliasing, type, ownership, extent, or bounds guarantees. Lowering uses the
//! existing IR memory operations and wrapping unsigned-64-bit arithmetic.

use crate::model::ir::{Assignment, BinaryOp, Expr, Place, Width};

/// An explicit object, byte-offset field, or strided index in guest memory.
///
/// Base and index expressions may themselves read memory or fault. Lowering
/// preserves them without simplification: an index evaluates its base before
/// its index, even when the stride is zero. Reusing a view constructs a fresh
/// expression; it does not capture register values or cache address evaluation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ViewPath {
    Object {
        name: String,
        base: Expr,
    },
    Field {
        base: Box<ViewPath>,
        offset: u64,
    },
    Index {
        base: Box<ViewPath>,
        index: Expr,
        stride: u64,
    },
}

impl ViewPath {
    /// Lower to an address with byte offsets and products computed modulo 2^64.
    ///
    /// This does not check the address or authorize reordering its evaluation.
    pub fn address(&self) -> Expr {
        match self {
            Self::Object { base, .. } => base.clone(),
            Self::Field { base, offset } => {
                Expr::binary(BinaryOp::Add, base.address(), Expr::Const(*offset))
            }
            Self::Index {
                base,
                index,
                stride,
            } => Expr::binary(
                BinaryOp::Add,
                base.address(),
                Expr::binary(BinaryOp::Mul, index.clone(), Expr::Const(*stride)),
            ),
        }
    }

    /// Lower to a checked little-endian load, with the IR's fault behavior.
    pub fn load(&self, width: Width) -> Expr {
        Expr::load(self.address(), width)
    }

    /// Lower to a checked little-endian store, with the IR's evaluation order.
    ///
    /// The IR evaluates and checks the destination before evaluating `value`.
    pub fn store(&self, width: Width, value: Expr) -> Assignment {
        Assignment {
            destination: Place::Memory {
                address: self.address(),
                width,
            },
            value,
        }
    }
}
