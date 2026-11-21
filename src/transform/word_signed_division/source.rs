//! Typed source adapters keep expression references and immutable value IDs
//! distinct. A captured load is an opaque graph atom, never an expression to
//! execute again. Availability is checked by the semantic consumer.
use super::*;
use crate::dataflow::value_graph::{BlockValues, ValueId, ValueNode};
use std::{collections::BTreeMap, marker::PhantomData};

pub(super) enum Node<K> {
    Constant(u64),
    Unary(U, K),
    Binary(B, K, K),
    Other,
}
pub(super) trait Source {
    type Key: Copy;
    fn node(&self, key: Self::Key) -> Option<Node<Self::Key>>;
    fn pure(&self, key: Self::Key, work: &mut Work) -> Option<()>;
    fn same(&self, a: Self::Key, b: Self::Key, work: &mut Work) -> Option<bool>;
    fn identical(&self, a: Self::Key, b: Self::Key) -> bool;
}
pub(super) struct Raw<'a>(PhantomData<&'a Expr>);
impl<'a> Raw<'a> {
    pub fn new(_: &'a Expr) -> Self {
        Self(PhantomData)
    }
}
impl<'a> Source for Raw<'a> {
    type Key = &'a Expr;
    fn node(&self, e: Self::Key) -> Option<Node<Self::Key>> {
        Some(match e {
            Expr::Const(n) => Node::Constant(*n),
            Expr::Unary(op, v) => Node::Unary(*op, v),
            Expr::Binary(op, a, b) => Node::Binary(*op, a, b),
            _ => Node::Other,
        })
    }
    fn pure(&self, e: Self::Key, work: &mut Work) -> Option<()> {
        work.pure(e)
    }
    fn same(&self, a: Self::Key, b: Self::Key, work: &mut Work) -> Option<bool> {
        work.same(a, b)
    }
    fn identical(&self, a: Self::Key, b: Self::Key) -> bool {
        std::ptr::eq(a, b)
    }
}
pub(super) struct Graph<'a>(pub(super) &'a BlockValues);
impl Source for Graph<'_> {
    type Key = ValueId;
    fn node(&self, id: ValueId) -> Option<Node<ValueId>> {
        Some(match self.0.node(id)? {
            ValueNode::Constant(n) => Node::Constant(n),
            ValueNode::Unary(op, v) => Node::Unary(op, v),
            ValueNode::Binary(op, a, b) => Node::Binary(op, a, b),
            _ => Node::Other,
        })
    }
    fn pure(&self, id: ValueId, work: &mut Work) -> Option<()> {
        let mut pending = vec![(id, 1usize)];
        let mut visited = BTreeMap::new();
        let mut nodes = 0;
        while let Some((id, depth)) = pending.pop() {
            work.spend()?;
            if depth > MAX_DEPTH {
                return None;
            }
            if visited.get(&id).is_some_and(|old| *old >= depth) {
                continue;
            }
            visited.insert(id, depth);
            nodes += 1;
            if nodes > MAX_NODES {
                return None;
            }
            match self.0.node(id)? {
                ValueNode::Unary(_, v) => pending.push((v, depth + 1)),
                ValueNode::Binary(_, a, b) => pending.extend([(a, depth + 1), (b, depth + 1)]),
                ValueNode::Select(c, t, n) => {
                    pending.extend([(c, depth + 1), (t, depth + 1), (n, depth + 1)])
                }
                // Every load occurrence already has a unique immutable ID.
                ValueNode::Initial(_) | ValueNode::Constant(_) | ValueNode::CapturedLoad(_) => {}
            }
        }
        Some(())
    }
    fn same(&self, a: ValueId, b: ValueId, work: &mut Work) -> Option<bool> {
        work.spend()?;
        Some(a == b)
    }
    fn identical(&self, a: ValueId, b: ValueId) -> bool {
        a == b
    }
}
