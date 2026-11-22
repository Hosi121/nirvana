//! The proposer normalizes edge predicates. The checker closes raw edge
//! assumptions and evaluates their consequences with a three-valued word domain.
use super::symbolic::Value;
use super::*;
use crate::model::ir::BinaryOp as B;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Facts {
    Unreachable,
    Known(BTreeMap<usize, bool>),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Word {
    Unknown,
    Nonzero,
    Constant(u64),
}
impl Word {
    pub fn truth(self) -> Option<bool> {
        match self {
            Self::Constant(n) => Some(n != 0),
            Self::Nonzero => Some(true),
            _ => None,
        }
    }
}
impl Facts {
    pub fn empty() -> Self {
        Self::Known(BTreeMap::new())
    }
    pub fn len(&self) -> usize {
        match self {
            Self::Known(f) => f.len(),
            _ => 0,
        }
    }
    pub fn intersection(states: &[Self], work: &mut ssa::Budget) -> Result<Self, ssa::SsaError> {
        let mut result = None;
        for state in states {
            work.spend(state.len() + 1)?;
            if let Self::Known(facts) = state {
                if let Some(Self::Known(common)) = &mut result {
                    common.retain(|id, value| facts.get(id) == Some(value));
                } else {
                    result = Some(Self::Known(facts.clone()));
                }
            }
        }
        Ok(result.unwrap_or(Self::Unreachable))
    }
    fn insert(&mut self, id: usize, truth: bool) {
        if let Self::Known(facts) = self
            && facts.insert(id, truth).is_some_and(|old| old != truth)
        {
            *self = Self::Unreachable;
        }
    }
    pub fn edge(
        &self,
        nodes: &[Value],
        condition: Option<(usize, bool)>,
        work: &mut ssa::Budget,
    ) -> Result<Self, ssa::SsaError> {
        let mut result = self.clone();
        if matches!(self, Self::Unreachable) {
            return Ok(result);
        }
        let Some((mut id, mut truth)) = condition else {
            return Ok(result);
        };
        loop {
            work.spend(1)?;
            match nodes[id] {
                Value::Constant(n) => {
                    if (n != 0) != truth {
                        return Ok(Self::Unreachable);
                    }
                    return Ok(result);
                }
                Value::Binary(B::Eq | B::Ne, a, b) => {
                    let next = if nodes[a] == Value::Constant(0) {
                        Some(b)
                    } else if nodes[b] == Value::Constant(0) {
                        Some(a)
                    } else {
                        None
                    };
                    if let Some(next) = next {
                        if matches!(nodes[id], Value::Binary(B::Eq, _, _)) {
                            truth = !truth;
                        }
                        id = next;
                        continue;
                    }
                }
                Value::Binary(B::Xor, a, b) => {
                    let next = if nodes[a] == Value::Constant(1) && nodes[b].is_boolean() {
                        Some(b)
                    } else if nodes[b] == Value::Constant(1) && nodes[a].is_boolean() {
                        Some(a)
                    } else {
                        None
                    };
                    if let Some(next) = next {
                        id = next;
                        truth = !truth;
                        continue;
                    }
                }
                _ => {}
            }
            result.insert(id, truth);
            return Ok(result);
        }
    }
    pub fn evaluate(
        &self,
        nodes: &[Value],
        work: &mut ssa::Budget,
    ) -> Result<Vec<Word>, ssa::SsaError> {
        work.spend(nodes.len())?;
        let known = match self {
            Self::Known(f) => Some(f),
            _ => None,
        };
        let mut result = Vec::<Word>::with_capacity(nodes.len());
        for (id, node) in nodes.iter().enumerate() {
            let value = if let Some(truth) = known.and_then(|f| f.get(&id)) {
                if *truth && node.is_boolean() {
                    Word::Constant(1)
                } else if *truth {
                    Word::Nonzero
                } else {
                    Word::Constant(0)
                }
            } else {
                match *node {
                    Value::Constant(n) => Word::Constant(n),
                    Value::Unary(op, a) => match result[a] {
                        Word::Constant(n) => Word::Constant(op.evaluate(n)),
                        _ => Word::Unknown,
                    },
                    Value::Binary(op, a, b) => match (result[a], result[b]) {
                        (Word::Constant(a), Word::Constant(b)) => Word::Constant(op.evaluate(a, b)),
                        _ if a == b && matches!(op, B::Eq | B::Ne) => {
                            Word::Constant(u64::from(op == B::Eq))
                        }
                        (Word::Nonzero, Word::Constant(0)) | (Word::Constant(0), Word::Nonzero)
                            if matches!(op, B::Eq | B::Ne) =>
                        {
                            Word::Constant(u64::from(op == B::Ne))
                        }
                        _ => Word::Unknown,
                    },
                    Value::Select(c, a, b) => match result[c].truth() {
                        Some(true) => result[a],
                        Some(false) => result[b],
                        None if result[a] == result[b] => result[a],
                        _ => Word::Unknown,
                    },
                    _ => Word::Unknown,
                }
            };
            result.push(value);
        }
        Ok(result)
    }
    /// A separate inverse traversal starts from the actual, unnormalized edge.
    pub fn close_edge(
        &self,
        nodes: &[Value],
        condition: Option<(usize, bool)>,
        work: &mut ssa::Budget,
    ) -> Result<Self, ssa::SsaError> {
        let mut result = self.clone();
        if matches!(self, Self::Unreachable) {
            return Ok(result);
        }
        let Some((id, truth)) = condition else {
            return Ok(result);
        };
        let mut pending = VecDeque::from([(id, truth)]);
        let mut visited = BTreeSet::new();
        while let Some((id, truth)) = pending.pop_front() {
            work.spend(1)?;
            if !visited.insert((id, truth)) {
                continue;
            }
            if let Some(known) = result.evaluate(nodes, work)?[id].truth()
                && known != truth
            {
                return Ok(Self::Unreachable);
            }
            result.insert(id, truth);
            if let Value::Binary(op, a, b) = nodes[id] {
                for (value, constant) in [(a, b), (b, a)] {
                    if matches!(op, B::Eq | B::Ne) && nodes[constant] == Value::Constant(0) {
                        pending.push_back((value, if op == B::Eq { !truth } else { truth }));
                    }
                    if op == B::Xor
                        && nodes[constant] == Value::Constant(1)
                        && nodes[value].is_boolean()
                    {
                        pending.push_back((value, !truth));
                    }
                }
            }
        }
        Ok(result)
    }
}
