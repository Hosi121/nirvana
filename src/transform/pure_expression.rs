//! Bounded source-tree checks shared by signed arithmetic views.
use crate::model::ir::Expr;

pub const MAX_NODES: usize = 4096;
pub const MAX_DEPTH: usize = 128;
pub const MAX_WORK: usize = 65_536;

pub(super) struct Work(usize);
impl Work {
    pub fn new() -> Self {
        Self(MAX_WORK)
    }
    pub fn used(&self) -> usize {
        MAX_WORK - self.0
    }
    pub fn spend(&mut self) -> Option<()> {
        self.0 = self.0.checked_sub(1)?;
        Some(())
    }
    pub fn pure(&mut self, expression: &Expr) -> Option<()> {
        let mut pending = vec![(expression, 1)];
        let mut nodes = 0;
        while let Some((e, depth)) = pending.pop() {
            self.spend()?;
            nodes += 1;
            if nodes > MAX_NODES || depth > MAX_DEPTH {
                return None;
            }
            match e {
                Expr::Load { .. } => return None,
                Expr::Unary(_, value) => pending.push((value, depth + 1)),
                Expr::Binary(_, a, b) => {
                    pending.extend([(a.as_ref(), depth + 1), (b.as_ref(), depth + 1)])
                }
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([
                    (condition.as_ref(), depth + 1),
                    (taken.as_ref(), depth + 1),
                    (not_taken.as_ref(), depth + 1),
                ]),
                _ => {}
            }
        }
        Some(())
    }
    pub fn same(&mut self, a: &Expr, b: &Expr) -> Option<bool> {
        let mut pending = vec![(a, b)];
        while let Some((a, b)) = pending.pop() {
            self.spend()?;
            match (a, b) {
                (Expr::Const(a), Expr::Const(b)) if a == b => {}
                (Expr::Register(a), Expr::Register(b)) if a == b => {}
                (Expr::Unary(a, x), Expr::Unary(b, y)) if a == b => pending.push((x, y)),
                (Expr::Binary(a, al, ar), Expr::Binary(b, bl, br)) if a == b => {
                    pending.extend([(al.as_ref(), bl.as_ref()), (ar.as_ref(), br.as_ref())])
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
                ) => pending.extend([
                    (a.as_ref(), b.as_ref()),
                    (at.as_ref(), bt.as_ref()),
                    (an.as_ref(), bn.as_ref()),
                ]),
                _ => return Some(false),
            }
        }
        Some(true)
    }
}
