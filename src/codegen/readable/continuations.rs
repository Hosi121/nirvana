//! C-scope continuation folding. Statement fragments are frozen after storage,
//! widths and memory views resolve; local declarations are at function scope.
//! PCs and machine-register traces are provenance, outside this projection.
use super::*;
const MAX_ITEMS: usize = 4096;
const MAX_WORK: usize = 262144;
const MAX_BYTES: usize = 1024 * 1024;
pub const MODEL_ID: &str = "c-fragment-continuation-v1";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ContinuationEvidence {
    pub removed_conditions: usize,
    pub compared_graph_nodes: usize,
}

fn shape(nodes: &[Node]) -> Option<(usize, usize)> {
    let mut pending: Vec<_> = nodes.iter().map(|n| (n, 0)).collect();
    let (mut items, mut conditions, mut returns) = (0, 0, 0);
    while let Some((node, depth)) = pending.pop() {
        items += 1;
        if items > MAX_ITEMS || depth > 64 {
            return None;
        }
        match node {
            Node::If {
                taken, not_taken, ..
            } => {
                conditions += 1;
                pending.extend(taken.iter().chain(not_taken).map(|n| (n, depth + 1)));
            }
            Node::Return(_) => returns += 1,
            Node::Step { .. } | Node::Evaluate(_) => {}
            _ => return None,
        }
    }
    Some((conditions, returns))
}
pub(super) fn possible(nodes: &[Node]) -> bool {
    shape(nodes).is_some_and(|(conditions, returns)| conditions > 0 && returns > 1)
}
struct Budget {
    work: usize,
    bytes: usize,
}
impl Budget {
    fn spend(&mut self, n: usize) -> Option<()> {
        self.work = self.work.checked_sub(n)?;
        Some(())
    }
    fn text(&mut self, text: &str) -> Option<()> {
        self.bytes = self.bytes.checked_sub(text.len())?;
        Some(())
    }
}

fn read_names(nodes: &[Node], names: &BTreeMap<usize, String>) -> BTreeSet<String> {
    let mut result = BTreeSet::new();
    let mut expressions = Vec::new();
    let mut pending: Vec<_> = nodes.iter().collect();
    while let Some(node) = pending.pop() {
        match node {
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                expressions.push(condition);
                pending.extend(taken.iter().chain(not_taken));
            }
            Node::Step { assignments, .. } => {
                for a in assignments {
                    expressions.push(&a.value);
                    if let Place::Memory { address, .. } = &a.destination {
                        expressions.push(address);
                    }
                }
            }
            Node::Evaluate(e) | Node::Return(e) => expressions.push(e),
            _ => {}
        }
    }
    while let Some(e) = expressions.pop() {
        match e {
            Expr::Register(r) => {
                if let Some(name) = names.get(&r.0) {
                    result.insert(name.clone());
                }
            }
            Expr::Unary(_, x) | Expr::Load { address: x, .. } => expressions.push(x),
            Expr::Binary(_, a, b) => expressions.extend([a.as_ref(), b.as_ref()]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => expressions.extend([condition.as_ref(), taken.as_ref(), not_taken.as_ref()]),
            _ => {}
        }
    }
    result
}

fn recover_with(
    source: &[Node],
    atom: &impl Fn(&Node) -> Option<String>,
    condition: &impl Fn(&Expr) -> Option<String>,
    names: &BTreeMap<usize, String>,
) -> Option<(Vec<Node>, ContinuationEvidence)> {
    let (before, _) = shape(source)?;
    let mut budget = Budget {
        work: MAX_WORK,
        bytes: MAX_BYTES,
    };
    // The proposer compares flat terminal continuations in lexical context.
    fn linear(
        nodes: &[Node],
        atom: &impl Fn(&Node) -> Option<String>,
        budget: &mut Budget,
    ) -> Option<Vec<(bool, String)>> {
        let mut out = Vec::new();
        for node in nodes {
            budget.spend(1)?;
            if !matches!(
                node,
                Node::Step { .. } | Node::Return(_) | Node::Evaluate(_)
            ) {
                return None;
            }
            let text = atom(node)?;
            budget.text(&text)?;
            if !text.is_empty() {
                out.push((matches!(node, Node::Return(_)), text));
            }
            if matches!(node, Node::Return(_)) {
                return Some(out);
            }
        }
        None
    }
    fn fold(
        nodes: &[Node],
        tail: &[Node],
        atom: &impl Fn(&Node) -> Option<String>,
        budget: &mut Budget,
    ) -> Option<Vec<Node>> {
        let mut out = Vec::new();
        for node in nodes.iter().rev() {
            budget.spend(1)?;
            match node {
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    budget.spend(out.len() + tail.len())?;
                    let mut continuation = out.clone();
                    continuation.extend_from_slice(tail);
                    let mut taken = fold(taken, &continuation, atom, budget)?;
                    let mut not_taken = fold(not_taken, &continuation, atom, budget)?;
                    if !condition.uses_memory()
                        && let Some(after) = linear(&continuation, atom, budget)
                    {
                        if linear(&taken, atom, budget).as_ref() == Some(&after) {
                            taken.clear();
                        }
                        if linear(&not_taken, atom, budget).as_ref() == Some(&after) {
                            not_taken.clear();
                        }
                    }
                    if !(taken.is_empty() && not_taken.is_empty() && !condition.uses_memory()) {
                        out.insert(
                            0,
                            Node::If {
                                condition: condition.clone(),
                                taken,
                                not_taken,
                            },
                        );
                    }
                }
                _ => out.insert(0, node.clone()),
            }
        }
        Some(out)
    }
    let candidate = fold(source, &[], atom, &mut budget)?;
    let (after, _) = shape(&candidate)?;
    if after >= before || read_names(source, names) != read_names(&candidate, names) {
        return None;
    }
    let compared_graph_nodes = check(source, &candidate, atom, condition)?;
    Some((
        candidate,
        ContinuationEvidence {
            removed_conditions: before - after,
            compared_graph_nodes,
        },
    ))
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
enum Flow {
    End,
    Return(String),
    Step(String, usize),
    Branch(String, bool, usize, usize),
}
// Independently compose each actual AST into a hash-consed continuation graph.
// Pure tests with equal children are identities. Every other emitted fragment
// remains ordered and exact, including checked accesses and their first faults.
fn check(
    source: &[Node],
    candidate: &[Node],
    atom: &impl Fn(&Node) -> Option<String>,
    condition: &impl Fn(&Expr) -> Option<String>,
) -> Option<usize> {
    shape(source)?;
    shape(candidate)?;
    fn intern(pool: &mut BTreeMap<Flow, usize>, node: Flow, budget: &mut Budget) -> Option<usize> {
        budget.spend(1)?;
        if let Some(&id) = pool.get(&node) {
            return Some(id);
        }
        if pool.len() >= MAX_ITEMS * 4 {
            return None;
        }
        let id = pool.len();
        pool.insert(node, id);
        Some(id)
    }
    fn graph(
        nodes: &[Node],
        mut next: usize,
        pool: &mut BTreeMap<Flow, usize>,
        atom: &impl Fn(&Node) -> Option<String>,
        condition: &impl Fn(&Expr) -> Option<String>,
        budget: &mut Budget,
    ) -> Option<usize> {
        for node in nodes.iter().rev() {
            budget.spend(1)?;
            next = match node {
                Node::If {
                    condition: c,
                    taken,
                    not_taken,
                } => {
                    let a = graph(taken, next, pool, atom, condition, budget)?;
                    let b = graph(not_taken, next, pool, atom, condition, budget)?;
                    if a == b && !c.uses_memory() {
                        a
                    } else {
                        let text = condition(c)?;
                        budget.text(&text)?;
                        intern(pool, Flow::Branch(text, !c.uses_memory(), a, b), budget)?
                    }
                }
                Node::Return(_) => {
                    let text = atom(node)?;
                    budget.text(&text)?;
                    intern(pool, Flow::Return(text), budget)?
                }
                Node::Step { .. } | Node::Evaluate(_) => {
                    let text = atom(node)?;
                    budget.text(&text)?;
                    if text.is_empty() {
                        next
                    } else {
                        intern(pool, Flow::Step(text, next), budget)?
                    }
                }
                _ => return None,
            };
        }
        Some(next)
    }
    let mut pool = BTreeMap::from([(Flow::End, 0)]);
    let mut budget = Budget {
        work: MAX_WORK,
        bytes: MAX_BYTES,
    };
    let a = graph(source, 0, &mut pool, atom, condition, &mut budget)?;
    let b = graph(candidate, 0, &mut pool, atom, condition, &mut budget)?;
    (a == b).then_some(pool.len())
}

pub(super) fn recover(
    printer: &Printer<'_>,
    nodes: &[Node],
) -> Option<(Vec<Node>, ContinuationEvidence)> {
    let atom = |node: &Node| {
        let mut out = String::new();
        printer
            .nodes(&mut out, std::slice::from_ref(node), 0, false)
            .ok()?;
        Some(out)
    };
    let condition = |value: &Expr| {
        let mut out = String::new();
        printer
            .value_statement(&mut out, 0, value, None, "if (", ")")
            .ok()?;
        Some(out)
    };
    recover_with(nodes, &atom, &condition, &printer.names)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn r(n: usize) -> Expr {
        Expr::Register(Reg(n))
    }
    fn step(pc: u64, value: u64) -> Node {
        Node::Step {
            address: pc,
            assignments: vec![Assignment {
                destination: Reg(1).into(),
                value: Expr::Const(value),
            }],
        }
    }
    fn atom(n: &Node) -> Option<String> {
        match n {
            Node::Step { assignments, .. } => Some(format!("{assignments:?}")),
            Node::Return(e) => Some(format!("return {e:?}")),
            Node::Evaluate(e) => Some(format!("eval {e:?}")),
            _ => None,
        }
    }
    fn cond(e: &Expr) -> Option<String> {
        Some(format!("{e:?}"))
    }
    fn nodes() -> Vec<Node> {
        let ret = Node::Return(Expr::binary(BinaryOp::Add, r(0), r(1)));
        vec![
            Node::If {
                condition: r(0),
                taken: vec![step(10, 7), ret.clone()],
                not_taken: vec![],
            },
            step(20, 7),
            ret,
        ]
    }
    #[test]
    fn terminal_c_continuations_share_across_distinct_machine_pcs() {
        let source = nodes();
        let names = BTreeMap::from([(0, "a".into()), (1, "b".into())]);
        let (candidate, e) = recover_with(&source, &atom, &cond, &names).unwrap();
        assert_eq!(candidate.len(), 2);
        assert_eq!(e.removed_conditions, 1);
        assert!(check(&source, &candidate, &atom, &cond).is_some());
    }
    #[test]
    fn effects_returns_memory_conditions_and_cycles_reject_unsound_candidates() {
        let source = nodes();
        let bad = vec![step(20, 8), source[2].clone()];
        assert!(check(&source, &bad, &atom, &cond).is_none());
        let mut changed_return = source.clone();
        changed_return[2] = Node::Return(Expr::Const(9));
        assert!(check(&source, &changed_return, &atom, &cond).is_none());
        let mut source = nodes();
        let Node::If { condition, .. } = &mut source[0] else {
            panic!()
        };
        *condition = Expr::load(r(0), Width::U8);
        assert!(check(&source, &source[1..], &atom, &cond).is_none());
        assert!(recover_with(&source, &atom, &cond, &BTreeMap::new()).is_none());
        assert!(!possible(&[Node::Loop(nodes())]));
    }
    #[test]
    fn changed_local_read_sets_keep_the_original_scope_plan() {
        let mut source = nodes();
        source[2] = Node::Return(r(1));
        let Node::If { taken, .. } = &mut source[0] else {
            panic!()
        };
        taken[1] = Node::Return(r(1));
        assert!(
            recover_with(
                &source,
                &atom,
                &cond,
                &BTreeMap::from([(0, "a".into()), (1, "b".into())])
            )
            .is_none()
        );
    }
}
