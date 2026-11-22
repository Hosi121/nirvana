use super::*;

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
pub(super) fn check(
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
