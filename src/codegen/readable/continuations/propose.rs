use super::*;

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
// Freeze each flat path up to its return. Sharing a suffix factors the
// continuation without commuting effects or re-evaluating its condition.
struct Frozen<'a> {
    node: &'a Node,
    terminal: bool,
    text: String,
}
fn terminal<'a>(
    prefix: &'a [Node],
    next: &'a [Node],
    atom: &impl Fn(&Node) -> Option<String>,
    budget: &mut Budget,
) -> Option<Vec<Frozen<'a>>> {
    let mut out = Vec::new();
    for node in prefix.iter().chain(next) {
        budget.spend(1)?;
        if !matches!(
            node,
            Node::Step { .. } | Node::Evaluate(_) | Node::Return(_)
        ) {
            return None;
        }
        let text = atom(node)?;
        budget.text(&text)?;
        let terminal = matches!(node, Node::Return(_));
        if !text.is_empty() || terminal {
            out.push(Frozen {
                node,
                terminal,
                text,
            });
        }
        if terminal {
            return Some(out);
        }
    }
    None
}
fn share_tail(
    condition: &Expr,
    taken: &[Node],
    not_taken: &[Node],
    next: &[Node],
    atom: &impl Fn(&Node) -> Option<String>,
    budget: &mut Budget,
) -> Option<Vec<Node>> {
    let a = terminal(taken, next, atom, budget)?;
    let b = terminal(not_taken, next, atom, budget)?;
    let common = a
        .iter()
        .rev()
        .zip(b.iter().rev())
        .take_while(|(x, y)| x.terminal == y.terminal && x.text == y.text)
        .count();
    if common == 0 {
        return None;
    }
    let taken: Vec<_> = a[..a.len() - common]
        .iter()
        .map(|n| n.node.clone())
        .collect();
    let not_taken: Vec<_> = b[..b.len() - common]
        .iter()
        .map(|n| n.node.clone())
        .collect();
    let mut out = Vec::new();
    if !taken.is_empty() || !not_taken.is_empty() || condition.uses_memory() {
        out.push(Node::If {
            condition: condition.clone(),
            taken,
            not_taken,
        });
    }
    out.extend(a[a.len() - common..].iter().map(|n| n.node.clone()));
    Some(out)
}
pub(super) fn fold(
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
                if let Some(shared) = share_tail(condition, &taken, &not_taken, &out, atom, budget)
                {
                    out = shared;
                } else if !(taken.is_empty() && not_taken.is_empty() && !condition.uses_memory()) {
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
