//! C-scope continuation folding. Statement fragments are frozen after storage,
//! widths and memory views resolve; local declarations are at function scope.
//! PCs and machine-register traces are provenance, outside this projection.
use super::*;

mod order;
mod propose;
#[cfg(test)]
mod tests;
mod verify;
const MAX_ITEMS: usize = 4096;
const MAX_WORK: usize = 262144;
const MAX_BYTES: usize = 1024 * 1024;
pub const MODEL_ID: &str = "c-fragment-continuation-v2";
pub const STORE_ORDER_MODEL_ID: &str = "c-fragment-continuation-v3";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StoreOrderEvidence {
    pub prefix_nodes: usize,
    pub range_witnesses: usize,
    pub swapped_pairs: usize,
}

#[derive(Clone, Copy)]
pub(super) enum Strategy {
    Exact,
    CheckedStores,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ContinuationEvidence {
    /// Static If nodes removed, including copies whose evaluation is shared.
    pub removed_conditions: usize,
    /// Static nonempty Step/Evaluate/Return fragments shared between paths.
    pub shared_fragments: usize,
    pub compared_graph_nodes: usize,
    pub store_order: Option<StoreOrderEvidence>,
}
impl ContinuationEvidence {
    pub fn model(&self) -> &'static str {
        if self.store_order.is_some() {
            STORE_ORDER_MODEL_ID
        } else {
            MODEL_ID
        }
    }
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
    shape(nodes).is_some_and(|(conditions, returns)| conditions > 0 && returns > 0)
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
    recover_candidate(source, source, atom, condition, names, None, None)
}

type StoreProbe<'a> = dyn Fn(&Node) -> Option<order::Span> + 'a;
fn recover_candidate(
    source: &[Node],
    seed: &[Node],
    atom: &impl Fn(&Node) -> Option<String>,
    condition: &impl Fn(&Expr) -> Option<String>,
    names: &BTreeMap<usize, String>,
    ordering: Option<(&order::Facts, &StoreProbe<'_>)>,
    store_order: Option<StoreOrderEvidence>,
) -> Option<(Vec<Node>, ContinuationEvidence)> {
    let (before, _) = shape(source)?;
    let mut budget = Budget {
        work: MAX_WORK,
        bytes: MAX_BYTES,
    };
    let candidate = propose::fold(seed, &[], atom, &mut budget)?;
    let (after, _) = shape(&candidate)?;
    let removed_conditions = before.checked_sub(after)?;
    fn fragments(
        nodes: &[Node],
        atom: &impl Fn(&Node) -> Option<String>,
        budget: &mut Budget,
    ) -> Option<usize> {
        let mut pending: Vec<_> = nodes.iter().collect();
        let mut count = 0;
        while let Some(node) = pending.pop() {
            budget.spend(1)?;
            if let Node::If {
                taken, not_taken, ..
            } = node
            {
                pending.extend(taken.iter().chain(not_taken));
            } else {
                let text = atom(node)?;
                budget.text(&text)?;
                count += usize::from(!text.is_empty());
            }
        }
        Some(count)
    }
    let shared_fragments = fragments(source, atom, &mut budget)?.checked_sub(fragments(
        &candidate,
        atom,
        &mut budget,
    )?)?;
    if (after >= before && shared_fragments == 0)
        || read_names(source, names) != read_names(&candidate, names)
    {
        return None;
    }
    let compared_graph_nodes = if let Some((facts, store)) = ordering {
        verify::check_ordered(source, &candidate, atom, condition, facts, store)?
    } else {
        verify::check(source, &candidate, atom, condition)?
    };
    Some((
        candidate,
        ContinuationEvidence {
            removed_conditions,
            shared_fragments,
            compared_graph_nodes,
            store_order,
        },
    ))
}

pub(super) fn recover(
    printer: &Printer<'_>,
    nodes: &[Node],
    strategy: Strategy,
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
    match strategy {
        Strategy::Exact => recover_with(nodes, &atom, &condition, &printer.names),
        Strategy::CheckedStores => {
            let facts = order::facts(printer, nodes, &atom)?;
            let store = |node: &Node| order::store(printer, node);
            let (ordered, evidence) = order::propose(nodes, &facts, &store)?;
            recover_candidate(
                nodes,
                &ordered,
                &atom,
                &condition,
                &printer.names,
                Some((&facts, &store)),
                Some(evidence),
            )
        }
    }
}
