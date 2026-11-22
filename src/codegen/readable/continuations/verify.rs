use super::*;

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
enum Tag {
    Store(order::Span),
    Effect(effects::Effect),
}
impl Tag {
    fn span(&self) -> Option<order::Span> {
        match self {
            Self::Store(s) | Self::Effect(effects::Effect::Store { span: s, .. }) => Some(*s),
            _ => None,
        }
    }
}

// Independent of the proposal's modular interval formula and name-set test.
fn move_before(a: &Tag, b: &Tag) -> bool {
    let disjoint = |a: order::Span, b: order::Span| {
        a.root == b.root
            && a.offset > b.offset
            && !(0..a.bytes).any(|i| {
                (0..b.bytes).any(|j| {
                    a.offset.wrapping_add(u64::from(i)) == b.offset.wrapping_add(u64::from(j))
                })
            })
    };
    match (a, b) {
        (Tag::Store(a), Tag::Store(b)) => disjoint(*a, *b),
        (
            Tag::Effect(effects::Effect::Store { span: a, .. }),
            Tag::Effect(effects::Effect::Store { span: b, .. }),
        ) => disjoint(*a, *b),
        (
            Tag::Effect(effects::Effect::Store { reads, .. }),
            Tag::Effect(effects::Effect::Local { written, .. }),
        ) => reads.iter().all(|name| name != written),
        _ => false,
    }
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
enum Flow {
    End,
    Return(String),
    Step(String, Option<Tag>, usize),
    Branch(String, bool, usize, usize),
}
struct Pool {
    ids: BTreeMap<Flow, usize>,
    nodes: Vec<Flow>,
}
impl Pool {
    fn intern(&mut self, node: Flow, budget: &mut Budget) -> Option<usize> {
        budget.spend(1)?;
        if let Some(&id) = self.ids.get(&node) {
            return Some(id);
        }
        if self.nodes.len() >= MAX_ITEMS * 4 {
            return None;
        }
        if let Flow::Step(text, ..) | Flow::Return(text) | Flow::Branch(text, ..) = &node {
            budget.text(text)?;
        }
        let id = self.nodes.len();
        self.ids.insert(node.clone(), id);
        self.nodes.push(node);
        Some(id)
    }
    fn step(
        &mut self,
        text: String,
        tag: Option<Tag>,
        mut next: usize,
        budget: &mut Budget,
    ) -> Option<usize> {
        // Independent insertion into the continuation graph, rather than the
        // proposal's AST bubble sort. Compare actual byte offsets modulo 2^64.
        let mut skipped = Vec::new();
        if let Some(a) = &tag {
            while let Flow::Step(other, Some(b), tail) = &self.nodes[next] {
                budget.spend(match (a.span(), b.span()) {
                    (Some(a), Some(b)) => 1 + usize::from(a.bytes) * usize::from(b.bytes),
                    _ => 1,
                })?;
                if !move_before(a, b) {
                    break;
                }
                budget.text(other)?;
                skipped.push((other.clone(), b.clone()));
                next = *tail;
            }
        }
        next = self.intern(Flow::Step(text, tag, next), budget)?;
        for (text, span) in skipped.into_iter().rev() {
            next = self.intern(Flow::Step(text, Some(span), next), budget)?;
        }
        Some(next)
    }
}

#[derive(Clone, Copy)]
pub(super) enum Ordering<'a> {
    Stores(&'a order::Facts, &'a StoreProbe<'a>),
    Effects(&'a order::Facts, &'a EffectProbe<'a>),
}
impl Ordering<'_> {
    fn facts(&self) -> &order::Facts {
        match self {
            Self::Stores(f, _) | Self::Effects(f, _) => f,
        }
    }
    fn tag(&self, node: &Node) -> Option<Tag> {
        match self {
            Self::Stores(facts, store) => {
                store(node).filter(|s| facts.contains(*s)).map(Tag::Store)
            }
            Self::Effects(facts, effect) => {
                effects::witnessed(effect(node)?, facts).map(Tag::Effect)
            }
        }
    }
}
struct Check<'a, A, C> {
    atom: &'a A,
    condition: &'a C,
    ordering: Option<Ordering<'a>>,
    pool: Pool,
    budget: Budget,
}
impl<A: Fn(&Node) -> Option<String>, C: Fn(&Expr) -> Option<String>> Check<'_, A, C> {
    fn graph(&mut self, nodes: &[Node], mut next: usize) -> Option<usize> {
        for node in nodes.iter().rev() {
            self.budget.spend(1)?;
            next = match node {
                Node::If {
                    condition: c,
                    taken,
                    not_taken,
                } => {
                    let a = self.graph(taken, next)?;
                    let b = self.graph(not_taken, next)?;
                    if a == b && !c.uses_memory() {
                        a
                    } else {
                        let text = (self.condition)(c)?;
                        self.budget.text(&text)?;
                        self.pool
                            .intern(Flow::Branch(text, !c.uses_memory(), a, b), &mut self.budget)?
                    }
                }
                Node::Return(_) => {
                    let text = (self.atom)(node)?;
                    self.budget.text(&text)?;
                    self.pool.intern(Flow::Return(text), &mut self.budget)?
                }
                Node::Step { .. } | Node::Evaluate(_) => {
                    let text = (self.atom)(node)?;
                    self.budget.text(&text)?;
                    if text.is_empty() {
                        next
                    } else {
                        let tag = self.ordering.and_then(|ordering| ordering.tag(node));
                        self.pool.step(text, tag, next, &mut self.budget)?
                    }
                }
                _ => return None,
            };
        }
        Some(next)
    }
}

// Independently compose each actual AST into a hash-consed continuation graph.
// Pure tests with equal children are identities. Checked store permutations
// additionally require an unchanged, unconditionally executed read prefix.
fn check_inner(
    source: &[Node],
    candidate: &[Node],
    atom: &impl Fn(&Node) -> Option<String>,
    condition: &impl Fn(&Expr) -> Option<String>,
    ordering: Option<Ordering<'_>>,
) -> Option<usize> {
    shape(source)?;
    shape(candidate)?;
    let mut check = Check {
        atom,
        condition,
        ordering,
        pool: Pool {
            ids: BTreeMap::from([(Flow::End, 0)]),
            nodes: vec![Flow::End],
        },
        budget: Budget {
            work: MAX_WORK,
            bytes: MAX_BYTES,
        },
    };
    let a = check.graph(source, 0)?;
    let b = check.graph(candidate, 0)?;
    (a == b).then_some(check.pool.nodes.len())
}
pub(super) fn check(
    source: &[Node],
    candidate: &[Node],
    atom: &impl Fn(&Node) -> Option<String>,
    condition: &impl Fn(&Expr) -> Option<String>,
) -> Option<usize> {
    check_inner(source, candidate, atom, condition, None)
}
#[cfg(test)]
pub(super) fn check_ordered(
    source: &[Node],
    candidate: &[Node],
    atom: &impl Fn(&Node) -> Option<String>,
    condition: &impl Fn(&Expr) -> Option<String>,
    facts: &order::Facts,
    store: &StoreProbe<'_>,
) -> Option<usize> {
    check_ordering(
        source,
        candidate,
        atom,
        condition,
        Ordering::Stores(facts, store),
    )
}

pub(super) fn check_ordering(
    source: &[Node],
    candidate: &[Node],
    atom: &impl Fn(&Node) -> Option<String>,
    condition: &impl Fn(&Expr) -> Option<String>,
    ordering: Ordering<'_>,
) -> Option<usize> {
    let facts = ordering.facts();
    facts.matches(source, atom)?;
    facts.matches(candidate, atom)?;
    let prefix = facts.prefix_len();
    check_inner(
        &source[prefix..],
        &candidate[prefix..],
        atom,
        condition,
        Some(ordering),
    )
}
