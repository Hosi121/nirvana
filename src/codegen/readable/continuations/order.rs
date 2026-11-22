//! Checked flat RW C memory: a successful read witnesses the same write range.
//! Only const input views participate. Different bases may alias; their stores
//! keep their order. The source prefix remains unchanged in every candidate.
use super::*;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Span {
    pub root: usize,
    pub offset: u64,
    pub bytes: u8,
}
impl Span {
    pub(super) fn disjoint(self, other: Self) -> bool {
        self.root == other.root
            && self.offset.wrapping_sub(other.offset) >= u64::from(other.bytes)
            && other.offset.wrapping_sub(self.offset) >= u64::from(self.bytes)
    }
}

pub(super) struct Facts {
    prefix: Vec<String>,
    ranges: BTreeSet<Span>,
}
impl Facts {
    pub fn contains(&self, span: Span) -> bool {
        self.ranges.contains(&span)
    }
    pub fn prefix_len(&self) -> usize {
        self.prefix.len()
    }
    pub fn range_count(&self) -> usize {
        self.ranges.len()
    }
    pub fn matches(&self, nodes: &[Node], atom: &impl Fn(&Node) -> Option<String>) -> Option<()> {
        if nodes.len() < self.prefix.len() {
            return None;
        }
        for (node, expected) in nodes.iter().zip(&self.prefix) {
            if !matches!(node, Node::Step { .. } | Node::Evaluate(_)) || atom(node)? != *expected {
                return None;
            }
        }
        Some(())
    }
}

fn span(
    printer: &Printer<'_>,
    point: Option<(u64, usize)>,
    address: &Expr,
    width: Width,
) -> Option<Span> {
    if address.uses_memory() {
        return None;
    }
    let (root, offset) = printer.views.as_ref()?.fixed_input_at(point, address)?;
    Some(Span {
        root: root.0,
        offset: offset as u64,
        bytes: width.bytes() as u8,
    })
}

pub(super) fn facts(
    printer: &Printer<'_>,
    nodes: &[Node],
    atom: &impl Fn(&Node) -> Option<String>,
) -> Option<Facts> {
    let mut result = Facts {
        prefix: Vec::new(),
        ranges: BTreeSet::new(),
    };
    let mut work = MAX_WORK;
    let mut bytes = MAX_BYTES;
    for node in nodes {
        if !matches!(node, Node::Step { .. } | Node::Evaluate(_)) {
            break;
        }
        let text = atom(node)?;
        bytes = bytes.checked_sub(text.len())?;
        result.prefix.push(text);
        if let Node::Step {
            address: pc,
            assignments,
        } = node
        {
            for (index, assignment) in assignments.iter().enumerate() {
                work = work.checked_sub(1)?;
                // A direct register load is unconditionally evaluated. Lazy
                // Select arms and context-dependent arithmetic stay outside.
                if let Place::Register(_) = assignment.destination
                    && let Expr::Load { address, width } = &assignment.value
                    && let Some(range) = span(printer, Some((*pc, index)), address, *width)
                {
                    result.ranges.insert(range);
                }
            }
        }
    }
    (result.ranges.len() >= 2 && result.ranges.len() <= MAX_ITEMS).then_some(result)
}

pub(super) fn store(printer: &Printer<'_>, node: &Node) -> Option<Span> {
    let Node::Step {
        address: pc,
        assignments,
    } = node
    else {
        return None;
    };
    let [assignment] = assignments.as_slice() else {
        return None;
    };
    let Place::Memory { address, width } = &assignment.destination else {
        return None;
    };
    if assignment.value.uses_memory() {
        return None;
    }
    span(printer, Some((*pc, 0)), address, *width)
}

pub(super) fn propose(
    nodes: &[Node],
    facts: &Facts,
    store: &impl Fn(&Node) -> Option<Span>,
) -> Option<(Vec<Node>, StoreOrderEvidence)> {
    let tag = |node: &Node| store(node).filter(|s| facts.contains(*s));
    let inversion = |a: &Span, b: &Span| {
        (a.offset > b.offset && a.disjoint(*b)).then_some(permutations::Swap::Store)
    };
    let (result, counts) = permutations::propose(nodes, facts.prefix_len(), &tag, &inversion)?;
    (counts.stores > 0).then_some((
        result,
        StoreOrderEvidence {
            prefix_nodes: facts.prefix_len(),
            range_witnesses: facts.range_count(),
            swapped_pairs: counts.stores,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn at(root: usize, offset: u64, bytes: u8) -> Span {
        Span {
            root,
            offset,
            bytes,
        }
    }
    fn node(pc: u64) -> Node {
        Node::Step {
            address: pc,
            assignments: vec![],
        }
    }
    fn atom(node: &Node) -> Option<String> {
        Some(format!("{node:?}"))
    }
    fn condition(expr: &Expr) -> Option<String> {
        Some(format!("{expr:?}"))
    }

    #[test]
    fn modular_range_test_matches_byte_sets_at_wraparound() {
        for a in -16_i64..=16 {
            for b in -16_i64..=16 {
                for aw in [1, 2, 4, 8] {
                    for bw in [1, 2, 4, 8] {
                        let x = at(0, a as u64, aw);
                        let y = at(0, b as u64, bw);
                        let overlap = (0..aw).any(|i| {
                            (0..bw).any(|j| {
                                x.offset.wrapping_add(u64::from(i))
                                    == y.offset.wrapping_add(u64::from(j))
                            })
                        });
                        assert_eq!(x.disjoint(y), !overlap, "{x:?} {y:?}");
                        assert!(!x.disjoint(at(1, y.offset, bw)));
                    }
                }
            }
        }
    }

    #[test]
    fn graph_checker_requires_read_prefix_ranges_and_keeps_overlap_and_alias_order() {
        let prefix = node(0);
        let source = vec![
            prefix.clone(),
            node(1),
            node(2),
            Node::Return(Expr::Const(7)),
        ];
        let candidate = vec![prefix, node(2), node(1), Node::Return(Expr::Const(7))];
        for (a, b, safe) in [
            (at(0, 8, 8), at(0, 0, 8), true),
            (at(0, u64::MAX - 3, 4), at(0, 0, 4), true),
            (at(0, 4, 8), at(0, 0, 8), false),
            (at(0, u64::MAX - 3, 8), at(0, 0, 4), false),
            (at(1, 8, 8), at(0, 0, 8), false),
        ] {
            let facts = Facts {
                prefix: vec![atom(&source[0]).unwrap()],
                ranges: BTreeSet::from([a, b]),
            };
            let store = |n: &Node| match n {
                Node::Step { address: 1, .. } => Some(a),
                Node::Step { address: 2, .. } => Some(b),
                _ => None,
            };
            assert!(verify::check(&source, &candidate, &atom, &condition).is_none());
            assert_eq!(
                verify::check_ordered(&source, &candidate, &atom, &condition, &facts, &store)
                    .is_some(),
                safe
            );
            assert_eq!(propose(&source, &facts, &store).is_some(), safe);
            let mut changed = candidate.clone();
            changed[0] = node(9);
            assert!(
                verify::check_ordered(&source, &changed, &atom, &condition, &facts, &store)
                    .is_none()
            );
            let missing = Facts {
                prefix: facts.prefix.clone(),
                ranges: BTreeSet::from([a]),
            };
            assert!(
                verify::check_ordered(&source, &candidate, &atom, &condition, &missing, &store)
                    .is_none()
            );
            assert!(propose(&source, &missing, &store).is_none());
        }
    }

    #[test]
    fn graph_insertion_checks_entire_store_runs_and_effect_barriers() {
        let source = vec![
            node(0),
            node(3),
            node(2),
            node(1),
            Node::Return(Expr::Const(7)),
        ];
        let candidate = vec![
            node(0),
            node(1),
            node(2),
            node(3),
            Node::Return(Expr::Const(7)),
        ];
        let ranges: BTreeSet<_> = (1..=3).map(|n| at(0, n * 8, 8)).collect();
        let facts = Facts {
            prefix: vec![atom(&source[0]).unwrap()],
            ranges,
        };
        let store = |n: &Node| match n {
            Node::Step {
                address: n @ 1..=3, ..
            } => Some(at(0, n * 8, 8)),
            _ => None,
        };
        assert!(
            verify::check_ordered(&source, &candidate, &atom, &condition, &facts, &store).is_some()
        );
        let mut source = source;
        source.insert(2, Node::Evaluate(Expr::load(Expr::Const(100), Width::U64)));
        let mut candidate = candidate;
        candidate.insert(2, source[2].clone());
        assert!(
            verify::check_ordered(&source, &candidate, &atom, &condition, &facts, &store).is_none()
        );
    }

    #[test]
    fn scalar_store_graphs_use_frozen_c_storage_dependencies() {
        let source = vec![
            node(0),
            node(1),
            node(2),
            node(3),
            Node::Return(Expr::Const(7)),
        ];
        let candidate = vec![
            node(0),
            node(2),
            node(1),
            node(3),
            Node::Return(Expr::Const(7)),
        ];
        let a = at(0, 0, 8);
        let facts = Facts {
            prefix: vec![atom(&source[0]).unwrap()],
            ranges: BTreeSet::from([a]),
        };
        for (written, safe) in [("value", false), ("other", true)] {
            let effect = |n: &Node| match n {
                Node::Step { address: 1, .. } => Some(effects::Effect::Store {
                    span: a,
                    reads: BTreeSet::from(["value".into()]),
                }),
                Node::Step { address: 2, .. } => Some(effects::Effect::Local {
                    written: written.into(),
                    reads: BTreeSet::from(["value".into()]),
                }),
                _ => None,
            };
            let ordering = verify::Ordering::Effects(&facts, &effect);
            assert_eq!(
                verify::check_ordering(&source, &candidate, &atom, &condition, ordering).is_some(),
                safe
            );
            let proposal = effects::propose(&source, &facts, &effect);
            assert_eq!(proposal.is_some(), safe);
            if let Some((nodes, evidence)) = proposal {
                assert_eq!(evidence.local_pairs, 1);
                assert_eq!(evidence.store_pairs, 0);
                assert!(
                    verify::check_ordering(&source, &nodes, &atom, &condition, ordering).is_some()
                );
            }
            let mut barrier = source.clone();
            barrier.swap(2, 3);
            assert!(
                verify::check_ordering(&barrier, &candidate, &atom, &condition, ordering).is_none()
            );
            let mut changed_prefix = candidate.clone();
            changed_prefix[0] = node(9);
            assert!(
                verify::check_ordering(&source, &changed_prefix, &atom, &condition, ordering)
                    .is_none()
            );
        }
    }
}
