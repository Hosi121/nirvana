use super::verify::check;
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
    assert_eq!(e.shared_fragments, 2);
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
    let (candidate, evidence) = recover_with(&source, &atom, &cond, &BTreeMap::new()).unwrap();
    assert_eq!(evidence.removed_conditions, 0);
    assert_eq!(evidence.shared_fragments, 2);
    assert!(
        matches!(candidate.first(), Some(Node::If { condition, .. }) if condition.uses_memory())
    );
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

#[test]
fn terminal_suffixes_share_after_distinct_prefixes_and_keep_the_branch() {
    let names = BTreeMap::from([(0, "a".into()), (1, "b".into()), (2, "p".into())]);
    for memory_condition in [false, true] {
        for layout in 0..3 {
            let mut a = vec![
                step(10, 3),
                Node::Evaluate(Expr::load(r(2), Width::U8)),
                Node::Return(Expr::binary(BinaryOp::Add, r(0), r(1))),
            ];
            let mut b = a.clone();
            b[0] = step(20, 4);
            let condition = if memory_condition {
                Expr::load(r(0), Width::U8)
            } else {
                r(0)
            };
            let return_node = a.last().unwrap().clone();
            if layout == 2 {
                a.pop();
                b.pop();
            }
            let mut source = vec![Node::If {
                condition,
                taken: std::mem::take(&mut a),
                not_taken: if layout != 0 { b.clone() } else { vec![] },
            }];
            if layout == 0 {
                source.extend(b);
            }
            if layout == 2 {
                source.push(return_node);
            }
            assert!(possible(&source));
            let (candidate, evidence) = recover_with(&source, &atom, &cond, &names).unwrap();
            assert_eq!(evidence.removed_conditions, 0);
            assert_eq!(evidence.shared_fragments, if layout == 2 { 1 } else { 2 });
            assert_eq!(candidate.len(), 3);
            assert!(check(&source, &candidate, &atom, &cond).is_some());
            let mut swapped = candidate;
            let Node::If {
                taken, not_taken, ..
            } = &mut swapped[0]
            else {
                panic!()
            };
            std::mem::swap(taken, not_taken);
            assert!(check(&source, &swapped, &atom, &cond).is_none());
        }
    }
}

#[test]
fn ordered_memory_fragments_keep_access_width_and_fault_order() {
    let write = Node::Step {
        address: 10,
        assignments: vec![Assignment {
            destination: Place::Memory {
                address: r(0),
                width: Width::U8,
            },
            value: Expr::load(r(1), Width::U64),
        }],
    };
    let read = Node::Evaluate(Expr::load(r(2), Width::U16));
    let ret = Node::Return(r(1));
    let source = vec![write.clone(), read.clone(), ret.clone()];
    let reordered = vec![read, write.clone(), ret.clone()];
    let dropped = vec![write, ret];
    let mut resized = source.clone();
    let Node::Step { assignments, .. } = &mut resized[0] else {
        panic!()
    };
    let Place::Memory { width, .. } = &mut assignments[0].destination else {
        panic!()
    };
    *width = Width::U64;
    assert!(check(&source, &source, &atom, &cond).is_some());
    for candidate in [reordered, dropped, resized] {
        assert!(check(&source, &candidate, &atom, &cond).is_none());
    }
}
