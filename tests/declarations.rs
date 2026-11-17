use nirvana::{ir, structure};
#[path = "../src/readable/declarations.rs"]
mod declarations;

use declarations::{
    DeclarationPlan, MAX_EXPRESSION_DEPTH, MAX_ITEMS, MAX_METADATA_BYTES, MAX_NAME_BYTES,
    MAX_NAMES, MAX_NODE_DEPTH,
};
use ir::{Assignment, BinaryOp, Expr, Place, Reg, Width};
use std::collections::{BTreeMap, BTreeSet};
use structure::Node;

fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn r(reg: usize) -> Expr {
    Expr::Register(Reg(reg))
}
fn set(reg: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(reg).into(),
        value,
    }
}
fn store(address: Expr, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address,
            width: Width::U64,
        },
        value,
    }
}
fn step(pc: u64, assignments: Vec<Assignment>) -> Node {
    Node::Step {
        address: pc,
        assignments,
    }
}
fn context(
    entries: &[(usize, &str)],
) -> (BTreeMap<usize, String>, BTreeSet<usize>, BTreeSet<String>) {
    (
        entries
            .iter()
            .map(|(reg, name)| (*reg, (*name).to_owned()))
            .collect(),
        entries.iter().map(|(reg, _)| *reg).collect(),
        entries.iter().map(|(_, name)| (*name).to_owned()).collect(),
    )
}
fn plan(nodes: &[Node], entries: &[(usize, &str)]) -> DeclarationPlan {
    let (names, read, eligible) = context(entries);
    DeclarationPlan::build(Some(nodes), None, &names, &read, &eligible)
}

#[test]
fn declares_first_writes_in_assignment_order_and_keeps_later_uses() {
    let nodes = vec![
        step(10, vec![set(0, c(5)), set(1, r(0)), set(0, c(6))]),
        step(11, vec![set(2, r(1))]),
        Node::Return(r(2)),
    ];
    let before = nodes.clone();
    let p = plan(&nodes, &[(0, "a"), (1, "b"), (2, "c")]);
    assert!(p.at((10, 0), "a"));
    assert!(p.at((10, 1), "b"));
    assert!(p.at((11, 0), "c"));
    assert!(!p.at((10, 2), "a"));
    assert!(!p.at((11, 0), "a"));
    assert!(!p.inline("unknown"));
    assert_eq!(nodes, before);
}

#[test]
fn aliases_share_first_write_and_prior_rhs_reads_block_every_alias() {
    let nodes = [step(
        10,
        vec![set(0, c(5)), set(1, c(6)), set(2, r(4)), set(3, c(7))],
    )];
    let p = plan(
        &nodes,
        &[
            (0, "shared"),
            (1, "shared"),
            (2, "other"),
            (3, "late"),
            (4, "late"),
        ],
    );
    assert!(p.at((10, 0), "shared"));
    assert!(!p.at((10, 1), "shared"));
    assert!(p.inline("other"));
    assert!(!p.inline("late"));
}

#[test]
fn direct_and_alias_self_reads_never_create_a_declaration() {
    let nodes = [step(
        1,
        vec![
            set(0, r(0)),
            set(1, Expr::binary(BinaryOp::Add, r(2), c(1))),
            set(3, Expr::load(r(4), Width::U8)),
        ],
    )];
    let p = plan(
        &nodes,
        &[
            (0, "self"),
            (1, "alias"),
            (2, "alias"),
            (3, "address"),
            (4, "address"),
        ],
    );
    for name in ["self", "alias", "address"] {
        assert!(!p.inline(name));
    }
}

#[test]
fn store_addresses_values_and_discarded_writes_still_count_as_prior_reads() {
    let nodes = [step(
        1,
        vec![
            store(r(0), r(1)),
            set(2, r(3)),
            set(4, c(1)),
            set(5, c(2)),
            set(6, c(3)),
        ],
    )];
    let (names, mut read, eligible) = context(&[
        (0, "address"),
        (1, "value"),
        (2, "discarded"),
        (3, "earlier"),
        (4, "address"),
        (5, "value"),
        (6, "earlier"),
    ]);
    read.remove(&2);
    let p = DeclarationPlan::build(Some(&nodes), None, &names, &read, &eligible);
    for name in ["address", "value", "earlier", "discarded"] {
        assert!(!p.inline(name));
    }
}

#[test]
fn unread_first_write_does_not_move_declaration_to_a_later_alias_write() {
    let nodes = [step(1, vec![set(0, c(1)), set(1, c(2))])];
    let (names, mut read, eligible) = context(&[(0, "value"), (1, "value")]);
    read.remove(&0);
    assert!(!DeclarationPlan::build(Some(&nodes), None, &names, &read, &eligible).inline("value"));
}

#[test]
fn eligible_excludes_parameters_and_destinations_must_be_named_and_read() {
    let nodes = [step(
        1,
        vec![set(0, c(1)), set(1, c(2)), set(2, c(3)), set(3, c(4))],
    )];
    let (names, mut read, mut eligible) = context(&[(0, "parameter"), (1, "local"), (2, "unread")]);
    read.remove(&2);
    eligible.remove("parameter");
    eligible.insert("absent".to_owned());
    let p = DeclarationPlan::build(Some(&nodes), None, &names, &read, &eligible);
    assert!(!p.inline("parameter"));
    assert!(p.inline("local"));
    assert!(!p.inline("unread"));
    assert!(!p.inline("absent"));
}

#[test]
fn permits_one_load_but_never_multiple_nested_or_lazy_arm_loads() {
    let load = || Expr::load(c(4096), Width::U64);
    let nodes = [step(
        1,
        vec![
            set(0, load()),
            set(1, Expr::binary(BinaryOp::Add, load(), load())),
            set(2, Expr::load(load(), Width::U8)),
            set(3, Expr::select(c(0), load(), load())),
            set(4, Expr::select(load(), c(1), c(2))),
        ],
    )];
    let p = plan(
        &nodes,
        &[
            (0, "one"),
            (1, "two"),
            (2, "nested"),
            (3, "lazy"),
            (4, "condition"),
        ],
    );
    assert!(p.inline("one"));
    assert!(p.inline("condition"));
    for name in ["two", "nested", "lazy"] {
        assert!(!p.inline(name));
    }
}

#[test]
fn stops_before_every_non_step_and_does_not_descend_into_control() {
    for control in [
        Node::Evaluate(c(0)),
        Node::Loop(vec![step(2, vec![set(1, c(2))])]),
        Node::If {
            condition: c(1),
            taken: vec![step(2, vec![set(1, c(2))])],
            not_taken: vec![],
        },
        Node::Return(c(0)),
        Node::Break,
        Node::Continue,
        Node::BreakOuter { levels: 1 },
        Node::ContinueOuter { levels: 1 },
    ] {
        let nodes = [
            step(1, vec![set(0, c(1))]),
            control,
            step(3, vec![set(2, c(3))]),
        ];
        let p = plan(&nodes, &[(0, "before"), (1, "nested"), (2, "after")]);
        assert!(p.inline("before"));
        assert!(!p.inline("nested"));
        assert!(!p.inline("after"));
    }
}

#[test]
fn duplicate_sites_anywhere_remove_only_the_affected_candidate() {
    let nodes = [
        step(10, vec![set(0, c(1)), set(1, c(2))]),
        step(11, vec![set(2, c(3))]),
        Node::Loop(vec![Node::If {
            condition: c(1),
            taken: vec![step(10, vec![store(c(0), c(0))])],
            not_taken: vec![],
        }]),
    ];
    let p = plan(
        &nodes,
        &[(0, "duplicate"), (1, "same_pc_other_index"), (2, "unique")],
    );
    assert!(!p.inline("duplicate"));
    assert!(p.at((10, 1), "same_pc_other_index"));
    assert!(p.inline("unique"));
}

#[test]
fn alternate_layout_intersects_names_and_exact_points_independently() {
    let (names, read, eligible) = context(&[(0, "a"), (1, "b")]);
    let nodes = [step(1, vec![set(0, c(1)), set(1, c(2))])];
    let same = [step(1, vec![set(0, c(9)), set(1, c(8))])];
    let p = DeclarationPlan::build(Some(&nodes), Some(&same), &names, &read, &eligible);
    assert!(p.at((1, 0), "a"));
    assert!(p.at((1, 1), "b"));
    let shifted = [step(1, vec![set(0, c(1))]), step(2, vec![set(1, c(2))])];
    let p = DeclarationPlan::build(Some(&nodes), Some(&shifted), &names, &read, &eligible);
    assert!(p.inline("a"));
    assert!(!p.inline("b"));
    let branch = [Node::If {
        condition: c(1),
        taken: nodes.to_vec(),
        not_taken: vec![],
    }];
    assert!(
        !DeclarationPlan::build(Some(&nodes), Some(&branch), &names, &read, &eligible).inline("a")
    );
    assert!(!DeclarationPlan::build(None, Some(&nodes), &names, &read, &eligible).inline("a"));
    assert!(!DeclarationPlan::build(Some(&nodes), Some(&[]), &names, &read, &eligible).inline("a"));
}

#[test]
fn alternate_duplicate_or_prior_alias_read_also_removes_primary_candidate() {
    let (names, read, eligible) = context(&[(0, "x"), (1, "x"), (2, "other")]);
    let main = [step(1, vec![set(0, c(1))])];
    let duplicate = [
        step(1, vec![set(0, c(1))]),
        Node::Loop(vec![step(1, vec![set(0, c(1))])]),
    ];
    assert!(
        !DeclarationPlan::build(Some(&main), Some(&duplicate), &names, &read, &eligible)
            .inline("x")
    );
    let prior = [step(9, vec![set(2, r(1))]), step(1, vec![set(0, c(1))])];
    assert!(
        !DeclarationPlan::build(Some(&main), Some(&prior), &names, &read, &eligible).inline("x")
    );
}

#[test]
fn sparse_register_ids_do_not_allocate_register_banks() {
    let nodes = [step(u64::MAX, vec![set(usize::MAX, c(1))])];
    let p = plan(&nodes, &[(usize::MAX, "sparse")]);
    assert!(p.at((u64::MAX, 0), "sparse"));
}

#[test]
fn depth_and_size_failure_outside_the_prefix_discard_every_candidate() {
    let (names, read, eligible) = context(&[(0, "x")]);
    let mut deep = c(0);
    for _ in 0..=MAX_EXPRESSION_DEPTH {
        deep = Expr::load(deep, Width::U8);
    }
    let nodes = [step(1, vec![set(0, c(1))]), Node::Return(deep)];
    assert!(!DeclarationPlan::build(Some(&nodes), None, &names, &read, &eligible).inline("x"));
    let mut node = Node::Break;
    for _ in 0..=MAX_NODE_DEPTH {
        node = Node::Loop(vec![node]);
    }
    let nodes = [step(1, vec![set(0, c(1))]), node];
    assert!(!DeclarationPlan::build(Some(&nodes), None, &names, &read, &eligible).inline("x"));
    let mut wide = vec![step(1, vec![set(0, c(1))])];
    wide.extend((0..MAX_ITEMS).map(|_| step(2, vec![])));
    assert!(!DeclarationPlan::build(Some(&wide), None, &names, &read, &eligible).inline("x"));
}

#[test]
fn combined_layout_budget_failure_discards_a_previously_valid_candidate() {
    let mut nodes = vec![step(1, vec![set(0, c(1))])];
    nodes.push(Node::Loop(
        (0..MAX_ITEMS / 2 + 1).map(|_| step(2, vec![])).collect(),
    ));
    let (names, read, eligible) = context(&[(0, "x")]);
    assert!(DeclarationPlan::build(Some(&nodes), None, &names, &read, &eligible).inline("x"));
    assert!(
        !DeclarationPlan::build(Some(&nodes), Some(&nodes), &names, &read, &eligible).inline("x")
    );
}

#[test]
fn metadata_limits_fail_closed_before_cloning_names() {
    let nodes = [step(1, vec![set(0, c(1))])];
    let (names, read, mut eligible) = context(&[(0, "x")]);
    eligible.insert("y".repeat(MAX_NAME_BYTES + 1));
    assert!(!DeclarationPlan::build(Some(&nodes), None, &names, &read, &eligible).inline("x"));
    let mut too_many = names.clone();
    for i in 1..=MAX_NAMES {
        too_many.insert(i, "unused".to_owned());
    }
    assert!(
        !DeclarationPlan::build(
            Some(&nodes),
            None,
            &too_many,
            &read,
            &BTreeSet::from(["x".to_owned()])
        )
        .inline("x")
    );
    let huge_names: BTreeMap<_, _> = (0..MAX_NAMES)
        .map(|i| (i, "x".repeat(MAX_NAME_BYTES)))
        .collect();
    assert!(huge_names.values().map(String::len).sum::<usize>() > MAX_METADATA_BYTES);
    assert!(
        !DeclarationPlan::build(
            Some(&nodes),
            None,
            &huge_names,
            &read,
            &BTreeSet::from(["x".to_owned()])
        )
        .inline("x")
    );
}
