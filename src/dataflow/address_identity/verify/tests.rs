use super::*;
use crate::dataflow::ssa::SsaFunction;
use crate::model::ir::{Assignment, Control, IrInstruction, Place, Reg, Width};

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Register(Reg(n)),
        value,
    }
}
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn source(instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, 8, instructions).unwrap()
}
fn straight(assignments: Vec<Assignment>, result: Expr) -> Program {
    source(vec![ins(0, assignments, Control::Return(result))])
}
fn graph(source: &Program) -> (SsaFunction, Vec<ValueId>) {
    let graph = SsaFunction::build(source).unwrap();
    let identity = (0..graph.values.len()).map(ValueId).collect();
    (graph, identity)
}
fn assignment(graph: &SsaFunction, instruction: u64, assignment: usize) -> ValueId {
    graph
        .point(Site {
            instruction,
            assignment: Some(assignment),
        })
        .unwrap()
        .definition
        .unwrap()
}
fn input(graph: &SsaFunction, instruction: u64, assignment: usize) -> ValueId {
    graph
        .point(Site {
            instruction,
            assignment: Some(assignment),
        })
        .unwrap()
        .reads[0]
        .value
}
fn initial(graph: &SsaFunction, register: usize) -> ValueId {
    ValueId(graph.values.iter().position(|definition| {
        matches!(definition, Definition::Initial { register: Reg(r) } if *r == register)
    }).unwrap())
}
fn valid(source: &Program, graph: &SsaFunction, ids: &[ValueId]) -> bool {
    validate(source, graph, ids, &BTreeSet::new()).is_some()
}

#[test]
fn identity_and_nonmaximal_copy_classes_are_accepted() {
    let source = straight(vec![set(2, r(0)), set(3, r(2)), set(4, r(3))], r(4));
    let (graph, mut ids) = graph(&source);
    assert!(valid(&source, &graph, &ids));
    let root = input(&graph, 0, 0);
    // Leave the last true equality unmerged.
    for index in 0..2 {
        ids[assignment(&graph, 0, index).0] = root;
    }
    assert!(valid(&source, &graph, &ids));
    assert!(super::super::aliases(&source, &graph, &BTreeSet::new()).is_some());
}

#[test]
fn dimensions_indices_and_noncanonical_roots_are_rejected() {
    let source = straight(vec![set(2, r(0)), set(3, r(2))], r(3));
    let (graph, mut ids) = graph(&source);
    assert!(!valid(&source, &graph, &ids[..ids.len() - 1]));
    let copy = assignment(&graph, 0, 0);
    let other = assignment(&graph, 0, 1);
    ids[copy.0] = ValueId(ids.len());
    assert!(!valid(&source, &graph, &ids));
    ids[copy.0] = other;
    ids[other.0] = input(&graph, 0, 0);
    assert!(!valid(&source, &graph, &ids));
}

#[test]
fn fresh_initial_load_noncopy_and_opaque_atoms_cannot_be_merged() {
    let source = straight(
        vec![
            set(2, Expr::load(r(0), Width::U64)),
            set(3, Expr::load(r(0), Width::U64)),
            set(4, Expr::Const(10)),
            set(5, r(0)),
        ],
        Expr::binary(crate::model::ir::BinaryOp::Add, r(5), r(1)),
    );
    let (graph, ids) = graph(&source);
    let initial = input(&graph, 0, 0);
    let load = assignment(&graph, 0, 0);
    for (a, b) in [
        (self::initial(&graph, 0), self::initial(&graph, 1)),
        (initial, load),
        (load, self::initial(&graph, 0)),
        (assignment(&graph, 0, 1), load),
        (assignment(&graph, 0, 2), initial),
    ] {
        let mut bad = ids.clone();
        bad[a.0] = b;
        assert!(!valid(&source, &graph, &bad), "{a:?} -> {b:?}");
        assert!(super::super::collect::collect(&source, &graph, &bad).is_none());
    }
    let copy = assignment(&graph, 0, 3);
    let mut bad = ids;
    bad[copy.0] = initial;
    assert!(valid(&source, &graph, &bad));
    let opaque = BTreeSet::from([Site {
        instruction: 0,
        assignment: Some(3),
    }]);
    assert!(validate(&source, &graph, &bad, &opaque).is_none());
}

fn diamond(different: bool) -> Program {
    source(vec![
        ins(
            0,
            vec![],
            Control::Branch {
                condition: r(7),
                target: 2,
            },
        ),
        ins(1, vec![set(2, r(0))], Control::Jump(3)),
        ins(
            2,
            vec![set(2, r(if different { 1 } else { 0 }))],
            Control::Jump(3),
        ),
        ins(
            3,
            vec![set(3, r(2)), set(4, Expr::load(r(3), Width::U8))],
            Control::Return(r(4)),
        ),
    ])
}

#[test]
fn equal_phi_inputs_and_following_copies_are_accepted() {
    let source = diamond(false);
    let (graph, _) = graph(&source);
    let ids = super::super::aliases(&source, &graph, &BTreeSet::new()).unwrap();
    assert!(valid(&source, &graph, &ids));
    let before = super::super::collect::collect(&source, &graph, &ids).unwrap();
    assert_eq!(before.len(), 1);
}

#[test]
fn varying_phi_is_a_valid_fresh_anchor_for_its_copies() {
    let source = diamond(true);
    let (graph, mut ids) = graph(&source);
    let phi = input(&graph, 3, 0);
    assert!(matches!(graph.values[phi.0], Definition::Phi { .. }));
    ids[assignment(&graph, 3, 0).0] = phi;
    assert!(valid(&source, &graph, &ids));
    assert!(super::super::aliases(&source, &graph, &BTreeSet::new()).is_some());
}

#[test]
fn one_different_phi_input_cannot_be_omitted_from_the_proof() {
    let source = diamond(true);
    let (graph, mut ids) = graph(&source);
    let left = assignment(&graph, 1, 0);
    let right = assignment(&graph, 2, 0);
    let root = input(&graph, 1, 0);
    let phi = input(&graph, 3, 0);
    ids[left.0] = root;
    ids[phi.0] = root;
    ids[assignment(&graph, 3, 0).0] = root;
    assert_ne!(ids[right.0], root);
    assert!(!valid(&source, &graph, &ids));
    let mut bad_graph = graph.clone();
    let Definition::Phi { inputs, .. } = &mut bad_graph.values[phi.0] else {
        unreachable!()
    };
    inputs.pop();
    assert!(!valid(&source, &bad_graph, &ids));
}

#[test]
fn later_definition_is_unavailable_at_earlier_substituted_reads() {
    let source = straight(
        vec![set(2, r(0)), set(3, Expr::load(r(0), Width::U8))],
        r(3),
    );
    let (graph, mut ids) = graph(&source);
    let root = input(&graph, 0, 0);
    let copy = assignment(&graph, 0, 0);
    ids[root.0] = copy;
    assert!(!valid(&source, &graph, &ids));
}

#[test]
fn higher_numeric_representatives_are_accepted_when_available() {
    let source = straight(
        vec![set(2, r(0)), set(3, Expr::load(r(2), Width::U8))],
        r(3),
    );
    let (mut graph, _) = graph(&source);
    let old_root = input(&graph, 0, 0);
    let old_copy = assignment(&graph, 0, 0);
    let remap = |value: ValueId| {
        if value == old_root {
            old_copy
        } else if value == old_copy {
            old_root
        } else {
            value
        }
    };
    graph.values.swap(old_root.0, old_copy.0);
    for definition in &mut graph.values {
        if let Definition::Phi { inputs, .. } = definition {
            for input in inputs {
                input.value = remap(input.value);
            }
        }
    }
    for block in &mut graph.blocks {
        for phi in &mut block.phis {
            *phi = remap(*phi);
        }
        for point in &mut block.points {
            point.definition = point.definition.map(remap);
            for read in &mut point.reads {
                read.value = remap(read.value);
            }
        }
        for exit in &mut block.exit_values {
            exit.value = remap(exit.value);
        }
    }
    let root = input(&graph, 0, 0);
    let copy = assignment(&graph, 0, 0);
    assert!(root.0 > copy.0);
    let mut ids: Vec<_> = (0..graph.values.len()).map(ValueId).collect();
    ids[copy.0] = root;
    assert!(valid(&source, &graph, &ids));
}

#[test]
fn availability_uses_all_cfg_paths_and_source_order_including_virtual_entry() {
    let source = diamond(true);
    let left = source.cfg().block_at(1).unwrap();
    let join = source.cfg().block_at(3).unwrap();
    let mut availability = Availability {
        source: &source,
        origins: vec![
            Origin::Assignment(left, 0),
            Origin::Phi(join),
            Origin::Initial,
        ],
        avoiding: BTreeMap::new(),
    };
    let mut budget = Budget(ssa::MAX_WORK);
    assert_eq!(
        availability.at(ValueId(0), Some((left, 0)), &mut budget),
        Some(false)
    );
    assert_eq!(
        availability.at(ValueId(0), Some((left, 1)), &mut budget),
        Some(true)
    );
    // One branch bypasses the definition before reaching the join.
    assert_eq!(
        availability.at(ValueId(0), Some((join, 0)), &mut budget),
        Some(false)
    );
    assert_eq!(
        availability.at(ValueId(1), Some((left, 1)), &mut budget),
        Some(false)
    );
    assert_eq!(
        availability.at(ValueId(1), Some((join, 0)), &mut budget),
        Some(true)
    );
    assert_eq!(availability.at(ValueId(0), None, &mut budget), Some(false));
    assert_eq!(availability.at(ValueId(2), None, &mut budget), Some(true));
}

#[test]
fn fresh_load_noncopy_and_opaque_anchors_support_following_real_copies() {
    for rhs in [Expr::load(r(0), Width::U64), Expr::Const(9), r(0)] {
        let source = straight(vec![set(2, rhs.clone()), set(3, r(2))], r(3));
        let (graph, mut ids) = graph(&source);
        let root = assignment(&graph, 0, 0);
        ids[assignment(&graph, 0, 1).0] = root;
        let opaque = if matches!(rhs, Expr::Register(_)) {
            BTreeSet::from([Site {
                instruction: 0,
                assignment: Some(0),
            }])
        } else {
            BTreeSet::new()
        };
        assert!(validate(&source, &graph, &ids, &opaque).is_some());
        assert!(super::super::aliases(&source, &graph, &opaque).is_some());
    }
}

#[test]
fn loop_phis_must_keep_the_virtual_initial_edge_and_changing_load_versions() {
    let source = self::source(vec![
        ins(
            0,
            vec![set(2, Expr::load(r(0), Width::U64)), set(3, r(2))],
            Control::Branch {
                condition: r(7),
                target: 0,
            },
        ),
        ins(1, vec![], Control::Return(r(3))),
    ]);
    let (graph, _) = graph(&source);
    let ids = super::super::aliases(&source, &graph, &BTreeSet::new()).unwrap();
    assert!(valid(&source, &graph, &ids));
    // R0's entry phi is invariant, but the load in the same block is fresh
    // on each execution. The initial edge cannot supply that load result.
    let phi = input(&graph, 0, 0);
    let loaded = assignment(&graph, 0, 0);
    let mut bad = ids.clone();
    let old = bad[phi.0];
    for root in &mut bad {
        if *root == old {
            *root = loaded;
        }
    }
    assert!(!valid(&source, &graph, &bad));

    let source = self::source(vec![
        ins(
            0,
            vec![set(2, Expr::load(r(0), Width::U64))],
            Control::Jump(1),
        ),
        ins(
            1,
            vec![set(3, r(2)), set(2, Expr::load(r(0), Width::U64))],
            Control::Branch {
                condition: r(7),
                target: 1,
            },
        ),
        ins(2, vec![], Control::Return(r(3))),
    ]);
    let (graph, mut ids) = self::graph(&source);
    let phi = input(&graph, 1, 0);
    let first_load = assignment(&graph, 0, 0);
    ids[phi.0] = first_load;
    ids[assignment(&graph, 1, 0).0] = first_load;
    assert!(!valid(&source, &graph, &ids));
    let verified = super::super::aliases(&source, &graph, &BTreeSet::new()).unwrap();
    assert_eq!(verified[phi.0], phi);
    assert_eq!(verified[assignment(&graph, 1, 0).0], phi);
}

#[test]
fn ungrounded_equations_cannot_prove_a_disconnected_class_member() {
    let source = straight(
        vec![],
        Expr::binary(crate::model::ir::BinaryOp::Add, r(0), r(1)),
    );
    let (mut graph, mut ids) = graph(&source);
    let phi = graph.blocks[0].points[0].reads[0].value;
    let anchor = graph
        .values
        .iter()
        .position(|d| matches!(d, Definition::Initial { register: Reg(1) }))
        .unwrap();
    // Exercise the class-equation check directly, in addition to the public
    // SSA boundary: this fabricated self-equation has no anchor dependency.
    let Definition::Phi { inputs, .. } = &mut graph.values[phi.0] else {
        unreachable!()
    };
    inputs[0].value = phi;
    ids[phi.0] = ValueId(anchor);
    assert!(
        validate_checked(
            &source,
            &graph,
            &ids,
            &BTreeSet::new(),
            &mut Budget(ssa::MAX_WORK)
        )
        .is_none()
    );
    assert!(!valid(&source, &graph, &ids));
}

#[test]
fn work_exhaustion_declines_without_a_partial_class_result() {
    let source = straight(vec![set(2, r(0))], r(2));
    let (graph, mut ids) = graph(&source);
    ids[assignment(&graph, 0, 0).0] = input(&graph, 0, 0);
    assert!(validate_checked(&source, &graph, &ids, &BTreeSet::new(), &mut Budget(0)).is_none());
}
