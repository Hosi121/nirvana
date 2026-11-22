use super::*;
use nirvana::address_identity::{Operand as SourceOperand, PathEdge};
use nirvana::middle_ir::LoadFlow;

fn last_load(facts: &nirvana::middle_ir::MemoryFacts<'_>) -> nirvana::middle_ir::ValueId {
    facts.loads().last().unwrap().value
}

#[test]
fn partial_stores_reconstruct_unanimous_bytes_and_link_to_mir_rhs_values() {
    let source = one(
        vec![
            store(r(0), Width::U64, b(B::Add, c(0x8877665544332211), c(0))),
            store(b(B::Add, r(0), c(2)), Width::U16, c(0xbbaa)),
        ],
        Control::Return(Expr::load(b(B::Add, r(0), c(1)), Width::U32)),
    );
    let middle = Function::from_low(&source).unwrap();
    let facts = middle.memory_facts().unwrap();
    assert!(std::ptr::eq(facts.function(), &middle));
    let load = last_load(&facts);
    assert_eq!(facts.constant_load(load), Some(0x55bbaa22));
    let LoadFlow::Reaching { candidates, .. } = facts.flow(load).unwrap() else {
        panic!()
    };
    assert_eq!(candidates.len(), 2);
    for candidate in candidates {
        let writer = facts.store(candidate.definition).unwrap();
        assert_eq!(writer.site.instruction, 0);
        assert!(writer.constant.is_some());
        let Statement::Store { value, address, .. } =
            &middle.blocks()[0].steps[0].statements[writer.site.assignment.unwrap()]
        else {
            panic!()
        };
        assert_eq!(
            (writer.value, writer.address),
            (value.result, address.result)
        );
    }
    for pointer in [4096, 4104, 4112] {
        let input = vec![pointer, 0, 0, 0, 0, 0, 0, 0];
        assert_eq!(
            source
                .run_with_memory(&input, 4096, &[0; 32], 1)
                .unwrap()
                .status,
            nirvana::ir::RunStatus::Returned(0x55bbaa22)
        );
    }
}

#[test]
fn scalar_store_facts_follow_ssa_versions_across_reused_machine_storage() {
    let source = one(
        vec![
            set(1, c(0x12345678)),
            store(r(0), Width::U32, r(1)),
            set(1, c(0)),
            store(b(B::Add, r(0), c(1)), Width::U8, r(1)),
        ],
        Control::Return(Expr::load(r(0), Width::U32)),
    );
    let middle = Function::from_low(&source).unwrap();
    let facts = middle.memory_facts().unwrap();
    assert_eq!(
        facts.stores().map(|s| s.constant).collect::<Vec<_>>(),
        vec![Some(0x12345678), Some(0)]
    );
    assert_eq!(facts.constant_load(last_load(&facts)), Some(0x12340078));
    compare(
        &source,
        &[vec![4096, u64::MAX, 0, 0, 0, 0, 0, 0]],
        &[0; 32],
        &[0, 1, 2],
    );
}

#[test]
fn nested_address_and_lazy_loads_have_distinct_exact_source_paths() {
    let source = one(
        vec![store(
            Expr::load(Expr::load(r(0), Width::U64), Width::U64),
            Width::U64,
            Expr::select(
                Expr::load(r(1), Width::U8),
                Expr::load(r(0), Width::U64),
                Expr::load(r(1), Width::U64),
            ),
        )],
        Control::Return(c(0)),
    );
    let middle = Function::from_low(&source).unwrap();
    let facts = middle.memory_facts().unwrap();
    assert_eq!(facts.loads().count(), 5);
    assert_eq!(facts.stores().count(), 1);
    assert_eq!(facts.analysis().accesses().len(), 6);
    let paths: Vec<_> = facts
        .loads()
        .map(|l| {
            let a = &facts.analysis().accesses()[l.access.unwrap()].source;
            assert_eq!(a.width, l.width);
            assert_eq!(a.site, l.origin.site);
            (a.operand, a.path.clone())
        })
        .collect();
    for path in [
        (
            SourceOperand::Destination,
            vec![PathEdge::Address, PathEdge::Address],
        ),
        (SourceOperand::Destination, vec![PathEdge::Address]),
        (SourceOperand::Value, vec![PathEdge::Condition]),
        (SourceOperand::Value, vec![PathEdge::Taken]),
        (SourceOperand::Value, vec![PathEdge::NotTaken]),
    ] {
        assert!(paths.contains(&path), "{path:?}");
    }
    let store = facts.stores().next().unwrap();
    let own_definition = facts.analysis().accesses()[store.access.unwrap()]
        .definition
        .unwrap();
    for load in facts.loads() {
        let LoadFlow::Reaching {
            incoming,
            candidates,
        } = facts.flow(load.value).unwrap()
        else {
            panic!()
        };
        assert_ne!(incoming, own_definition);
        assert!(candidates.iter().all(|c| c.definition != own_definition));
    }
}

#[test]
fn store_rhs_reads_precommit_memory_and_unknown_values_remain_unknown() {
    let source = one(
        vec![
            store(r(0), Width::U64, c(17)),
            store(
                r(0),
                Width::U64,
                b(B::Add, Expr::load(r(0), Width::U64), c(1)),
            ),
        ],
        Control::Return(Expr::load(r(0), Width::U64)),
    );
    let middle = Function::from_low(&source).unwrap();
    let facts = middle.memory_facts().unwrap();
    let rhs = facts
        .loads()
        .find(|l| l.origin.site.assignment == Some(1))
        .unwrap();
    assert_eq!(facts.constant_load(rhs.value), Some(17));
    let LoadFlow::Reaching { candidates, .. } = facts.flow(rhs.value).unwrap() else {
        panic!()
    };
    assert!(
        candidates
            .iter()
            .all(|c| facts.store(c.definition).unwrap().site.assignment == Some(0))
    );
    assert_eq!(facts.constant_load(last_load(&facts)), None);
    assert_eq!(
        source
            .run_with_memory(&[4096, 0, 0, 0, 0, 0, 0, 0], 4096, &[0; 32], 1)
            .unwrap()
            .status,
        nirvana::ir::RunStatus::Returned(18)
    );
}

#[test]
fn may_alias_writes_require_agreement_across_every_possible_source_byte() {
    for (value, expected) in [(0x1111, Some(0x11111111)), (0x2222, None)] {
        let source = one(
            vec![
                store(r(0), Width::U64, c(0x1111111111111111)),
                store(r(1), Width::U16, c(value)),
            ],
            Control::Return(Expr::load(r(0), Width::U32)),
        );
        let middle = Function::from_low(&source).unwrap();
        let facts = middle.memory_facts().unwrap();
        assert_eq!(facts.constant_load(last_load(&facts)), expected);
        for p in 4096..=4104 {
            for q in 4096..=4126 {
                let report = source
                    .run_with_memory(&[p, q, 0, 0, 0, 0, 0, 0], 4096, &[7; 32], 1)
                    .unwrap();
                if let Some(expected) = expected {
                    assert_eq!(report.status, nirvana::ir::RunStatus::Returned(expected));
                }
            }
        }
    }
}

#[test]
fn memory_phis_loops_and_unreachable_loads_keep_their_distinct_meaning() {
    let source = Program::new(
        0,
        8,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![store(r(0), Width::U64, c(7))],
                control: Control::Branch {
                    condition: r(1),
                    target: 3,
                },
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![store(r(0), Width::U64, c(7))],
                control: Control::Next,
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![set(2, b(B::Add, r(2), c(1)))],
                control: Control::Branch {
                    condition: b(B::Ult, r(2), c(3)),
                    target: 1,
                },
            },
            IrInstruction {
                address: 3,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::load(r(0), Width::U64)),
            },
            IrInstruction {
                address: 9,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::load(r(1), Width::U8)),
            },
        ],
    )
    .unwrap();
    let middle = Function::from_low(&source).unwrap();
    let facts = middle.memory_facts().unwrap();
    for load in facts.loads() {
        if load.origin.site.instruction == 9 {
            assert!(matches!(
                facts.flow(load.value).unwrap(),
                LoadFlow::Unreachable
            ));
            assert_eq!(facts.constant_load(load.value), None);
        } else {
            assert_eq!(facts.constant_load(load.value), Some(7));
            let LoadFlow::Reaching { incoming, .. } = facts.flow(load.value).unwrap() else {
                panic!()
            };
            assert!(matches!(
                facts.analysis().definitions()[incoming.0],
                nirvana::memory_ssa::Definition::Phi { .. }
            ));
        }
    }
    assert!(facts.flow(nirvana::middle_ir::ValueId(usize::MAX)).is_err());
    compare(
        &source,
        &[
            vec![4096, 0, 0, 0, 0, 0, 0, 0],
            vec![4096, 1, 0, 0, 0, 0, 0, 0],
        ],
        &[0; 32],
        &(0..=12).collect::<Vec<_>>(),
    );
}

#[test]
fn query_resource_failure_is_unavailable_not_an_empty_writer_set() {
    let mut assignments = Vec::new();
    for _ in 0..300 {
        assignments.push(store(r(1), Width::U8, c(0)));
    }
    for _ in 0..901 {
        assignments.push(set(3, Expr::load(r(0), Width::U8)));
    }
    let source = one(assignments, Control::Return(c(0)));
    let middle = Function::from_low(&source).unwrap();
    let facts = middle.memory_facts().unwrap();
    assert!(facts.analysis().queries().is_err());
    for load in facts.loads() {
        assert!(matches!(
            facts.flow(load.value).unwrap(),
            LoadFlow::Unavailable(_)
        ));
        assert_eq!(facts.constant_load(load.value), None);
    }
}
