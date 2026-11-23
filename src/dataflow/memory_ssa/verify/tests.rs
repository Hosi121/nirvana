use super::*;
#[path = "query_tests.rs"]
mod query_tests;
use crate::model::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Reg, Width};
fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
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
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn fixture() -> (Program, SsaFunction, Analysis) {
    // Entry can be revisited. Both branches and the initial edge must remain.
    let source = Program::new(
        0,
        4,
        vec![
            ins(
                0,
                vec![set(2, Expr::load(r(0), Width::U64))],
                Control::Branch {
                    condition: r(3),
                    target: 3,
                },
            ),
            ins(1, vec![store(r(0), r(2))], Control::Jump(4)),
            ins(3, vec![store(r(0), Expr::Const(7))], Control::Jump(4)),
            ins(
                4,
                vec![set(3, Expr::Const(0))],
                Control::Branch {
                    condition: r(1),
                    target: 0,
                },
            ),
            ins(5, vec![], Control::Return(Expr::load(r(0), Width::U64))),
        ],
    )
    .unwrap();
    let registers = SsaFunction::build(&source).unwrap();
    let candidate = analyze(&source, &registers).unwrap();
    (source, registers, candidate)
}
#[test]
fn graph_check_keeps_entry_backedges_and_accepts_renumbered_generations() {
    let (source, registers, mut candidate) = fixture();
    let evidence = validate_graph(&source, &registers, &candidate).unwrap();
    assert_eq!(candidate.graph_evidence(), Some(&evidence));
    assert_eq!(evidence.blocks, source.cfg().reachable_blocks().len());
    assert_eq!(evidence.accesses, 4);
    let count = candidate.definitions.len();
    let rename = |id: &mut MemoryId| id.0 = count - 1 - id.0;
    for definition in &mut candidate.definitions {
        match definition {
            Definition::Initial => {}
            Definition::Phi { inputs, .. } => {
                inputs.reverse();
                for input in inputs {
                    rename(&mut input.memory);
                }
            }
            Definition::Store { previous, .. } | Definition::Opaque { previous, .. } => {
                rename(previous)
            }
        }
    }
    candidate.definitions.reverse();
    for access in &mut candidate.accesses {
        rename(&mut access.incoming);
        if let Some(id) = &mut access.definition {
            rename(id);
        }
    }
    for block in &mut candidate.blocks {
        rename(&mut block.entry);
        rename(&mut block.exit);
        for event in &mut block.events {
            if let Event::Effect(id) = event {
                rename(id);
            }
        }
    }
    candidate.blocks.reverse();
    assert_eq!(
        validate_graph(&source, &registers, &candidate).unwrap(),
        evidence
    );
}
#[test]
fn graph_check_rejects_missing_edges_generation_changes_and_unclaimed_members() {
    for mutation in 0..10 {
        let (source, registers, mut candidate) = fixture();
        let entry = candidate
            .blocks
            .iter()
            .find(|b| b.start == 0)
            .unwrap()
            .entry;
        match mutation {
            0 => {
                if let Definition::Phi { inputs, .. } = &mut candidate.definitions[entry.0] {
                    inputs.retain(|i| i.predecessor.is_some());
                }
            }
            1 => {
                if let Definition::Phi { inputs, .. } = &mut candidate.definitions[entry.0] {
                    inputs.retain(|i| i.predecessor.is_none());
                }
            }
            2 => {
                if let Definition::Phi { inputs, .. } = &mut candidate.definitions[entry.0] {
                    inputs[0].memory = entry;
                }
            }
            3 => candidate.accesses[0].incoming = MemoryId(0),
            4 => candidate.accesses[0]
                .source
                .path
                .push(address_identity::PathEdge::Left),
            5 => candidate.accesses[0].definition = Some(entry),
            6 => {
                let b = candidate
                    .blocks
                    .iter_mut()
                    .find(|b| !b.events.is_empty())
                    .unwrap();
                b.events.pop();
            }
            7 => candidate.definitions.push(Definition::Initial),
            8 => candidate.blocks[0].exit = MemoryId(usize::MAX),
            9 => candidate.accesses.push(candidate.accesses[0].clone()),
            _ => unreachable!(),
        }
        assert!(
            matches!(
                validate_graph(&source, &registers, &candidate),
                Err(ValidationError::Invalid(_))
            ),
            "mutation {mutation}"
        );
    }
}
#[test]
fn graph_check_binds_nested_addresses_lazy_arms_rhs_reads_and_commit_order() {
    let load = |value| Expr::load(value, Width::U64);
    let source = Program::new(
        0,
        4,
        vec![ins(
            0,
            vec![store(
                load(r(0)),
                Expr::select(load(r(1)), load(r(2)), load(r(3))),
            )],
            Control::Return(load(r(0))),
        )],
    )
    .unwrap();
    let registers = SsaFunction::build(&source).unwrap();
    let original = analyze(&source, &registers).unwrap();
    validate_graph(&source, &registers, &original).unwrap();
    assert_eq!(original.accesses.len(), 6);
    for (a, b) in [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)] {
        let mut candidate = original.clone();
        candidate.blocks[0].events.swap(a, b);
        assert!(validate_graph(&source, &registers, &candidate).is_err());
    }
    let mut candidate = original.clone();
    let commit = candidate.accesses[4].definition.unwrap();
    candidate.accesses[3].incoming = commit;
    assert!(validate_graph(&source, &registers, &candidate).is_err());
}
#[test]
fn graph_check_retains_explicit_effects_at_their_phases() {
    let source = Program::new(
        0,
        4,
        vec![ins(
            0,
            vec![set(2, Expr::load(r(0), Width::U64))],
            Control::Return(Expr::binary(
                BinaryOp::Add,
                r(2),
                Expr::load(r(1), Width::U64),
            )),
        )],
    )
    .unwrap();
    let registers = SsaFunction::build(&source).unwrap();
    let effects = [
        Effect {
            instruction: 0,
            phase: Phase::Before,
            kind: EffectKind::CallStack,
        },
        Effect {
            instruction: 0,
            phase: Phase::After,
            kind: EffectKind::Call,
        },
    ];
    let candidate = analyze_with_effects(&source, &registers, &effects, &BTreeSet::new()).unwrap();
    let facts =
        address_identity::ordered_memory_addresses(&source, &registers, &BTreeSet::new()).unwrap();
    let check = |c: &Analysis| {
        graph_with_facts(
            &source,
            &registers,
            c,
            &effects,
            &facts.accesses,
            &facts.forms,
        )
    };
    assert_eq!(check(&candidate).unwrap().opaque_effects, 2);
    assert!(validate_graph(&source, &registers, &candidate).is_err());
    for mutation in 0..3 {
        let mut bad = candidate.clone();
        match mutation {
            0 => {
                bad.blocks[0].events.remove(0);
            }
            1 => {
                let n = bad.blocks[0].events.len();
                bad.blocks[0].events.swap(0, n - 1);
            }
            2 => {
                if let Definition::Opaque { effect, .. } = bad
                    .definitions
                    .iter_mut()
                    .find(|d| matches!(d, Definition::Opaque { .. }))
                    .unwrap()
                {
                    effect.kind = EffectKind::StringMove;
                }
            }
            _ => unreachable!(),
        }
        assert!(check(&bad).is_err());
    }
}

#[test]
fn graph_check_bounds_candidate_storage_and_keeps_query_unavailability_separate() {
    let (source, registers, original) = fixture();
    let mut candidate = original.clone();
    candidate.blocks[0]
        .events
        .resize(MAX_MEMBERS, Event::Access(0));
    assert!(matches!(
        validate_graph(&source, &registers, &candidate),
        Err(ValidationError::Unavailable(_))
    ));
    candidate = original.clone();
    candidate.queries = Err("query work limit".into());
    assert_eq!(
        validate_graph(&source, &registers, &candidate).unwrap(),
        *original.graph_evidence().unwrap()
    );
    // Candidate coverage is an additional layer, outside this graph-only API.
    candidate.queries = Ok(Vec::new());
    assert!(validate_graph(&source, &registers, &candidate).is_ok());
}
