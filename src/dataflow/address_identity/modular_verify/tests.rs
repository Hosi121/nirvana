use super::*;
use crate::model::ir::{Assignment, IrInstruction, Reg};

fn r(register: usize) -> Expr {
    Expr::Register(Reg(register))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn b(op: BinaryOp, a: Expr, d: Expr) -> Expr {
    Expr::binary(op, a, d)
}
fn load(address: Expr) -> Expr {
    Expr::load(address, Width::U8)
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Register(Reg(register)),
        value,
    }
}
fn instruction(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn straight(assignments: Vec<Assignment>, result: Expr) -> Program {
    Program::new(
        0,
        32,
        vec![instruction(0, assignments, Control::Return(result))],
    )
    .unwrap()
}
fn fixture(
    source: &Program,
    opaque: &BTreeSet<Site>,
) -> (SsaFunction, Vec<ValueId>, MemoryAddresses) {
    let graph = SsaFunction::build(source).unwrap();
    let aliases = super::super::aliases(source, &graph, opaque).unwrap();
    // Only fixture construction uses the producer; the checker never does.
    let candidate = super::super::collect::collect_memory(
        source,
        &graph,
        &aliases,
        &vec![64; graph.values.len()],
        opaque,
    )
    .unwrap();
    (graph, aliases, candidate)
}
fn copy(candidate: &MemoryAddresses) -> MemoryAddresses {
    MemoryAddresses {
        accesses: candidate.accesses.clone(),
        forms: candidate.forms.clone(),
        phi_values: candidate.phi_values.clone(),
    }
}

#[test]
fn opaque_declarations_bind_unreachable_source_without_requiring_a_live_ssa_point() {
    let source = Program::new(
        0,
        32,
        vec![
            instruction(0, vec![], Control::Jump(2)),
            instruction(1, vec![set(0, c(0))], Control::Next),
            instruction(2, vec![set(1, load(r(0)))], Control::Return(r(1))),
        ],
    )
    .unwrap();
    let opaque = BTreeSet::from([Site {
        instruction: 1,
        assignment: Some(0),
    }]);
    let (graph, aliases, candidate) = fixture(&source, &opaque);
    assert!(
        !graph
            .blocks
            .iter()
            .flat_map(|block| &block.points)
            .any(|p| opaque.contains(&p.site))
    );
    let proof = validate(&source, &graph, &aliases, &opaque, &candidate).unwrap();
    assert_eq!(proof.accesses, 1);
    for site in [
        Site {
            instruction: 1,
            assignment: None,
        },
        Site {
            instruction: 1,
            assignment: Some(1),
        },
        Site {
            instruction: 9,
            assignment: Some(0),
        },
    ] {
        let forged = BTreeSet::from([site]);
        assert!(validate(&source, &graph, &aliases, &forged, &candidate).is_err());
    }
}
fn rejects(
    source: &Program,
    graph: &SsaFunction,
    aliases: &[ValueId],
    opaque: &BTreeSet<Site>,
    candidate: &MemoryAddresses,
    mutate: impl FnOnce(&mut MemoryAddresses),
) {
    let mut bad = copy(candidate);
    mutate(&mut bad);
    let result = validate(source, graph, aliases, opaque, &bad);
    assert!(
        result.is_err(),
        "accepted false address candidate: {result:?}"
    );
}

#[test]
fn source_walker_covers_nested_reads_select_arms_control_and_store_order() {
    let source = straight(
        vec![
            set(2, load(load(r(0)))),
            Assignment {
                destination: Place::Memory {
                    address: b(BinaryOp::Add, r(0), load(r(1))),
                    width: Width::U32,
                },
                value: Expr::Select {
                    condition: Box::new(load(r(2))),
                    taken: Box::new(load(r(3))),
                    not_taken: Box::new(load(r(4))),
                },
            },
        ],
        load(r(5)),
    );
    let opaque = BTreeSet::new();
    let (graph, aliases, candidate) = fixture(&source, &opaque);
    let evidence = validate(&source, &graph, &aliases, &opaque, &candidate).unwrap();
    assert_eq!(evidence.accesses, 8);
    assert_eq!(evidence.accesses, candidate.accesses.len());
    assert!(candidate.forms.iter().any(Option::is_none));
    assert!(evidence.basis_evaluations > 0);
    for index in 0..candidate.accesses.len() {
        rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
            bad.accesses.remove(index);
            bad.forms.remove(index);
        });
        rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
            bad.accesses[index].path.push(PathEdge::Left);
        });
        rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
            bad.accesses[index].operand = Operand::Control;
            bad.accesses[index].site.instruction = 7;
        });
        rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
            bad.accesses[index].width = Width::U64;
        });
    }
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.accesses.swap(0, 1);
        bad.forms.swap(0, 1);
    });
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.accesses.push(bad.accesses[0].clone());
        bad.forms.push(bad.forms[0].clone());
    });
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.accesses[1].result = None;
    });
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.accesses[6].kind = AccessKind::Read;
    });
}

#[test]
fn modular_basis_rejects_missing_terms_offsets_signs_and_unmasked_shifts() {
    let source = straight(
        vec![
            set(2, b(BinaryOp::Add, r(0), c(u64::MAX))),
            set(
                3,
                load(b(BinaryOp::Sub, r(2), b(BinaryOp::Shl, r(1), c(65)))),
            ),
            set(
                4,
                load(b(BinaryOp::Add, r(0), b(BinaryOp::Mul, r(1), c(1 << 63)))),
            ),
        ],
        c(0),
    );
    let opaque = BTreeSet::new();
    let (graph, aliases, candidate) = fixture(&source, &opaque);
    validate(&source, &graph, &aliases, &opaque, &candidate).unwrap();
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.forms[0].as_mut().unwrap().offset = 0;
    });
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.accesses[0].address = AddressShape::Unknown;
        bad.forms[0].as_mut().unwrap().terms.remove(1);
    });
    for coefficient in [0, 2, 1u64 << 63, u64::MAX] {
        rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
            bad.accesses[0].address = AddressShape::Unknown;
            bad.forms[0].as_mut().unwrap().terms[1].1 = coefficient;
        });
    }
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.forms[0].as_mut().unwrap().terms.swap(0, 1);
    });
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        let form = bad.forms[0].as_mut().unwrap();
        form.terms.push(form.terms[0]);
    });
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.accesses[0].address = AddressShape::Unknown;
        bad.forms[0].as_mut().unwrap().terms[0].0 = ValueId(graph.values.len());
    });
}

#[test]
fn cancelled_source_atoms_are_checked_even_beyond_the_form_term_limit() {
    let mut expression = c(9);
    for register in 0..24 {
        expression = b(
            BinaryOp::Add,
            expression,
            b(BinaryOp::Sub, r(register), r(register)),
        );
    }
    let source = straight(vec![set(30, load(expression))], c(0));
    let opaque = BTreeSet::new();
    let (graph, aliases, candidate) = fixture(&source, &opaque);
    assert_eq!(candidate.forms[0].as_ref().unwrap().terms.len(), 0);
    let evidence = validate(&source, &graph, &aliases, &opaque, &candidate).unwrap();
    assert!(evidence.source_atoms >= 24);
    assert!(evidence.basis_evaluations >= 25);
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.forms[0].as_mut().unwrap().offset = 10;
    });
}

#[test]
fn fresh_load_opaque_and_unsupported_assignment_results_stay_atoms() {
    let source = straight(
        vec![
            set(2, Expr::load(r(0), Width::U64)),
            set(3, Expr::load(r(0), Width::U64)),
            set(4, b(BinaryOp::And, r(0), c(0))),
            set(5, b(BinaryOp::Mul, b(BinaryOp::Sub, r(0), r(0)), r(1))),
            set(
                6,
                Expr::unary(
                    UnaryOp::Extract {
                        start: 0,
                        width: Width::U8,
                    },
                    r(0),
                ),
            ),
            set(7, c(42)),
            set(8, r(2)),
            set(9, load(r(8))),
            set(10, load(r(3))),
            set(11, load(r(4))),
            set(12, load(r(5))),
            set(13, load(r(6))),
            set(14, load(r(7))),
        ],
        c(0),
    );
    let opaque = BTreeSet::from([Site {
        instruction: 0,
        assignment: Some(5),
    }]);
    let (graph, aliases, candidate) = fixture(&source, &opaque);
    validate(&source, &graph, &aliases, &opaque, &candidate).unwrap();
    assert_ne!(candidate.forms[2], candidate.forms[3]);
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.accesses[3].address = AddressShape::Unknown;
        bad.forms[3] = bad.forms[2].clone();
    });
    for index in 4..8 {
        rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
            bad.accesses[index].address = AddressShape::Unknown;
            bad.forms[index] = Some(ModularAddress {
                offset: if index == 7 { 42 } else { 0 },
                terms: vec![],
            });
        });
    }
}

#[test]
fn raw_literal_grammar_and_constant_unary_semantics_match_the_producer() {
    let source = straight(
        vec![
            set(2, load(Expr::unary(UnaryOp::SignExtend(Width::U8), c(255)))),
            set(
                3,
                load(Expr::unary(
                    UnaryOp::Extract {
                        start: 64,
                        width: Width::U64,
                    },
                    c(u64::MAX),
                )),
            ),
            set(
                4,
                load(Expr::unary(
                    UnaryOp::Extract {
                        start: 0,
                        width: Width::U8,
                    },
                    b(BinaryOp::Sub, r(0), r(0)),
                )),
            ),
            set(5, load(b(BinaryOp::And, c(255), c(7)))),
            set(
                6,
                load(b(BinaryOp::Mul, b(BinaryOp::Add, c(1), c(1)), c(3))),
            ),
            set(7, load(b(BinaryOp::And, r(0), c(u64::MAX)))),
            // The left literal has priority. A new constant-folding rule
            // would wrongly expand this assignment instead of keeping its
            // fresh SSA result atom.
            set(8, b(BinaryOp::And, c(7), c(u64::MAX))),
            set(9, load(r(8))),
        ],
        c(0),
    );
    let opaque = BTreeSet::new();
    let (graph, aliases, candidate) = fixture(&source, &opaque);
    assert_eq!(candidate.forms[0].as_ref().unwrap().offset, u64::MAX);
    assert_eq!(candidate.forms[1].as_ref().unwrap().offset, 0);
    assert_eq!(candidate.forms[2].as_ref().unwrap().offset, 0);
    assert!(candidate.forms[3].is_none());
    assert_eq!(candidate.forms[4].as_ref().unwrap().offset, 6);
    assert_eq!(candidate.forms[6].as_ref().unwrap().terms.len(), 1);
    validate(&source, &graph, &aliases, &opaque, &candidate).unwrap();
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.forms[3] = Some(ModularAddress {
            offset: 7,
            terms: vec![],
        });
    });
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.accesses[6].address = AddressShape::Unknown;
        bad.forms[6] = Some(ModularAddress {
            offset: 7,
            terms: vec![],
        });
    });
}

#[test]
fn shape_flattening_and_conservative_unknown_forms_are_distinct() {
    let source = straight(
        vec![set(
            2,
            load(b(BinaryOp::Add, r(0), b(BinaryOp::Mul, r(1), c(8)))),
        )],
        c(0),
    );
    let opaque = BTreeSet::new();
    let (graph, aliases, candidate) = fixture(&source, &opaque);
    let mut unknown = copy(&candidate);
    unknown.accesses[0].address = AddressShape::Unknown;
    unknown.forms[0] = None;
    let evidence = validate(&source, &graph, &aliases, &opaque, &unknown).unwrap();
    assert_eq!(evidence.modular_forms, evidence.phi_inputs);
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.forms[0] = None;
    });
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        let AddressShape::Base {
            index: Some(index), ..
        } = &mut bad.accesses[0].address
        else {
            panic!()
        };
        index.stride = 4;
    });
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.accesses[0].address = AddressShape::Absolute(0);
    });
}

#[test]
fn phi_input_coverage_and_identities_are_checked_without_partial_evidence() {
    let source = Program::new(
        0,
        8,
        vec![
            instruction(
                0,
                vec![],
                Control::Branch {
                    condition: r(0),
                    // Address 1 is the fallthrough, address 2 the taken arm.
                    target: 2,
                },
            ),
            instruction(
                1,
                vec![set(2, b(BinaryOp::Add, r(1), c(4)))],
                Control::Jump(3),
            ),
            instruction(2, vec![set(2, r(1))], Control::Jump(3)),
            instruction(3, vec![set(3, load(r(2)))], Control::Return(r(3))),
        ],
    )
    .unwrap();
    let opaque = BTreeSet::new();
    let (graph, aliases, candidate) = fixture(&source, &opaque);
    let evidence = validate(&source, &graph, &aliases, &opaque, &candidate).unwrap();
    assert_eq!(
        evidence.phi_inputs,
        candidate.phi_values.as_ref().unwrap().len()
    );
    assert!(evidence.phi_inputs > 0);
    let first = *candidate
        .phi_values
        .as_ref()
        .unwrap()
        .keys()
        .next()
        .unwrap();
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.phi_values.as_mut().unwrap().remove(&first);
    });
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.phi_values
            .as_mut()
            .unwrap()
            .get_mut(&first)
            .unwrap()
            .offset ^= 1;
    });
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        bad.phi_values.as_mut().unwrap().insert(
            ValueId(graph.values.len()),
            ModularAddress {
                offset: 0,
                terms: vec![],
            },
        );
    });
    let mut unknown = copy(&candidate);
    unknown.phi_values = Err("producer work limit".into());
    let access_evidence = validate_accesses(&source, &graph, &aliases, &opaque, &unknown).unwrap();
    assert_eq!(access_evidence.accesses, candidate.accesses.len());
    assert_eq!(
        access_evidence.modular_forms,
        candidate.forms.iter().filter(|form| form.is_some()).count()
    );
    assert_eq!(access_evidence.phi_inputs, 0);
    assert!(
        validate(&source, &graph, &aliases, &opaque, &unknown)
            .unwrap_err()
            .starts_with("unavailable:")
    );
    assert!(
        check(
            &source,
            &graph,
            &aliases,
            &opaque,
            &candidate,
            Budget {
                work: 0,
                members: 0
            },
            true,
        )
        .unwrap_err()
        .starts_with("unavailable:")
    );
    unknown.forms[0].as_mut().unwrap().offset ^= 1;
    assert!(validate_accesses(&source, &graph, &aliases, &opaque, &unknown).is_err());
    let mut invalid_aliases = aliases.clone();
    invalid_aliases[0] = ValueId(graph.values.len());
    assert!(validate(&source, &graph, &invalid_aliases, &opaque, &candidate).is_err());
}

#[test]
fn entry_backedge_keeps_virtual_initial_and_previous_iteration_phi_atoms() {
    let source = Program::new(
        0,
        8,
        vec![
            instruction(
                0,
                vec![
                    set(2, b(BinaryOp::Add, r(2), c(8))),
                    set(3, load(b(BinaryOp::Add, r(0), r(2)))),
                ],
                Control::Branch {
                    condition: r(1),
                    // Re-enter address 0, or fall through to the return at 1.
                    target: 0,
                },
            ),
            instruction(1, vec![], Control::Return(r(3))),
        ],
    )
    .unwrap();
    let opaque = BTreeSet::new();
    let (graph, aliases, candidate) = fixture(&source, &opaque);
    let evidence = validate(&source, &graph, &aliases, &opaque, &candidate).unwrap();
    assert!(evidence.phi_inputs > 0);
    let phi = graph
        .values
        .iter()
        .find_map(|definition| match definition {
            Definition::Phi {
                register: Reg(2),
                inputs,
                ..
            } => Some(inputs),
            _ => None,
        })
        .unwrap();
    let initial = phi
        .iter()
        .find(|input| input.predecessor.is_none())
        .unwrap()
        .value;
    let backedge = phi
        .iter()
        .find(|input| input.predecessor == Some(0))
        .unwrap()
        .value;
    assert_ne!(initial, backedge);
    rejects(&source, &graph, &aliases, &opaque, &candidate, |bad| {
        let values = bad.phi_values.as_mut().unwrap();
        let previous = values[&initial].clone();
        values.insert(backedge, previous);
    });
}

#[test]
fn phi_basis_work_limit_keeps_checked_accesses_and_the_memory_graph() {
    const ATOMS: usize = 2000;
    fn cancelled(registers: &[usize]) -> Expr {
        if registers.len() == 1 {
            return b(BinaryOp::Sub, r(registers[0]), r(registers[0]));
        }
        let middle = registers.len() / 2;
        b(
            BinaryOp::Add,
            cancelled(&registers[..middle]),
            cancelled(&registers[middle..]),
        )
    }
    let expression = b(
        BinaryOp::Add,
        c(9),
        cancelled(&(0..ATOMS).collect::<Vec<_>>()),
    );
    let mut expression_nodes = 0;
    let mut expression_depth = 0;
    let mut pending = vec![(&expression, 1usize)];
    while let Some((expr, depth)) = pending.pop() {
        expression_nodes += 1;
        expression_depth = expression_depth.max(depth);
        match expr {
            Expr::Binary(_, a, b) => pending.extend([(&**a, depth + 1), (&**b, depth + 1)]),
            Expr::Const(_) | Expr::Register(_) => {}
            _ => panic!("unexpected cancellation fixture syntax"),
        }
    }
    assert_eq!((expression_nodes, expression_depth), (8001, 14));
    let source = Program::new(
        0,
        ATOMS + 2,
        vec![
            instruction(0, vec![set(ATOMS, expression)], Control::Jump(1)),
            instruction(
                1,
                vec![set(ATOMS + 1, load(c(4096)))],
                Control::Return(r(ATOMS)),
            ),
        ],
    )
    .unwrap();
    // The load's two nodes and the return's register give 8,004 source
    // expression nodes, inside the ordinary SSA node/depth/register budgets.
    assert!(expression_nodes + 3 < ssa::MAX_NODES);
    assert!(expression_depth < ssa::MAX_DEPTH);
    assert!(source.register_count() < ssa::MAX_REGISTERS);
    let opaque = BTreeSet::new();
    let (graph, aliases, candidate) = fixture(&source, &opaque);
    assert_eq!(graph.values.len(), 4005);
    assert_eq!(candidate.phi_values.as_ref().unwrap().len(), ATOMS + 1);
    assert_eq!(candidate.accesses.len(), 1);
    assert_eq!(candidate.forms[0].as_ref().unwrap().terms.len(), 0);
    // Producer maps cancel each pair immediately. The independent DAG keeps
    // the 2,000 source atoms: its 6,001 reachable scalar nodes need 2,001
    // evaluations, exceeding the fixed 8M work budget without a deep tree.
    let scalar_nodes = 3 * ATOMS + 1;
    let evaluation_work = (scalar_nodes + 1) * (ATOMS + 1);
    assert_eq!(evaluation_work, 12_010_002);
    assert!(evaluation_work > ssa::MAX_WORK);
    let reason = validate(&source, &graph, &aliases, &opaque, &candidate).unwrap_err();
    assert!(reason.starts_with("unavailable: modular address work budget"));
    let (checked, evidence) =
        super::super::checked_memory_addresses(&source, &graph, &opaque).unwrap();
    assert_eq!(checked.accesses, candidate.accesses);
    assert_eq!(checked.forms, candidate.forms);
    assert_eq!(checked.phi_values.as_ref().unwrap_err(), &reason);
    assert_eq!(evidence.accesses, 1);
    assert_eq!(evidence.modular_forms, 1);
    assert_eq!(evidence.phi_inputs, 0);
    assert!(!evidence.phi_checked);
    let memory = crate::dataflow::memory_ssa::analyze(&source, &graph).unwrap();
    let graph_evidence = memory.graph_evidence().unwrap();
    assert_eq!(
        (
            graph_evidence.blocks,
            graph_evidence.definitions,
            graph_evidence.accesses
        ),
        (2, 3, 1)
    );
    assert_eq!(memory.accesses().len(), 1);
    assert!(memory.queries().is_err());
    assert!(memory.query_certificates().is_empty());
    assert!(memory.query_evidence().is_none());
    assert!(!memory.address_evidence().phi_checked);
    println!(
        "phi fallback: {} source nodes, depth {expression_depth}, {} SSA values, {} producer phi values; {scalar_nodes} scalar DAG nodes, {evaluation_work} basis work; 1 checked access, 2 retained memory blocks, unavailable queries",
        expression_nodes + 3,
        graph.values.len(),
        candidate.phi_values.as_ref().unwrap().len(),
    );
}
