use super::*;

#[test]
fn coverage_certificates_are_closed_invariants_not_discovery_order_traces() {
    let (source, registers, mut candidate) = fixture();
    let original = validate(&source, &registers, &candidate).unwrap();
    assert_eq!(original.queries.as_ref(), candidate.query_evidence());
    candidate.queries.as_mut().unwrap().reverse();
    candidate.query_certificates.reverse();
    for proof in &mut candidate.query_certificates {
        proof.states.reverse();
    }
    assert_eq!(validate(&source, &registers, &candidate).unwrap(), original);

    // An intentionally coarse invariant may include every memory generation
    // and every writer. More possibilities lose precision but remain sound.
    for query in candidate.queries.as_mut().unwrap() {
        let read = &candidate.accesses[query.access];
        let mask = ((1u16 << read.source.width.bytes()) - 1) as u8;
        query.address_widened = read.address.is_some();
        query.candidates = candidate
            .definitions
            .iter()
            .enumerate()
            .filter_map(|(n, def)| {
                let (sources, unknown) = match def {
                    Definition::Initial | Definition::Opaque { .. } => ([0; 8], mask),
                    Definition::Store { access, .. } => {
                        let mut sources = [0; 8];
                        sources[..read.source.width.bytes()].fill(
                            ((1u16 << candidate.accesses[*access].source.width.bytes()) - 1) as u8,
                        );
                        (sources, 0)
                    }
                    Definition::Phi { .. } => return None,
                };
                Some(Clobber {
                    definition: MemoryId(n),
                    alias: Alias::May,
                    byte_mask: mask,
                    byte_sources: sources,
                    unknown_bytes: unknown,
                })
            })
            .collect();
    }
    for proof in &mut candidate.query_certificates {
        let width = candidate.accesses[proof.access].source.width;
        proof.states = (0..candidate.definitions.len())
            .map(|n| QueryState {
                memory: MemoryId(n),
                address: None,
                byte_mask: ((1u16 << width.bytes()) - 1) as u8,
            })
            .collect();
    }
    let result = validate(&source, &registers, &candidate).unwrap();
    assert_eq!(
        result.queries.unwrap().queries,
        original.queries.unwrap().queries
    );
}

#[test]
fn missing_reads_writers_predecessors_and_source_positions_are_rejected() {
    for mutation in 0..14 {
        let (source, registers, mut candidate) = fixture();
        match mutation {
            0 => {
                candidate.queries.as_mut().unwrap().pop();
            }
            1 => {
                candidate.query_certificates.pop();
            }
            2 => {
                candidate.queries.as_mut().unwrap()[0].candidates.clear();
            }
            3 => {
                candidate.query_certificates[0].states.clear();
            }
            4 => {
                candidate.query_certificates[0].states[0].memory = MemoryId(usize::MAX);
            }
            5 => {
                candidate.query_certificates[0].states[0].byte_mask = 0;
            }
            6 => {
                let state = candidate.query_certificates[0].states[0].clone();
                candidate.query_certificates[0].states.push(state);
            }
            7 => {
                candidate.queries.as_mut().unwrap()[0].access = usize::MAX;
            }
            8 => {
                let query = candidate.queries.as_mut().unwrap().last_mut().unwrap();
                let n = query
                    .candidates
                    .iter()
                    .position(|c| {
                        matches!(
                            candidate.definitions[c.definition.0],
                            Definition::Store { .. }
                        )
                    })
                    .unwrap();
                query.candidates.remove(n);
            }
            9 => {
                let query = candidate.queries.as_mut().unwrap().last_mut().unwrap();
                let writer = query
                    .candidates
                    .iter_mut()
                    .find(|c| {
                        matches!(
                            candidate.definitions[c.definition.0],
                            Definition::Store { .. }
                        )
                    })
                    .unwrap();
                writer.byte_sources[0] = 2;
            }
            10 => {
                candidate.query_certificates[0].states[0].address =
                    Some(address_identity::ModularAddress {
                        offset: 0,
                        terms: vec![(crate::dataflow::ssa::ValueId(usize::MAX), 1)],
                    });
            }
            11 => {
                let state = &mut candidate.query_certificates[0].states[0];
                state.address = Some(address_identity::ModularAddress {
                    offset: 0,
                    terms: vec![(crate::dataflow::ssa::ValueId(0), 0)],
                });
            }
            12 => {
                candidate.query_certificates[0].access = usize::MAX;
            }
            13 => {
                let query = candidate.queries.as_mut().unwrap().last_mut().unwrap();
                let store = query
                    .candidates
                    .iter_mut()
                    .find(|c| {
                        matches!(
                            candidate.definitions[c.definition.0],
                            Definition::Store { .. }
                        )
                    })
                    .unwrap();
                store.unknown_bytes = store.byte_mask;
            }
            _ => unreachable!(),
        }
        assert!(
            matches!(
                validate(&source, &registers, &candidate),
                Err(ValidationError::Invalid(_))
            ),
            "mutation {mutation}"
        );
    }
}

fn byte_store_read(write_address: Expr, read_width: Width) -> (Program, SsaFunction, Analysis) {
    let source = Program::new(
        0,
        4,
        vec![
            ins(
                0,
                vec![Assignment {
                    destination: Place::Memory {
                        address: write_address,
                        width: Width::U8,
                    },
                    value: Expr::Const(0xaa),
                }],
                Control::Next,
            ),
            ins(1, vec![], Control::Return(Expr::load(r(0), read_width))),
        ],
    )
    .unwrap();
    let registers = SsaFunction::build(&source).unwrap();
    let analysis = analyze(&source, &registers).unwrap();
    (source, registers, analysis)
}
#[test]
fn partial_and_may_alias_stores_cannot_erase_unwritten_initial_bytes() {
    for may_alias in [false, true] {
        let (source, registers, mut candidate) = byte_store_read(
            r(if may_alias { 1 } else { 0 }),
            if may_alias { Width::U8 } else { Width::U64 },
        );
        validate(&source, &registers, &candidate).unwrap();
        let query = &mut candidate.queries.as_mut().unwrap()[0];
        query
            .candidates
            .retain(|c| !matches!(candidate.definitions[c.definition.0], Definition::Initial));
        if !may_alias {
            let store = &mut query.candidates[0];
            store.byte_mask = 255;
            store.byte_sources.fill(1);
        }
        assert!(validate(&source, &registers, &candidate).is_err());
        let actual = source
            .execute_with_memory(&[64, 80, 0, 0], 0, &[0x55; 128], 8)
            .unwrap();
        assert_eq!(
            actual.value,
            if may_alias { 0x55 } else { 0x55555555555555aa }
        );
        assert_ne!(
            actual.value,
            if may_alias { 0xaa } else { 0xaaaaaaaaaaaaaaaa }
        );
        // Dropping the initial state as well cannot bypass the closure check.
        candidate.query_certificates[0]
            .states
            .retain(|s| !matches!(candidate.definitions[s.memory.0], Definition::Initial));
        assert!(validate(&source, &registers, &candidate).is_err());
    }
}

#[test]
fn growing_loop_locations_need_a_closed_widened_state_not_an_iteration_cutoff() {
    let source = Program::new(
        0,
        4,
        vec![
            ins(
                0,
                vec![
                    set(2, Expr::load(r(0), Width::U64)),
                    store(r(0), Expr::Const(7)),
                    set(0, Expr::binary(BinaryOp::Add, r(0), Expr::Const(8))),
                ],
                Control::Branch {
                    condition: r(1),
                    target: 0,
                },
            ),
            ins(1, vec![], Control::Return(r(2))),
        ],
    )
    .unwrap();
    let registers = SsaFunction::build(&source).unwrap();
    let mut candidate = analyze(&source, &registers).unwrap();
    let evidence = validate(&source, &registers, &candidate).unwrap();
    assert!(
        candidate.query_certificates[0]
            .states
            .iter()
            .any(|s| s.address.is_none())
    );
    assert!(evidence.queries.unwrap().states > 16);
    candidate.query_certificates[0]
        .states
        .retain(|s| s.address.is_some());
    assert!(validate(&source, &registers, &candidate).is_err());
}

#[test]
fn query_unavailability_retains_only_checked_graph_evidence() {
    let (source, registers, mut candidate) = fixture();
    candidate.queries = Err("work limit".into());
    assert!(validate(&source, &registers, &candidate).is_err());
    candidate.query_certificates.clear();
    assert_eq!(
        validate(&source, &registers, &candidate).unwrap().queries,
        None
    );
    candidate.queries = Ok(Vec::new());
    assert!(validate(&source, &registers, &candidate).is_err());
}

#[test]
fn oversized_certificates_are_unavailable_before_following_their_states() {
    let (source, registers, mut candidate) = fixture();
    let state = candidate.query_certificates[0].states[0].clone();
    candidate.query_certificates[0]
        .states
        .resize(MAX_MEMBERS, state);
    assert!(matches!(
        validate(&source, &registers, &candidate),
        Err(ValidationError::Unavailable(_))
    ));
}
