use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::process::{Command, Stdio};

use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus,
    Width,
};
use nirvana::memory_ssa::{self, Alias, Analysis, Definition, MemoryId};
use nirvana::ssa::SsaFunction;

use crate::support::ir::c;
use crate::support::ir::r;
fn add(a: Expr, n: u64) -> Expr {
    Expr::binary(BinaryOp::Add, a, c(n))
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn store(address: Expr, width: Width, tag: u8) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value: c(u64::from(tag) * 0x0101010101010101),
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
fn analyze(instructions: Vec<IrInstruction>) -> (Program, Analysis) {
    let program = Program::new(instructions[0].address, 4, instructions).unwrap();
    let graph = SsaFunction::build(&program).unwrap();
    let before = program.instructions().to_vec();
    let result = memory_ssa::analyze(&program, &graph).unwrap();
    assert_eq!(program.instructions(), before);
    (program, result)
}
fn writers(analysis: &Analysis, instruction: u64) -> BTreeSet<u64> {
    contributions(analysis, instruction).into_keys().collect()
}
fn contributions(analysis: &Analysis, instruction: u64) -> BTreeMap<u64, u8> {
    let access = analysis
        .accesses()
        .iter()
        .position(|a| a.source.site.instruction == instruction && a.source.kind == AccessKind::Read)
        .unwrap();
    analysis
        .queries()
        .as_ref()
        .unwrap()
        .iter()
        .find(|q| q.access == access)
        .unwrap()
        .candidates
        .iter()
        .map(|c| {
            (
                match &analysis.definitions()[c.definition.0] {
                    Definition::Initial => 0,
                    Definition::Store { access, .. } => {
                        analysis.accesses()[*access].source.site.instruction
                    }
                    other => panic!("unexpected candidate: {other:?}"),
                },
                c.byte_mask,
            )
        })
        .collect()
}

#[test]
fn disjoint_full_partial_and_unknown_alias_writes_keep_the_right_history() {
    let (_, a) = analyze(vec![
        ins(100, vec![store(r(0), Width::U64, 1)], Control::Next),
        ins(101, vec![store(add(r(0), 8), Width::U64, 2)], Control::Next),
        ins(
            102,
            vec![set(2, Expr::load(r(0), Width::U64))],
            Control::Next,
        ),
        ins(103, vec![store(r(1), Width::U8, 3)], Control::Next),
        ins(
            104,
            vec![set(2, Expr::load(r(0), Width::U64))],
            Control::Next,
        ),
        ins(105, vec![store(add(r(0), 7), Width::U16, 4)], Control::Next),
        ins(
            106,
            vec![set(2, Expr::load(r(0), Width::U64))],
            Control::Next,
        ),
        ins(107, vec![store(r(0), Width::U64, 5)], Control::Next),
        ins(
            108,
            vec![set(2, Expr::load(r(0), Width::U64))],
            Control::Return(r(2)),
        ),
    ]);
    assert_eq!(writers(&a, 102), BTreeSet::from([100]));
    assert_eq!(writers(&a, 104), BTreeSet::from([100, 103]));
    assert_eq!(writers(&a, 106), BTreeSet::from([100, 103, 105]));
    assert_eq!(writers(&a, 108), BTreeSet::from([107]));
    assert!(
        a.queries().as_ref().unwrap()[0]
            .candidates
            .iter()
            .all(|c| c.alias == Alias::Exact)
    );
}

#[test]
fn concrete_byte_tags_never_introduce_a_writer_missing_from_the_candidates() {
    let (program, a) = analyze(vec![
        ins(100, vec![store(r(0), Width::U64, 1)], Control::Next),
        ins(101, vec![store(r(1), Width::U16, 2)], Control::Next),
        ins(102, vec![store(add(r(0), 7), Width::U8, 3)], Control::Next),
        ins(
            103,
            vec![set(2, Expr::load(r(0), Width::U64))],
            Control::Return(r(2)),
        ),
    ]);
    let candidates = contributions(&a, 103);
    for p in 32..=48 {
        for q in 24..=64 {
            let result = program
                .run_with_memory(&[p, q, 0, 0], 0, &[0; 128], 20)
                .unwrap();
            let RunStatus::Returned(value) = result.status else {
                panic!("{result:?}");
            };
            for (byte, tag) in value.to_le_bytes().into_iter().enumerate() {
                let writer = match tag {
                    0 => 0,
                    1 => 100,
                    2 => 101,
                    3 => 102,
                    _ => panic!("unexpected byte tag"),
                };
                assert!(
                    candidates
                        .get(&writer)
                        .is_some_and(|mask| mask & (1 << byte) != 0),
                    "p={p} q={q} tag={tag} byte={byte}"
                );
            }
        }
    }
}

#[test]
fn diamond_phis_keep_both_writers_and_the_virtual_initial_path() {
    for write_false in [false, true] {
        let (_, a) = analyze(vec![
            ins(
                100,
                vec![],
                Control::Branch {
                    condition: r(2),
                    target: 110,
                },
            ),
            ins(
                101,
                if write_false {
                    vec![store(r(0), Width::U64, 1)]
                } else {
                    vec![]
                },
                Control::Jump(120),
            ),
            ins(110, vec![store(r(0), Width::U64, 2)], Control::Jump(120)),
            ins(
                120,
                vec![set(3, Expr::load(r(0), Width::U64))],
                Control::Return(r(3)),
            ),
        ]);
        assert_eq!(
            writers(&a, 120),
            BTreeSet::from([if write_false { 101 } else { 0 }, 110])
        );
        let block = a.blocks().iter().find(|b| b.start == 120).unwrap();
        let Definition::Phi { inputs, .. } = &a.definitions()[block.entry.0] else {
            panic!()
        };
        assert_eq!(
            inputs.iter().map(|i| i.predecessor).collect::<Vec<_>>(),
            vec![Some(101), Some(110)]
        );
    }
}

#[test]
fn loop_carried_addresses_do_not_confuse_equal_ssa_names_with_equal_iterations() {
    for delta in [0, 8] {
        let (program, a) = analyze(vec![
            ins(
                100,
                vec![set(2, Expr::load(r(0), Width::U64))],
                Control::Next,
            ),
            ins(
                101,
                vec![store(add(r(0), delta), Width::U64, 1)],
                Control::Next,
            ),
            ins(
                102,
                vec![set(0, add(r(0), 8)), set(1, add(r(1), u64::MAX))],
                Control::Next,
            ),
            ins(
                103,
                vec![],
                Control::Branch {
                    condition: r(1),
                    target: 100,
                },
            ),
            ins(104, vec![], Control::Return(r(2))),
        ]);
        assert_eq!(writers(&a, 100), BTreeSet::from([0, 101]));
        let query = &a.queries().as_ref().unwrap()[0];
        assert_eq!(query.address_widened, delta == 0);
        let previous_store = query
            .candidates
            .iter()
            .find(|c| matches!(a.definitions()[c.definition.0], Definition::Store { .. }))
            .unwrap();
        assert_eq!(
            previous_store.alias,
            if delta == 8 { Alias::Exact } else { Alias::May }
        );
        let Definition::Phi { inputs, .. } = &a.definitions()[a.blocks()[0].entry.0] else {
            panic!()
        };
        assert!(
            inputs
                .iter()
                .any(|i| i.predecessor.is_none() && i.memory == MemoryId(0))
        );
        for count in 1..=4 {
            let result = program
                .run_with_memory(&[32, count, 0, 0], 0, &[0; 128], 100)
                .unwrap();
            let RunStatus::Returned(value) = result.status else {
                panic!("{result:?}")
            };
            for tag in value.to_le_bytes() {
                assert!(writers(&a, 100).contains(&if tag == 0 { 0 } else { 101 }));
            }
        }
    }
}

#[test]
fn nested_address_rhs_and_lazy_reads_keep_the_original_store_order() {
    let (_, a) = analyze(vec![ins(
        100,
        vec![Assignment {
            destination: Place::Memory {
                address: Expr::load(c(32), Width::U64),
                width: Width::U64,
            },
            value: Expr::select(
                r(0),
                Expr::load(c(64), Width::U64),
                Expr::load(c(u64::MAX), Width::U64),
            ),
        }],
        Control::Return(Expr::load(c(64), Width::U64)),
    )]);
    let accesses = a.accesses();
    assert_eq!(
        accesses.iter().map(|a| a.source.kind).collect::<Vec<_>>(),
        vec![
            AccessKind::Read,
            AccessKind::Read,
            AccessKind::Read,
            AccessKind::Write,
            AccessKind::Read
        ]
    );
    assert!(
        accesses[..4]
            .iter()
            .all(|a| a.incoming == accesses[0].incoming)
    );
    assert_eq!(accesses[4].incoming, accesses[3].definition.unwrap());
    assert!(
        accesses[1]
            .source
            .path
            .contains(&nirvana::type_infer::PathEdge::Taken)
    );
    assert!(
        accesses[2]
            .source
            .path
            .contains(&nirvana::type_infer::PathEdge::NotTaken)
    );
}

#[test]
fn modular_offsets_and_register_versions_do_not_invent_object_separation() {
    let (_, a) = analyze(vec![
        ins(
            100,
            vec![store(add(r(0), u64::MAX - 7), Width::U64, 1)],
            Control::Next,
        ),
        ins(
            101,
            vec![set(2, Expr::load(r(0), Width::U64))],
            Control::Next,
        ),
        ins(102, vec![set(0, r(1))], Control::Next),
        ins(
            103,
            vec![set(2, Expr::load(r(0), Width::U64))],
            Control::Return(r(2)),
        ),
    ]);
    assert_eq!(writers(&a, 101), BTreeSet::from([0]));
    assert_eq!(writers(&a, 103), BTreeSet::from([0, 100]));
}

#[test]
fn pointer_phis_translate_separately_for_each_predecessor_and_keep_real_aliases() {
    let (p, a) = analyze(vec![
        ins(100, vec![store(r(0), Width::U64, 1)], Control::Next),
        ins(
            101,
            vec![store(r(1), Width::U64, 2)],
            Control::Branch {
                condition: r(2),
                target: 110,
            },
        ),
        ins(102, vec![set(3, r(0))], Control::Jump(120)),
        ins(110, vec![set(3, r(1))], Control::Jump(120)),
        ins(120, vec![], Control::Return(Expr::load(r(3), Width::U64))),
    ]);
    assert_eq!(writers(&a, 120), BTreeSet::from([100, 101]));
    for choice in [0, 1] {
        for other in 24..=48 {
            let RunStatus::Returned(value) = p
                .run_with_memory(&[32, other, choice, 0], 0, &[0; 128], 20)
                .unwrap()
                .status
            else {
                panic!()
            };
            for (byte, tag) in value.to_le_bytes().into_iter().enumerate() {
                let writer = match tag {
                    1 => 100,
                    2 => 101,
                    _ => panic!("initial memory cannot reach this Load"),
                };
                assert!(contributions(&a, 120)[&writer] & (1 << byte) != 0);
            }
        }
    }
}

#[test]
fn simultaneous_loop_phi_translation_keeps_previous_iteration_pointer_values() {
    let (p, a) = analyze(vec![
        ins(
            100,
            vec![set(2, Expr::load(r(0), Width::U64))],
            Control::Next,
        ),
        ins(101, vec![store(r(1), Width::U64, 2)], Control::Next),
        ins(
            102,
            vec![set(3, r(0)), set(0, r(1)), set(1, r(3))],
            Control::Next,
        ),
        // A one-shot control byte repeats the loop once. Both pointer phis
        // swap simultaneously; R2 keeps the observed data until exit.
        ins(
            103,
            vec![],
            Control::Branch {
                condition: Expr::load(c(16), Width::U8),
                target: 110,
            },
        ),
        ins(104, vec![], Control::Return(r(2))),
        ins(110, vec![store(c(16), Width::U8, 0)], Control::Jump(100)),
    ]);
    assert_eq!(writers(&a, 100), BTreeSet::from([0, 101, 110]));
    let mut ram = [0; 128];
    ram[16] = 1;
    let RunStatus::Returned(value) = p
        .run_with_memory(&[32, 48, 0, 0], 0, &ram, 30)
        .unwrap()
        .status
    else {
        panic!()
    };
    assert_eq!(value, 0x0202020202020202);
    assert!(contributions(&a, 100)[&101] == 0xff);
    // Unconstrained input pointers may also alias the loop-control byte.
    assert!(contributions(&a, 100)[&110] != 0);
}

#[test]
fn reloaded_pointer_atoms_expire_when_their_defining_block_is_crossed() {
    let (p, a) = analyze(vec![
        ins(
            100,
            vec![
                set(3, Expr::load(c(16), Width::U64)),
                set(2, Expr::load(r(3), Width::U64)),
            ],
            Control::Next,
        ),
        ins(101, vec![store(r(3), Width::U64, 1)], Control::Next),
        ins(
            102,
            vec![Assignment {
                destination: Place::Memory {
                    address: c(16),
                    width: Width::U64,
                },
                value: r(1),
            }],
            Control::Next,
        ),
        ins(
            103,
            vec![set(0, add(r(0), u64::MAX))],
            Control::Branch {
                condition: r(0),
                target: 100,
            },
        ),
        ins(104, vec![], Control::Return(r(2))),
    ]);
    let access = a
        .accesses()
        .iter()
        .position(|x| x.source.site.instruction == 100 && x.source.site.assignment == Some(1))
        .unwrap();
    let query = a
        .queries()
        .as_ref()
        .unwrap()
        .iter()
        .find(|q| q.access == access)
        .unwrap();
    assert!(query.address_widened);
    assert!(
        query
            .candidates
            .iter()
            .any(|c| matches!(a.definitions()[c.definition.0], Definition::Initial))
    );
    let mut ram = [0; 128];
    ram[16..24].copy_from_slice(&32u64.to_le_bytes());
    let RunStatus::Returned(value) = p
        .run_with_memory(&[2, 48, 0, 0], 0, &ram, 30)
        .unwrap()
        .status
    else {
        panic!()
    };
    assert_eq!(
        value, 0,
        "the newly loaded pointer reaches untouched initial memory"
    );
}

#[test]
fn partial_stores_compose_per_byte_without_combining_alternative_paths() {
    let (_, a) = analyze(vec![
        ins(100, vec![store(r(0), Width::U64, 1)], Control::Next),
        ins(101, vec![store(r(0), Width::U32, 2)], Control::Next),
        ins(102, vec![store(add(r(0), 4), Width::U32, 3)], Control::Next),
        ins(103, vec![], Control::Return(Expr::load(r(0), Width::U64))),
    ]);
    assert_eq!(
        contributions(&a, 103),
        BTreeMap::from([(101, 0x0f), (102, 0xf0)])
    );
    let (_, a) = analyze(vec![
        ins(
            100,
            vec![store(r(0), Width::U64, 1)],
            Control::Branch {
                condition: r(1),
                target: 110,
            },
        ),
        ins(101, vec![store(r(0), Width::U32, 2)], Control::Jump(120)),
        ins(
            110,
            vec![store(add(r(0), 4), Width::U32, 3)],
            Control::Jump(120),
        ),
        ins(120, vec![], Control::Return(Expr::load(r(0), Width::U64))),
    ]);
    assert_eq!(
        contributions(&a, 120),
        BTreeMap::from([(100, 0xff), (101, 0x0f), (110, 0xf0)])
    );
}

#[test]
fn byte_intervals_match_executed_memory_for_all_widths_and_shifted_overlaps() {
    for read in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for write in [Width::U8, Width::U16, Width::U32, Width::U64] {
            for offset in -12i64..=12 {
                let (p, a) = analyze(vec![
                    ins(
                        100,
                        vec![Assignment {
                            destination: Place::Memory {
                                address: add(r(0), offset as u64),
                                width: write,
                            },
                            value: c(0x0807060504030201),
                        }],
                        Control::Next,
                    ),
                    ins(101, vec![], Control::Return(Expr::load(r(0), read))),
                ]);
                let RunStatus::Returned(value) = p
                    .run_with_memory(&[64, 0, 0, 0], 0, &[0xaa; 128], 10)
                    .unwrap()
                    .status
                else {
                    panic!()
                };
                let candidates = contributions(&a, 101);
                let mut expected = BTreeMap::new();
                for (byte, tag) in value.to_le_bytes().iter().take(read.bytes()).enumerate() {
                    let writer = match tag {
                        0xaa => 0,
                        1..=8 => 100,
                        _ => panic!(),
                    };
                    *expected.entry(writer).or_insert(0u8) |= 1 << byte;
                }
                assert_eq!(
                    candidates, expected,
                    "read={read:?} write={write:?} offset={offset}"
                );
                let query = &a.queries().as_ref().unwrap()[0];
                for candidate in &query.candidates {
                    for byte in 0..8 {
                        let contributes = candidate.byte_mask & (1 << byte) != 0;
                        match &a.definitions()[candidate.definition.0] {
                            Definition::Initial => {
                                assert_eq!(candidate.unknown_bytes & (1 << byte) != 0, contributes);
                                assert_eq!(candidate.byte_sources[byte], 0);
                            }
                            Definition::Store { .. } => {
                                assert_eq!(candidate.unknown_bytes, 0);
                                let expected = if contributes {
                                    1 << (value.to_le_bytes()[byte] - 1)
                                } else {
                                    0
                                };
                                assert_eq!(
                                    candidate.byte_sources[byte], expected,
                                    "{read:?}/{write:?}/{offset}/byte {byte}"
                                );
                            }
                            other => panic!("{other:?}"),
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn phi_translations_retain_every_possible_store_byte_position() {
    let (p, a) = analyze(vec![
        ins(
            100,
            vec![Assignment {
                destination: Place::Memory {
                    address: r(0),
                    width: Width::U32,
                },
                value: c(0x44332211),
            }],
            Control::Branch {
                condition: r(1),
                target: 110,
            },
        ),
        ins(101, vec![], Control::Jump(120)),
        ins(110, vec![set(0, add(r(0), 1))], Control::Jump(120)),
        ins(
            120,
            vec![set(2, Expr::load(r(0), Width::U16))],
            Control::Return(r(2)),
        ),
    ]);
    let query = a.queries().as_ref().unwrap().last().unwrap();
    assert!(query.translated_edges > 0);
    assert_eq!(query.candidates.len(), 1);
    let writer = query.candidates[0];
    assert_eq!(writer.byte_mask, 3);
    assert_eq!(writer.unknown_bytes, 0);
    assert_eq!(writer.byte_sources, [3, 6, 0, 0, 0, 0, 0, 0]);
    for (branch, expected) in [(0, 0x2211), (1, 0x3322)] {
        assert_eq!(
            p.execute_with_memory(&[64, branch, 0, 0], 0, &[0xa5; 128], 16)
                .unwrap()
                .value,
            expected
        );
    }
}

#[test]
fn query_exhaustion_keeps_the_graph_and_reports_no_partial_candidate_set() {
    let mut code = Vec::new();
    for i in 0..600 {
        code.push(ins(100 + i, vec![store(r(0), Width::U8, 1)], Control::Next));
    }
    for i in 0..600 {
        code.push(ins(
            700 + i,
            vec![set(2, Expr::load(r(1), Width::U64))],
            if i == 599 {
                Control::Return(r(2))
            } else {
                Control::Next
            },
        ));
    }
    let (p, a) = analyze(code);
    assert!(
        a.queries()
            .as_ref()
            .unwrap_err()
            .contains("candidate storage limit")
    );
    assert_eq!(a.accesses().len(), 1200);
    let mut malformed = SsaFunction::build(&p).unwrap();
    malformed.blocks[0].points[0].site.instruction = 0;
    assert!(memory_ssa::analyze(&p, &malformed).is_err());
    let json = a.to_json().unwrap();
    let mut child=Command::new("python3").args(["-c","import json,sys; r=json.load(sys.stdin); assert r['schema']=='nirvana-memory-ssa-v1'; assert r['queries']['status']=='unavailable'; assert 'reads' not in r['queries']; assert len(r['accesses'])==1200"]).stdin(Stdio::piped()).spawn().unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(json.as_bytes())
        .unwrap();
    assert!(child.wait().unwrap().success());
}
