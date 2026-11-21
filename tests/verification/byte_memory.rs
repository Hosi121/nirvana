//! Check actual MemorySSA byte-source sets against an independent array model.
use super::memory_bits::{address, check_at, put};
use crate::support::ir::{c, r};
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use nirvana::memory_ssa::{self, Analysis, Definition};
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn program(read: Width, write: Width, offset: i64) -> Program {
    Program::new(
        0,
        3,
        vec![
            ins(
                0,
                vec![Assignment {
                    destination: Place::Memory {
                        address: Expr::binary(B::Add, r(0), c(offset as u64)),
                        width: write,
                    },
                    value: r(1),
                }],
                Control::Next,
            ),
            ins(
                1,
                vec![Assignment {
                    destination: Reg(2).into(),
                    value: Expr::load(r(0), read),
                }],
                Control::Return(r(2)),
            ),
        ],
    )
    .unwrap()
}
fn analyze(source: &Program) -> Analysis {
    memory_ssa::analyze(source, &nirvana::ssa::SsaFunction::build(source).unwrap()).unwrap()
}
fn choices(analysis: &Analysis, byte: usize, read_address: &str) -> Vec<String> {
    let query = analysis.queries().as_ref().unwrap().last().unwrap();
    let mut result = std::collections::BTreeSet::new();
    for candidate in &query.candidates {
        if candidate.byte_mask & (1 << byte) == 0 {
            continue;
        }
        match analysis.definitions()[candidate.definition.0] {
            Definition::Initial => {
                assert!(candidate.unknown_bytes & (1 << byte) != 0);
                result.insert(format!("(select m {read_address})"));
            }
            Definition::Store { .. } => {
                assert_eq!(candidate.unknown_bytes & (1 << byte), 0);
                for source in 0..8 {
                    if candidate.byte_sources[byte] & (1 << source) != 0 {
                        result.insert(format!("((_ extract {} {}) x)", source * 8 + 7, source * 8));
                    }
                }
            }
            _ => panic!("unexpected effect in scalar model"),
        }
    }
    assert!(!result.is_empty());
    result.into_iter().collect()
}
fn violation(actual: &str, choices: &[String]) -> String {
    format!(
        "(define-fun observed () (_ BitVec 8) {actual})\n(assert (and {}))",
        choices
            .iter()
            .map(|v| format!("(distinct observed {v})"))
            .collect::<Vec<_>>()
            .join(" ")
    )
}
#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn production_byte_maps_cover_array_store_read_values_and_replay_broken_maps() {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/byte-memory");
    let widths = [Width::U8, Width::U16, Width::U32, Width::U64];
    let mut proved = 0;
    for read in widths {
        for write in widths {
            for offset in -12i64..=12 {
                let source = program(read, write, offset);
                let analysis = analyze(&source);
                let stored = put(
                    "m",
                    &format!("(bvadd a (_ bv{} 64))", offset as u64),
                    "x",
                    write.bytes(),
                );
                for byte in 0..read.bytes() {
                    let target = address("a", byte);
                    check_at(
                        &root,
                        &format!("map-{}-{}-{offset}-{byte}", read.bits(), write.bits()),
                        &violation(
                            &format!("(select {stored} {target})"),
                            &choices(&analysis, byte, &target),
                        ),
                        "unsat",
                    );
                    proved += 1;
                }
            }
        }
    }
    // No address relation is assumed: either the old byte or one of the
    // Store's own bytes supplies the result. Use the production candidate set.
    for write in widths {
        let source = Program::new(
            0,
            4,
            vec![
                ins(
                    0,
                    vec![Assignment {
                        destination: Place::Memory {
                            address: r(1),
                            width: write,
                        },
                        value: r(2),
                    }],
                    Control::Next,
                ),
                ins(
                    1,
                    vec![Assignment {
                        destination: Reg(3).into(),
                        value: Expr::load(r(0), Width::U8),
                    }],
                    Control::Return(r(3)),
                ),
            ],
        )
        .unwrap();
        let analysis = analyze(&source);
        let stored = put("m", "b", "x", write.bytes());
        check_at(
            &root,
            &format!("may-{}", write.bits()),
            &violation(&format!("(select {stored} a)"), &choices(&analysis, 0, "a")),
            "unsat",
        );
        proved += 1;
    }
    let source = Program::new(
        0,
        4,
        vec![
            ins(
                0,
                vec![Assignment {
                    destination: Place::Memory {
                        address: r(0),
                        width: Width::U32,
                    },
                    value: r(1),
                }],
                Control::Branch {
                    condition: r(3),
                    target: 2,
                },
            ),
            ins(1, vec![], Control::Jump(3)),
            ins(
                2,
                vec![Assignment {
                    destination: Reg(0).into(),
                    value: Expr::binary(B::Add, r(0), c(1)),
                }],
                Control::Jump(3),
            ),
            ins(
                3,
                vec![Assignment {
                    destination: Reg(2).into(),
                    value: Expr::load(r(0), Width::U16),
                }],
                Control::Return(r(2)),
            ),
        ],
    )
    .unwrap();
    let analysis = analyze(&source);
    let stored = put("m", "a", "x", 4);
    for byte in 0..2 {
        let target = address("(ite choice (bvadd a (_ bv1 64)) a)", byte);
        check_at(
            &root,
            &format!("phi-{byte}"),
            &violation(
                &format!("(select {stored} {target})"),
                &choices(&analysis, byte, &target),
            ),
            "unsat",
        );
        proved += 1;
    }
    let stored = put("m", "a", "x", 4);
    check_at(
        &root,
        "wrong-source-byte",
        &format!(
            "(assert (= a (_ bv64 64)))\n(assert (= x #x0000000044332211))\n{}",
            violation(
                &format!("(select {stored} a)"),
                &["((_ extract 15 8) x)".into()]
            )
        ),
        "sat",
    );
    assert_eq!(
        program(Width::U8, Width::U32, 0)
            .execute_with_memory(&[64, 0x44332211, 0], 0, &[0xaa; 128], 4)
            .unwrap()
            .value,
        0x11
    );
    let stored = put("m", "a", "x", 1);
    let target = address("a", 1);
    check_at(
        &root,
        "missing-initial-byte",
        &format!(
            "(assert (= a (_ bv64 64)))\n(assert (= x (_ bv128 64)))\n(assert (= (select m {target}) #xaa))\n{}",
            violation(&format!("(select {stored} {target})"), &["#x00".into()])
        ),
        "sat",
    );
    assert_eq!(
        program(Width::U16, Width::U8, 0)
            .execute_with_memory(&[64, 128, 0], 0, &[0xaa; 128], 4)
            .unwrap()
            .value,
        0xaa80
    );
    assert_eq!(proved, 1506);
    println!(
        "{proved} universal production byte-map claims; 2 SAT broken maps with fixed relevant inputs replayed in checked IR"
    );
}
