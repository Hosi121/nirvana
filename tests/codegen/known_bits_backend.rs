use crate::support::ir::{c, r};
use crate::support::{checked_c, native};
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus, Width,
};
use std::fmt::Write as _;
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn address(offset: u64) -> Expr {
    b(B::Add, r(7), c(offset))
}
fn store(offset: u64, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: address(offset),
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
fn sources() -> Vec<(Program, u64, bool)> {
    let diamond = vec![
        ins(
            0,
            vec![set(0, Expr::load(r(7), Width::U64))],
            Control::Branch {
                condition: r(0),
                target: 2,
            },
        ),
        ins(1, vec![set(1, c(0x11)), store(8, c(17))], Control::Jump(3)),
        ins(2, vec![set(1, c(0x13)), store(8, c(19))], Control::Jump(3)),
        ins(
            3,
            vec![
                set(2, b(B::And, r(1), c(0x11))),
                store(
                    16,
                    Expr::select(
                        Expr::load(address(24), Width::U64),
                        r(2),
                        Expr::load(address(40), Width::U64),
                    ),
                ),
            ],
            Control::Return(r(2)),
        ),
    ];
    let bits = |e| b(B::Or, b(B::And, e, c(15)), c(16));
    let looped = vec![
        ins(
            0,
            vec![
                set(0, Expr::load(r(7), Width::U64)),
                set(1, bits(r(0))),
                set(2, b(B::And, r(0), c(3))),
            ],
            Control::Jump(1),
        ),
        ins(
            1,
            vec![],
            Control::Branch {
                condition: r(2),
                target: 3,
            },
        ),
        ins(
            2,
            vec![store(
                16,
                Expr::select(
                    Expr::load(address(24), Width::U64),
                    b(B::And, r(1), c(16)),
                    Expr::load(address(40), Width::U64),
                ),
            )],
            Control::Return(b(B::And, r(1), c(16))),
        ),
        ins(
            3,
            vec![
                set(1, bits(b(B::Add, r(1), c(1)))),
                store(8, r(1)),
                set(2, b(B::Sub, r(2), c(1))),
            ],
            Control::Jump(1),
        ),
    ];
    let equal = b(B::Eq, r(2), r(3));
    let identity = Program::new(
        0,
        8,
        vec![ins(
            0,
            vec![
                set(0, Expr::load(r(7), Width::U64)),
                store(8, r(0)),
                set(2, Expr::load(address(8), Width::U64)),
                set(3, Expr::load(address(8), Width::U64)),
                store(
                    16,
                    Expr::select(
                        Expr::load(address(24), Width::U64),
                        equal.clone(),
                        Expr::load(address(40), Width::U64),
                    ),
                ),
            ],
            Control::Return(equal),
        )],
    )
    .unwrap();
    [diamond, looped]
        .into_iter()
        .zip([17, 16])
        .map(|(i, value)| (Program::new(0, 8, i).unwrap(), value, false))
        .chain(crate::support::bit_invariants::memory_programs().map(|p| (p, 128, false)))
        .chain([(identity, 1, true)])
        .collect()
}
#[test]
fn bit_phi_and_loop_invariants_reduce_c_while_preserving_all_ram_and_first_faults() {
    let scratch = native::Scratch::new();
    let mut rows = 0;
    for (index, (source, returned, identity)) in sources().into_iter().enumerate() {
        let mut text = String::new();
        let mut expected = Vec::new();
        let mut outcomes = [0; 3];
        for x in [0u64, 1, 2, 3, 127, 128, 255, 256, 1 << 63, u64::MAX] {
            for flag in [0, 1] {
                for pointer in [
                    4096,
                    4097,
                    4104,
                    4112,
                    4120,
                    4128,
                    4144,
                    4151,
                    4152,
                    4159,
                    u64::MAX,
                ] {
                    let stored = x.rotate_left(8) ^ 0xa500;
                    writeln!(text, "{pointer} {x} {stored} 19 {flag}").unwrap();
                    let mut memory: Vec<_> = (0..64usize)
                        .map(|n| n.wrapping_mul(29).wrapping_add(7) as u8)
                        .collect();
                    for (i, v) in [x, stored, 19, flag].into_iter().enumerate() {
                        if let Some(o) = pointer
                            .checked_add(i as u64 * 8)
                            .and_then(|a| a.checked_sub(4096))
                            .filter(|o| *o <= 56)
                        {
                            memory[o as usize..o as usize + 8].copy_from_slice(&v.to_le_bytes());
                        }
                    }
                    let mut input = [0; 8];
                    input[7] = pointer;
                    input[4] = 4160;
                    let report = source.run_with_memory(&input, 4096, &memory, 64).unwrap();
                    let mut row = match report.status {
                        RunStatus::Returned(value) => {
                            outcomes[0] += 1;
                            assert_eq!(value, returned);
                            vec![0, 0, 0, 0, value]
                        }
                        RunStatus::Fault(f) => {
                            let access = if f.access == nirvana::ir::AccessKind::Read {
                                1
                            } else {
                                2
                            };
                            outcomes[access] += 1;
                            vec![1, f.address, access as u64, f.width.bytes() as u64, 0]
                        }
                        _ => panic!("small loop exceeds budget"),
                    };
                    row.extend(
                        report
                            .state
                            .memory
                            .chunks_exact(8)
                            .map(|v| u64::from_le_bytes(v.try_into().unwrap())),
                    );
                    expected.push(row);
                }
            }
        }
        assert!(outcomes.into_iter().all(|n| n > 0));
        for coalesce in [false, true] {
            for objects in [false, true] {
                let out = nirvana::readable::emit_readable_c_with_options(
                    &source,
                    nirvana::readable::ReadableOptions {
                        stack_register: Some(Reg(4)),
                        coalesce_locals: coalesce,
                        recover_objects: objects,
                        compact_memory: true,
                    },
                )
                .unwrap();
                if identity {
                    let evidence = out
                        .memory_values
                        .expect("word identity is adopted after cost comparison");
                    assert!(
                        evidence.proved_loads >= 2
                            && evidence.snapshot_values > 0
                            && evidence.replaced_reads >= 4
                    );
                } else {
                    let evidence = out.known_bits.expect("partial bit proof adopted");
                    assert!(
                        evidence.replacements > 0
                            && evidence.known_values > evidence.constant_values
                    );
                    if index >= 2 {
                        assert!(
                            evidence.memory_available
                                && evidence.memory_loads > 0
                                && evidence.store_load_edges > 0
                        );
                    }
                }
                let body = out.code.split("uint64_t nirvana_readable(").nth(1).unwrap();
                assert!(body.contains(&format!("return {returned};")), "{body}");
                let path = scratch
                    .0
                    .join(format!("bits-{index}-{coalesce}-{objects}.c"));
                std::fs::write(&path, checked_c::source(&out, 8, 4)).unwrap();
                for opt in ["-O0", "-O2"] {
                    let bin = path.with_extension(format!("{opt}.bin"));
                    native::compile_c(
                        &path,
                        &bin,
                        &[
                            opt,
                            "-fsanitize=undefined",
                            "-fno-sanitize-recover=undefined",
                        ],
                    );
                    assert_eq!(
                        native::run_fields(&bin, &text, 13),
                        expected,
                        "{index}/{coalesce}/{objects}/{opt}"
                    );
                    rows += expected.len();
                }
            }
        }
    }
    println!("{rows} known-bit C return/full-RAM/ordered-first-fault observations");
}
