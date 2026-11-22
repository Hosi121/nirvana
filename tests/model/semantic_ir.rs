use crate::support::ir::{c, r};
use crate::support::{checked_c, native};
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use nirvana::semantic_ir::{SemanticPlan, validate};
use nirvana::{display_dce, x86};
use std::fmt::Write as _;
#[path = "semantic_ir/word.rs"]
mod word;

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
    b(B::Add, r(x86::RDI), c(offset))
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
fn make(assignments: Vec<Assignment>, control: Control) -> Program {
    Program::new(
        0,
        32,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control,
        }],
    )
    .unwrap()
}
fn high(x: Expr) -> Expr {
    b(B::SMulHigh, c(0x6666_6666_6666_6667), x)
}
fn estimate(x: Expr) -> Expr {
    b(B::AShr, high(x), c(2))
}
fn sign(x: Expr) -> Expr {
    b(B::AShr, x, c(63))
}
fn quotient(x: Expr) -> Expr {
    b(B::Sub, estimate(x.clone()), sign(x))
}
fn source() -> Program {
    make(
        vec![
            set(0, Expr::load(r(x86::RDI), Width::U64)),
            set(6, r(0)),
            set(1, high(r(0))),
            set(0, c(99)),
            store(8, r(0)),
            set(2, b(B::AShr, r(1), c(2))),
            set(3, sign(r(6))),
            set(4, b(B::Sub, r(2), r(3))),
            set(5, b(B::Sub, r(6), b(B::Mul, r(4), c(10)))),
            store(16, r(5)),
            set(0, Expr::load(address(24), Width::U64)),
        ],
        Control::Return(b(B::Xor, b(B::Xor, b(B::Sub, r(2), r(3)), r(5)), r(0))),
    )
}
fn split(source: &Program) -> Program {
    let a = &source.instructions()[0];
    let mut instructions: Vec<_> = a
        .assignments
        .iter()
        .enumerate()
        .map(|(i, a)| IrInstruction {
            address: i as u64,
            size: 1,
            assignments: vec![a.clone()],
            control: Control::Next,
        })
        .collect();
    instructions.last_mut().unwrap().control = a.control.clone();
    Program::new(0, source.register_count(), instructions).unwrap()
}
fn compare(source: &Program, target: &Program, input: &[u64], memory: &[u8], full: bool) {
    let mut extended = vec![0xa5a5_5a5a_9876_1234; target.register_count()];
    extended[..input.len()].copy_from_slice(input);
    for limit in 0..=source.instructions().len() * 5 + 2 {
        let a = source.run_with_memory(input, 4096, memory, limit).unwrap();
        let z = target
            .run_with_memory(&extended, 4096, memory, limit)
            .unwrap();
        assert_eq!(a.status, z.status, "limit={limit}");
        assert_eq!(a.state.memory, z.state.memory);
        assert_eq!(a.state.trace, z.state.trace);
        assert_eq!(a.state.instruction, z.state.instruction);
        if full {
            assert_eq!(
                a.state.registers,
                z.state.registers[..source.register_count()]
            );
        }
    }
}

#[test]
fn retained_lowering_binds_its_input_and_projects_only_its_own_capture_file() {
    let source = source();
    let plan = SemanticPlan::analyze(&source).unwrap();
    let lowering = plan.lowering(&source).unwrap();
    assert_eq!(lowering.source().instructions(), source.instructions());
    assert_eq!(lowering.source().register_count(), source.register_count());
    assert_eq!(lowering.evidence(), plan.evidence());
    assert!(lowering.validate());
    let mut input = vec![0; source.register_count()];
    input[x86::RDI] = 4096;
    let memory: Vec<_> = (0..64).collect();
    for budget in [0, 1, 2] {
        let expected = source
            .run_with_memory(&input, 4096, &memory, budget)
            .unwrap();
        assert!(lowering.project_report(expected.clone()).is_none());
        for initial in [0, u64::MAX] {
            let mut extended = input.clone();
            extended.resize(lowering.program().register_count(), initial);
            let actual = lowering
                .program()
                .run_with_memory(&extended, 4096, &memory, budget)
                .unwrap();
            assert_eq!(lowering.project_report(actual).unwrap(), expected);
        }
    }
    let mut changed = source.instructions().to_vec();
    changed[0].assignments[2].value = b(B::SMulHigh, c(0x6666_6666_6666_6666), r(0));
    let changed = Program::new(0, source.register_count(), changed).unwrap();
    assert!(plan.lowering(&changed).is_none());
}
fn inputs() -> Vec<u64> {
    let mut values = vec![
        0,
        1,
        9,
        10,
        11,
        (1 << 63) - 1,
        1 << 63,
        (1 << 63) + 1,
        u64::MAX - 10,
        u64::MAX,
    ];
    let mut seed = 0xfedc_ba98_7654_3210u64;
    for _ in 0..32 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        values.push(seed);
    }
    values
}
#[test]
fn historical_inputs_preserve_all_original_registers_memory_faults_and_cutoffs() {
    for source in [source(), split(&source())] {
        let original = source.instructions().to_vec();
        let plan = SemanticPlan::analyze(&source).unwrap();
        let evidence = plan.evidence();
        assert_eq!(
            (evidence.inputs, evidence.divisions, evidence.remainders),
            (1, 1, 1)
        );
        let lowered = plan.lower(&source).unwrap();
        assert!(validate(&source, &plan, &lowered));
        let compact = display_dce::propose(&lowered).unwrap();
        assert!(display_dce::validate(&lowered, &compact));
        for x in inputs() {
            for pointer in [
                4096,
                4097,
                4104,
                4128,
                4136,
                4144,
                4152,
                4159,
                4160,
                u64::MAX,
            ] {
                let mut input = [0x6543_210f_edcb_a987; 32];
                input[x86::RDI] = pointer;
                let mut memory = [0x93; 64];
                if let Some(offset) = pointer.checked_sub(4096).filter(|&p| p <= 56) {
                    memory[offset as usize..offset as usize + 8].copy_from_slice(&x.to_le_bytes());
                }
                compare(&source, &lowered, &input, &memory, true);
                compare(&source, &compact, &input, &memory, false);
                if pointer == 4096 {
                    let run = lowered
                        .execute_with_memory(
                            &[input.to_vec(), vec![0; lowered.register_count() - 32]].concat(),
                            4096,
                            &memory,
                            32,
                        )
                        .unwrap();
                    assert_eq!(run.registers[4], ((x as i64) / 10) as u64);
                    assert_eq!(run.registers[5], ((x as i64) % 10) as u64);
                }
            }
        }
        assert_eq!(source.instructions(), original);
    }
}
#[test]
fn control_only_values_keep_lazy_reads_and_branch_targets() {
    for branch in [false, true] {
        let condition = Expr::select(
            Expr::load(r(x86::RDI), Width::U64),
            quotient(r(0)),
            Expr::load(address(64), Width::U64),
        );
        let instructions = if branch {
            vec![
                IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![set(0, r(6))],
                    control: Control::Branch {
                        condition,
                        target: 2,
                    },
                },
                IrInstruction {
                    address: 1,
                    size: 1,
                    assignments: vec![store(8, c(11))],
                    control: Control::Return(c(11)),
                },
                IrInstruction {
                    address: 2,
                    size: 1,
                    assignments: vec![store(8, c(22))],
                    control: Control::Return(c(22)),
                },
            ]
        } else {
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![set(0, r(6))],
                control: Control::Return(condition),
            }]
        };
        let source = Program::new(0, 32, instructions).unwrap();
        let plan = SemanticPlan::analyze(&source).unwrap();
        assert_eq!(plan.evidence().divisions, 1);
        let target = plan.lower(&source).unwrap();
        for x in inputs() {
            for flag in [0u64, 1] {
                for pointer in [4096, 4097, 4152, 4159, u64::MAX] {
                    let mut input = [0; 32];
                    input[6] = x;
                    input[x86::RDI] = pointer;
                    let mut memory = [0; 64];
                    memory[..8].copy_from_slice(&flag.to_le_bytes());
                    compare(&source, &target, &input, &memory, true);
                }
            }
        }
    }
}
#[test]
fn repeated_loop_captures_track_signed_wraparound() {
    let source = Program::new(
        0,
        32,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![set(10, c(0)), set(9, c(3))],
                control: Control::Jump(2),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![set(0, b(B::Add, r(0), c(1)))],
                control: Control::Jump(2),
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![
                    set(6, r(0)),
                    set(1, high(r(0))),
                    set(2, b(B::AShr, r(1), c(2))),
                    set(3, sign(r(6))),
                    set(4, b(B::Sub, r(2), r(3))),
                    set(5, b(B::Sub, r(6), b(B::Mul, r(4), c(10)))),
                    store(16, r(5)),
                    set(10, b(B::Add, r(10), b(B::Xor, r(4), r(5)))),
                    set(9, b(B::Sub, r(9), c(1))),
                ],
                control: Control::Branch {
                    condition: r(9),
                    target: 1,
                },
            },
            IrInstruction {
                address: 3,
                size: 1,
                assignments: vec![],
                control: Control::Return(r(10)),
            },
        ],
    )
    .unwrap();
    let plan = SemanticPlan::analyze(&source).unwrap();
    let target = plan.lower(&source).unwrap();
    for x in inputs() {
        let mut input = [0; 32];
        input[0] = x;
        input[x86::RDI] = 4096;
        compare(&source, &target, &input, &[0; 64], true);
        let expected = (0..3u64)
            .map(|i| x.wrapping_add(i) as i64)
            .fold(0u64, |a, x| {
                a.wrapping_add((x / 10) as u64 ^ (x % 10) as u64)
            });
        assert_eq!(
            target
                .execute_with_memory(
                    &[input.to_vec(), vec![0; target.register_count() - 32]].concat(),
                    4096,
                    &[0; 64],
                    32
                )
                .unwrap()
                .value,
            expected
        );
    }
}
#[test]
fn validator_rejects_changed_capture_premature_use_effects_controls_and_source() {
    let source = source();
    let plan = SemanticPlan::analyze(&source).unwrap();
    let good = plan.lower(&source).unwrap();
    let rebuild = |a| Program::new(0, good.register_count(), a).unwrap();
    let mut bad = good.instructions().to_vec();
    let capture = bad[0]
        .assignments
        .iter()
        .position(|a| matches!(a.destination, Place::Register(Reg(32..))))
        .unwrap();
    bad[0].assignments[capture].value = c(42);
    assert!(!validate(&source, &plan, &rebuild(bad)));
    let mut bad = good.instructions().to_vec();
    bad[0].assignments[1].value = r(32); // snapshot exists only at the following high product
    assert!(!validate(&source, &plan, &rebuild(bad)));
    let mut bad = good.instructions().to_vec();
    bad[0].assignments[0].value = r(32); // a captured value cannot replace a read
    assert!(!validate(&source, &plan, &rebuild(bad)));
    let mut bad = good.instructions().to_vec();
    bad[0].assignments.swap(capture, capture + 1);
    assert!(!validate(&source, &plan, &rebuild(bad)));
    let mut bad = good.instructions().to_vec();
    bad[0].assignments.remove(4);
    assert!(!validate(&source, &plan, &rebuild(bad)));
    let mut bad = good.instructions().to_vec();
    bad[0].control = Control::Return(c(0));
    assert!(!validate(&source, &plan, &rebuild(bad)));
    let mut changed = source.instructions().to_vec();
    changed[0].assignments[2].value = high(b(B::Add, r(0), c(1)));
    let changed = Program::new(0, 32, changed).unwrap();
    assert!(!validate(&changed, &plan, &good));
    assert!(plan.lower(&changed).is_none());
}
#[test]
fn unrelated_reads_overwritten_values_and_resource_excess_decline_atomically() {
    let separate = make(
        vec![
            set(1, estimate(Expr::load(r(0), Width::U64))),
            set(2, sign(Expr::load(r(0), Width::U64))),
        ],
        Control::Return(b(B::Sub, r(1), r(2))),
    );
    assert!(SemanticPlan::analyze(&separate).is_none());
    let overwritten = make(
        vec![
            set(6, r(0)),
            set(0, c(123)),
            set(1, estimate(r(0))),
            set(2, sign(r(6))),
        ],
        Control::Return(b(B::Sub, r(1), r(2))),
    );
    assert!(SemanticPlan::analyze(&overwritten).is_none());
    let large = Program::new(0, 4096, source().instructions().to_vec()).unwrap();
    assert!(SemanticPlan::analyze(&large).is_none());
    let mut deep = r(0);
    for _ in 0..129 {
        deep = b(B::Add, deep, c(1));
    }
    let deep = make(vec![], Control::Return(quotient(deep)));
    assert!(SemanticPlan::analyze(&deep).is_none());
}

#[test]
fn generated_c_preserves_complete_ram_and_first_read_or_write_fault() {
    let source = source();
    let scratch = native::Scratch::new();
    let mut text = String::new();
    let mut expected = Vec::new();
    let mut statuses = [0; 3];
    for pointer in [4096, 4097, 4104, 4128, 4136, 4144, 4152, 4159, u64::MAX] {
        for x in inputs() {
            let words = [x, 17, 19, 23];
            writeln!(text, "{pointer} {x} 17 19 23").unwrap();
            let mut memory: Vec<_> = (0..64usize)
                .map(|i| i.wrapping_mul(29).wrapping_add(7) as u8)
                .collect();
            for (i, word) in words.into_iter().enumerate() {
                if let Some(offset) = pointer
                    .checked_add(i as u64 * 8)
                    .and_then(|p| p.checked_sub(4096))
                    .filter(|&p| p <= 56)
                {
                    memory[offset as usize..offset as usize + 8]
                        .copy_from_slice(&word.to_le_bytes());
                }
            }
            let mut regs = [0; 32];
            regs[x86::RDI] = pointer;
            regs[x86::RSP] = 4160;
            let report = source.run_with_memory(&regs, 4096, &memory, 32).unwrap();
            let mut row = match report.status {
                nirvana::ir::RunStatus::Returned(value) => {
                    statuses[0] += 1;
                    vec![0, 0, 0, 0, value]
                }
                nirvana::ir::RunStatus::Fault(fault) => {
                    let access = if fault.access == nirvana::ir::AccessKind::Read {
                        1
                    } else {
                        2
                    };
                    statuses[access] += 1;
                    vec![
                        1,
                        fault.address,
                        access as u64,
                        fault.width.bytes() as u64,
                        0,
                    ]
                }
                _ => panic!("straight-line execution suspended"),
            };
            row.extend(
                report
                    .state
                    .memory
                    .chunks_exact(8)
                    .map(|w| u64::from_le_bytes(w.try_into().unwrap())),
            );
            expected.push(row);
        }
    }
    assert!(statuses.into_iter().all(|n| n > 0));
    for coalesce in [false, true] {
        for objects in [false, true] {
            let output = nirvana::readable::emit_readable_c_with_options(
                &source,
                nirvana::readable::ReadableOptions {
                    stack_register: Some(Reg(x86::RSP)),
                    coalesce_locals: coalesce,
                    recover_objects: objects,
                    compact_memory: true,
                },
            )
            .unwrap();
            assert!(output.semantic_evidence.is_some());
            assert!(
                output.code.contains("nirvana_sdiv64(") && output.code.contains("nirvana_srem64(")
            );
            let harness = checked_c::source(&output, 32, 4);
            let path = scratch.0.join(format!("checked-{coalesce}-{objects}.c"));
            std::fs::write(&path, harness).unwrap();
            for opt in ["-O0", "-O2"] {
                let executable = path.with_extension(format!("{opt}.bin"));
                native::compile_c(
                    &path,
                    &executable,
                    &[
                        opt,
                        "-fsanitize=undefined",
                        "-fno-sanitize-recover=undefined",
                    ],
                );
                assert_eq!(
                    native::run_fields(&executable, &text, 13),
                    expected,
                    "{coalesce}/{objects}/{opt}"
                );
            }
        }
    }
}
