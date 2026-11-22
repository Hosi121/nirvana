use super::*;
use crate::support::word_reciprocals::{WIDTHS, cases, corrected_kernel, kernel, word};
use nirvana::ir::{RunStatus, UnaryOp};

struct Case {
    program: Program,
    q: Reg,
    rem: Reg,
}

#[test]
fn estimate_corrected_word_captures_survive_input_overwrites_and_fault_cutoffs() {
    for width in WIDTHS {
        for divisor in [31, -31] {
            for before in [false, true] {
                let q = corrected_kernel(width, divisor, 4, before, true);
                let source = Program::new(
                    0,
                    8,
                    vec![
                        IrInstruction {
                            address: 0,
                            size: 1,
                            assignments: vec![set(1, q)],
                            control: Control::Next,
                        },
                        IrInstruction {
                            address: 1,
                            size: 1,
                            assignments: vec![set(0, c(99)), store(8, r(1))],
                            control: Control::Return(r(1)),
                        },
                    ],
                )
                .unwrap();
                let plan = SemanticPlan::analyze(&source).unwrap();
                assert!(plan.evidence().divisions >= 1);
                let lowered = plan.lower(&source).unwrap();
                assert!(validate(&source, &plan, &lowered));
                for x in values(width) {
                    for pointer in [4096, 4144, 4159, u64::MAX] {
                        let mut regs = vec![0xa123_ffff_7839_2084; 8];
                        regs[0] = x;
                        regs[x86::RDI] = pointer;
                        let memory = [0xa9; 64];
                        compare(&source, &lowered, &regs, &memory, true);
                        if pointer == 4096 {
                            let mut expanded = regs;
                            expanded.resize(lowered.register_count(), 0);
                            let run = lowered
                                .execute_with_memory(&expanded, 4096, &memory, 100)
                                .unwrap();
                            assert_eq!(
                                run.registers[1],
                                (signed(x.wrapping_add(13), width) / divisor) as u64 & width.mask()
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn signed_extended_results_keep_the_original_low_word_and_full_machine_state() {
    for width in WIDTHS {
        for divisor in [31, -31] {
            let q = corrected_kernel(width, divisor, 4, true, true);
            let source = Program::new(
                0,
                8,
                vec![
                    IrInstruction {
                        address: 0,
                        size: 1,
                        assignments: vec![set(1, q)],
                        control: Control::Next,
                    },
                    IrInstruction {
                        address: 1,
                        size: 1,
                        assignments: vec![set(2, Expr::unary(UnaryOp::SignExtend(width), r(1)))],
                        control: Control::Next,
                    },
                    IrInstruction {
                        address: 2,
                        size: 1,
                        assignments: vec![set(0, c(99)), store(8, r(2))],
                        control: Control::Return(Expr::select(
                            Expr::load(address(16), Width::U64),
                            r(2),
                            Expr::load(address(24), Width::U64),
                        )),
                    },
                ],
            )
            .unwrap();
            let plan = SemanticPlan::analyze(&source).unwrap();
            assert!(plan.evidence().divisions >= 2);
            let lowered = plan.lower(&source).unwrap();
            assert!(validate(&source, &plan, &lowered));
            for x in values(width) {
                for pointer in [4096, 4144, 4159, u64::MAX] {
                    let mut regs = vec![0xa123_ffff_7839_2084; 8];
                    regs[0] = x;
                    regs[x86::RDI] = pointer;
                    let memory = [0xa9; 64];
                    compare(&source, &lowered, &regs, &memory, true);
                    if pointer == 4096 {
                        let mut expanded = regs;
                        expanded.resize(lowered.register_count(), 0);
                        let run = lowered
                            .execute_with_memory(&expanded, 4096, &memory, 100)
                            .unwrap();
                        let quotient = signed(x.wrapping_add(13), width) / divisor;
                        assert_eq!(run.registers[1], quotient as u64 & width.mask());
                        assert_eq!(run.registers[2], quotient as u64);
                    }
                }
            }
        }
    }
}
fn source(width: Width, divisor: i64) -> Case {
    let expected_shift = if divisor.unsigned_abs() == 3 { 0 } else { 2 };
    let (_, shift) = cases(width)
        .into_iter()
        .find(|(d, s)| d.unsigned_abs() == divisor.unsigned_abs() && *s == expected_shift)
        .unwrap();
    let q = kernel(width, divisor, shift, true, false);
    let rem = word(
        b(B::Sub, r(6), b(B::Mul, q.clone(), c(divisor as u64))),
        width,
    );
    let mut assignments = vec![
        set(0, Expr::load(r(x86::RDI), Width::U64)),
        set(0, word(r(0), width)),
        set(1, r(0)),
        set(6, r(0)),
    ];
    let mut memo: Vec<(Expr, Reg)> = Vec::new();
    let mut next = 12;
    let mut overwritten = false;
    fn emit(
        e: &Expr,
        out: &mut Vec<Assignment>,
        memo: &mut Vec<(Expr, Reg)>,
        next: &mut usize,
        overwritten: &mut bool,
    ) -> Expr {
        if let Some((_, reg)) = memo.iter().find(|(old, _)| old == e) {
            return Expr::Register(*reg);
        }
        let value = match e {
            Expr::Unary(op, v) => Expr::unary(*op, emit(v, out, memo, next, overwritten)),
            Expr::Binary(op, a, z) => b(
                *op,
                emit(a, out, memo, next, overwritten),
                emit(z, out, memo, next, overwritten),
            ),
            Expr::Const(_) | Expr::Register(_) => return e.clone(),
            _ => panic!("this fixture decomposes only pure arithmetic"),
        };
        let reg = Reg(*next);
        *next += 1;
        out.push(set(reg.0, value));
        memo.push((e.clone(), reg));
        if matches!(e, Expr::Binary(B::Mul, ..)) && !*overwritten {
            *overwritten = true;
            out.extend([set(0, c(99)), set(1, c(123)), store(8, r(0))]);
        }
        Expr::Register(reg)
    }
    let Expr::Register(q) = emit(&q, &mut assignments, &mut memo, &mut next, &mut overwritten)
    else {
        panic!()
    };
    assignments.push(store(8, Expr::Register(q)));
    let Expr::Register(rem) = emit(
        &rem,
        &mut assignments,
        &mut memo,
        &mut next,
        &mut overwritten,
    ) else {
        panic!()
    };
    assignments.push(store(
        16,
        Expr::select(
            Expr::load(address(32), Width::U64),
            Expr::Register(rem),
            Expr::load(address(40), Width::U64),
        ),
    ));
    let result = b(
        B::Xor,
        Expr::Register(q),
        b(B::Shl, Expr::Register(rem), c(8)),
    );
    let p = Program::new(
        0,
        next,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control: Control::Return(result),
        }],
    )
    .unwrap();
    Case { program: p, q, rem }
}
fn values(width: Width) -> Vec<u64> {
    let mut values = inputs();
    let sign = 1u64 << (width.bits() - 1);
    values.extend([
        sign - 1,
        sign,
        sign + 1,
        width.mask(),
        width.mask() - 1,
        0x1_0000,
    ]);
    values
}
fn signed(x: u64, width: Width) -> i64 {
    crate::support::ir::unary_value(UnaryOp::SignExtend(width), x) as i64
}

#[test]
fn truncated_live_values_and_overwrites_preserve_every_original_state_and_cutoff() {
    let mut observations = 0;
    for width in WIDTHS {
        for divisor in [3, -3, 7, -7] {
            let case = source(width, divisor);
            for source in [case.program.clone(), split(&case.program)] {
                let plan = SemanticPlan::analyze(&source).expect("word graph plan");
                let e = plan.evidence();
                assert_eq!(
                    (e.inputs, e.divisions, e.remainders),
                    (1, 1, 1),
                    "{width:?}/{divisor}"
                );
                let lowered = plan.lower(&source).unwrap();
                assert!(validate(&source, &plan, &lowered));
                let compact = display_dce::propose(&lowered).unwrap();
                assert!(display_dce::validate(&lowered, &compact));
                for x in values(width) {
                    for pointer in [
                        4096,
                        4097,
                        4104,
                        4112,
                        4120,
                        4128,
                        4144,
                        4152,
                        4159,
                        u64::MAX,
                    ] {
                        let mut regs = vec![0xa654_9832_fedc_7711; source.register_count()];
                        regs[x86::RDI] = pointer;
                        let mut memory = [0x93; 64];
                        if let Some(offset) = pointer.checked_sub(4096).filter(|p| *p <= 56) {
                            memory[offset as usize..offset as usize + 8]
                                .copy_from_slice(&x.to_le_bytes());
                        }
                        compare(&source, &lowered, &regs, &memory, true);
                        compare(&source, &compact, &regs, &memory, false);
                        if pointer == 4096 {
                            let mut expanded = regs.clone();
                            expanded.resize(lowered.register_count(), 0);
                            let run = lowered
                                .execute_with_memory(&expanded, 4096, &memory, 1000)
                                .unwrap();
                            let x = signed(x, width);
                            assert_eq!(
                                run.registers[case.q.0],
                                (x / divisor) as u64 & width.mask()
                            );
                            assert_eq!(
                                run.registers[case.rem.0],
                                (x % divisor) as u64 & width.mask()
                            );
                        }
                        observations += 2 * (source.instructions().len() * 5 + 3);
                    }
                }
            }
        }
    }
    println!(
        "{observations} word source/lowered/DCE observations with full RAM, trace, registers, fault PC and budgets"
    );
}

#[test]
fn word_snapshots_repeat_across_signed_boundary_loop_iterations() {
    for width in WIDTHS {
        for divisor in [3, -7] {
            let case = source(width, divisor);
            let mut body = case.program.instructions()[0].assignments[1..].to_vec();
            body.extend([
                set(
                    10,
                    b(
                        B::Add,
                        r(10),
                        b(B::Xor, Expr::Register(case.q), Expr::Register(case.rem)),
                    ),
                ),
                set(9, b(B::Sub, r(9), c(1))),
            ]);
            let source = Program::new(
                0,
                case.program.register_count(),
                vec![
                    IrInstruction {
                        address: 0,
                        size: 1,
                        assignments: vec![set(9, c(3)), set(10, c(0))],
                        control: Control::Jump(2),
                    },
                    IrInstruction {
                        address: 1,
                        size: 1,
                        assignments: vec![set(0, word(b(B::Add, r(6), c(1)), width))],
                        control: Control::Jump(2),
                    },
                    IrInstruction {
                        address: 2,
                        size: 1,
                        assignments: body,
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
            let lowered = plan.lower(&source).unwrap();
            for x in values(width) {
                let mut regs = vec![0; source.register_count()];
                regs[0] = x;
                regs[x86::RDI] = 4096;
                compare(&source, &lowered, &regs, &[0x93; 64], true);
                let expected =
                    (0..3u64)
                        .map(|i| signed(x.wrapping_add(i), width))
                        .fold(0u64, |sum, x| {
                            sum.wrapping_add(
                                ((x / divisor) as u64 & width.mask())
                                    ^ ((x % divisor) as u64 & width.mask()),
                            )
                        });
                regs.resize(lowered.register_count(), 0);
                assert_eq!(
                    lowered
                        .execute_with_memory(&regs, 4096, &[0x93; 64], 32)
                        .unwrap()
                        .value,
                    expected
                );
            }
        }
    }
}

#[test]
fn wrong_width_and_load_replays_cannot_validate_as_word_captures() {
    let source = source(Width::U32, 7).program;
    let plan = SemanticPlan::analyze(&source).unwrap();
    let good = plan.lower(&source).unwrap();
    let mut bad = good.instructions().to_vec();
    fn narrow(e: &mut Expr) -> bool {
        match e {
            Expr::Unary(UnaryOp::SignExtend(Width::U32), _) => {
                let Expr::Unary(op, _) = e else {
                    unreachable!()
                };
                *op = UnaryOp::SignExtend(Width::U16);
                true
            }
            Expr::Unary(_, v) => narrow(v),
            Expr::Binary(_, a, z) => narrow(a) || narrow(z),
            _ => false,
        }
    }
    let mut changed = false;
    for a in &mut bad[0].assignments {
        if matches!(a.destination,Place::Register(Reg(n)) if n>=source.register_count())
            && narrow(&mut a.value)
        {
            changed = true;
            break;
        }
    }
    assert!(changed);
    let bad = Program::new(0, good.register_count(), bad).unwrap();
    assert!(!validate(&source, &plan, &bad));
    let mut regs = vec![0; good.register_count()];
    regs[x86::RDI] = 4096;
    let mut memory = [0x93; 64];
    memory[..8].copy_from_slice(&65536u64.to_le_bytes());
    assert_ne!(
        good.execute_with_memory(&regs, 4096, &memory, 32)
            .unwrap()
            .value,
        bad.execute_with_memory(&regs, 4096, &memory, 32)
            .unwrap()
            .value
    );
    fn replace(e: &mut Expr) {
        match e {
            Expr::Register(Reg(0)) => *e = Expr::load(r(x86::RDI), Width::U64),
            Expr::Unary(_, v) => replace(v),
            Expr::Binary(_, a, z) => {
                replace(a);
                replace(z)
            }
            _ => {}
        }
    }
    let mut q = kernel(Width::U32, 7, 2, true, false);
    replace(&mut q);
    let separate = Program::new(
        0,
        32,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(q),
        }],
    )
    .unwrap();
    assert!(SemanticPlan::analyze(&separate).is_none());
}

#[test]
fn word_c_generation_preserves_all_ram_and_first_fault_with_both_storage_modes() {
    let scratch = native::Scratch::new();
    let mut observations = 0;
    for width in WIDTHS {
        for divisor in [3, -7] {
            let source = source(width, divisor).program;
            let mut input = String::new();
            let mut expected = Vec::new();
            let mut statuses = [0; 3];
            for pointer in [4096, 4097, 4104, 4112, 4128, 4144, 4152, 4159, u64::MAX] {
                for x in values(width) {
                    writeln!(input, "{pointer} {x} 17 19 23").unwrap();
                    let mut memory: Vec<_> = (0..64usize)
                        .map(|i| i.wrapping_mul(29).wrapping_add(7) as u8)
                        .collect();
                    for (i, v) in [x, 17, 19, 23].into_iter().enumerate() {
                        if let Some(offset) = pointer
                            .checked_add(i as u64 * 8)
                            .and_then(|a| a.checked_sub(4096))
                            .filter(|p| *p <= 56)
                        {
                            memory[offset as usize..offset as usize + 8]
                                .copy_from_slice(&v.to_le_bytes());
                        }
                    }
                    let mut regs = vec![0; source.register_count()];
                    regs[x86::RDI] = pointer;
                    regs[x86::RSP] = 4160;
                    let report = source.run_with_memory(&regs, 4096, &memory, 32).unwrap();
                    let mut row = match report.status {
                        RunStatus::Returned(v) => {
                            statuses[0] += 1;
                            vec![0, 0, 0, 0, v]
                        }
                        RunStatus::Fault(f) => {
                            let a = if f.access == nirvana::ir::AccessKind::Read {
                                1
                            } else {
                                2
                            };
                            statuses[a] += 1;
                            vec![1, f.address, a as u64, f.width.bytes() as u64, 0]
                        }
                        _ => panic!("bounded straight line"),
                    };
                    row.extend(
                        report
                            .state
                            .memory
                            .chunks_exact(8)
                            .map(|b| u64::from_le_bytes(b.try_into().unwrap())),
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
                    let body = output
                        .code
                        .split("uint64_t nirvana_readable(")
                        .nth(1)
                        .unwrap();
                    assert!(
                        body.contains("nirvana_sdiv_word(") && body.contains("nirvana_srem_word("),
                        "{body}"
                    );
                    let file = scratch.0.join(format!(
                        "word-{}-{divisor}-{coalesce}-{objects}.c",
                        width.bits()
                    ));
                    std::fs::write(
                        &file,
                        checked_c::source(&output, source.register_count(), 4),
                    )
                    .unwrap();
                    for opt in ["-O0", "-O2"] {
                        let bin = file.with_extension(format!("{opt}.bin"));
                        native::compile_c(
                            &file,
                            &bin,
                            &[
                                opt,
                                "-fsanitize=undefined",
                                "-fno-sanitize-recover=undefined",
                            ],
                        );
                        assert_eq!(native::run_fields(&bin, &input, 13), expected);
                        observations += expected.len();
                    }
                }
            }
        }
    }
    println!("{observations} sanitized C word memory/fault observations");
}
