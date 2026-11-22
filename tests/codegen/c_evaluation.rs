use crate::support::checked_c;
use crate::support::native;

use native::{Scratch, link, object, run_fields};
use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus,
    Width,
};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use std::fmt::Write as _;

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: BinaryOp, a: Expr, b: Expr) -> Expr {
    Expr::binary(op, a, b)
}
fn load(address: Expr) -> Expr {
    Expr::load(address, Width::U64)
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
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

#[test]
fn native_c_sequences_binary_select_and_nested_address_faults() {
    let expressions = [
        b(BinaryOp::Add, load(r(0)), load(r(1))),
        b(BinaryOp::UMulHigh, load(r(0)), load(r(1))),
        b(BinaryOp::SMulHigh, load(r(0)), load(r(1))),
        b(BinaryOp::AShr, load(r(0)), load(r(1))),
        Expr::select(
            Expr::load(r(0), Width::U8),
            b(BinaryOp::Add, load(r(1)), load(c(0x1000))),
            load(c(0xffff)),
        ),
        load(load(r(0))),
        b(
            BinaryOp::Mul,
            c(0),
            b(BinaryOp::Add, load(r(0)), load(r(1))),
        ),
    ];
    let inputs: Vec<_> = [0x1000, 0x1008, 0x100f, 0xffff]
        .into_iter()
        .flat_map(|a| {
            [0x1000, 0x1008, 0x100f, 0xffff]
                .into_iter()
                .map(move |b| [a, b])
        })
        .collect();
    for expr in expressions {
        let p = Program::new(
            0,
            2,
            vec![instruction(
                0,
                vec![store(c(0x1000), Width::U64, c(0x1008))],
                Control::Return(expr),
            )],
        )
        .unwrap();
        compare(&p, &inputs);
    }
}

#[test]
fn native_c_shared_branch_return_keeps_prefix_writes_and_first_fault() {
    let result = b(BinaryOp::Add, load(r(1)), load(c(0x1000)));
    let program = Program::new(
        0,
        2,
        vec![
            instruction(
                0,
                vec![store(c(0x100f), Width::U8, c(0x7f))],
                Control::Branch {
                    condition: b(BinaryOp::Eq, load(r(0)), load(r(1))),
                    target: 3,
                },
            ),
            instruction(1, vec![store(r(0), Width::U8, c(0xaa))], Control::Next),
            instruction(2, vec![], Control::Return(result.clone())),
            instruction(3, vec![store(r(1), Width::U8, c(0xbb))], Control::Next),
            instruction(4, vec![], Control::Return(result)),
        ],
    )
    .unwrap();
    let inputs: Vec<_> = [0x1000, 0x1008, 0x100f, 0xffff]
        .into_iter()
        .flat_map(|a| {
            [0x1000, 0x1008, 0x100f, 0xffff]
                .into_iter()
                .map(move |b| [a, b])
        })
        .collect();
    let output = emit_readable_c_with_options(&program, ReadableOptions::default()).unwrap();
    let function = output
        .code
        .split("uint64_t nirvana_readable(")
        .nth(1)
        .unwrap();
    assert_eq!(function.matches("return ").count(), 1, "{function}");
    compare(&program, &inputs);
}

#[test]
fn native_c_continuations_share_cleanup_and_preserve_first_faults() {
    let inputs: Vec<_> = [0x1000, 0x1007, 0x1008, 0x100f, 0xffff, u64::MAX]
        .into_iter()
        .flat_map(|address| {
            [0, 1, 3, 0x1000, 0x1001, 0x100f, u64::MAX].map(|condition| [address, condition])
        })
        .collect();
    for width in [Width::U8, Width::U64] {
        for (memory_condition, changed_write, define_local) in [
            (false, false, false),
            (true, false, false),
            (false, true, false),
            (false, false, true),
        ] {
            let cleanup = store(
                r(0),
                width,
                if define_local {
                    r(2)
                } else {
                    load(b(BinaryOp::Add, r(0), c(1)))
                },
            );
            let mut taken_cleanup = cleanup.clone();
            if changed_write {
                taken_cleanup.value = b(BinaryOp::Add, taken_cleanup.value, c(1));
            }
            let condition = if memory_condition {
                b(BinaryOp::And, Expr::load(r(1), Width::U8), c(1))
            } else {
                r(1)
            };
            let result = b(
                BinaryOp::Add,
                r(1),
                if define_local { r(2) } else { load(r(0)) },
            );
            let definition = |value| {
                if define_local {
                    vec![Assignment {
                        destination: Reg(2).into(),
                        value: b(BinaryOp::Add, Expr::load(r(0), Width::U8), c(value)),
                    }]
                } else {
                    vec![]
                }
            };
            let program = Program::new(
                0,
                if define_local { 3 } else { 2 },
                vec![
                    instruction(
                        0,
                        vec![store(c(0x100f), Width::U8, c(0x55))],
                        Control::Branch {
                            condition,
                            target: 4,
                        },
                    ),
                    instruction(1, definition(7), Control::Next),
                    instruction(2, vec![cleanup.clone()], Control::Next),
                    instruction(3, vec![], Control::Return(result.clone())),
                    instruction(4, definition(9), Control::Next),
                    instruction(5, vec![taken_cleanup], Control::Next),
                    instruction(6, vec![], Control::Return(result)),
                ],
            )
            .unwrap();
            let output = emit_readable_c_with_options(
                &program,
                ReadableOptions {
                    coalesce_locals: true,
                    ..ReadableOptions::default()
                },
            )
            .unwrap();
            if !memory_condition && !changed_write && !define_local {
                assert_eq!(output.continuations.unwrap().removed_conditions, 1);
            } else if let Some(evidence) = output.continuations {
                assert_eq!(evidence.removed_conditions, 0, "{}", output.code);
            }
            if define_local {
                assert!(output.continuations.is_some(), "{}", output.code);
            }
            compare(&program, &inputs);
        }
    }
}

#[test]
fn native_c_equal_branch_bodies_still_evaluate_ordered_faulting_condition() {
    let result = b(BinaryOp::Xor, load(c(0x1000)), r(1));
    for condition in [
        r(0),
        Expr::select(
            b(BinaryOp::And, Expr::load(r(0), Width::U8), c(1)),
            b(BinaryOp::Eq, load(r(1)), load(c(0x1000))),
            load(c(0xfffe)),
        ),
    ] {
        let program = Program::new(
            0,
            2,
            vec![
                instruction(
                    0,
                    vec![store(c(0x100f), Width::U8, c(0x5a))],
                    Control::Branch {
                        condition,
                        target: 2,
                    },
                ),
                instruction(1, vec![], Control::Return(result.clone())),
                instruction(2, vec![], Control::Return(result.clone())),
            ],
        )
        .unwrap();
        let output = emit_readable_c_with_options(&program, ReadableOptions::default()).unwrap();
        let function = output
            .code
            .split("uint64_t nirvana_readable(")
            .nth(1)
            .unwrap();
        assert_eq!(function.matches("return ").count(), 1, "{function}");
        assert!(function.contains("(void)("), "{function}");
        compare(
            &program,
            &[
                [0, 0x1008],
                [0x1000, 0x1008],
                [0x1008, 0x1000],
                [0xffff, 0x1008],
                [0x1000, 0xffff],
                [0x100f, 0x1008],
                [0x100f, 0xffff],
            ],
        );
    }
}

#[test]
fn native_c_sequences_store_address_before_rhs_and_commits_nothing_after_fault() {
    let p = Program::new(
        0,
        2,
        vec![instruction(
            0,
            vec![
                store(c(0x1000), Width::U64, c(0x1008)),
                store(
                    b(BinaryOp::Add, load(r(0)), load(r(1))),
                    Width::U8,
                    b(BinaryOp::Add, load(r(1)), load(r(0))),
                ),
                store(c(0x1000), Width::U8, c(0xee)),
            ],
            Control::Return(c(7)),
        )],
    )
    .unwrap();
    let inputs: Vec<_> = [0x1000, 0x1008, 0xffff]
        .into_iter()
        .flat_map(|a| [0x1000, 0x1008, 0xffff].into_iter().map(move |b| [a, b]))
        .collect();
    compare(&p, &inputs);
}

#[test]
fn native_c_repeats_sequenced_loop_conditions_at_each_iteration() {
    let condition = b(
        BinaryOp::Eq,
        Expr::load(r(0), Width::U8),
        Expr::load(r(1), Width::U8),
    );
    let p = Program::new(
        0,
        2,
        vec![
            instruction(
                0,
                vec![
                    store(c(0x1000), Width::U8, c(2)),
                    store(c(0x1008), Width::U8, c(5)),
                ],
                Control::Next,
            ),
            instruction(
                1,
                vec![],
                Control::Branch {
                    condition,
                    target: 3,
                },
            ),
            instruction(
                2,
                vec![store(
                    c(0x1000),
                    Width::U8,
                    b(BinaryOp::Add, Expr::load(c(0x1000), Width::U8), c(1)),
                )],
                Control::Jump(1),
            ),
            instruction(3, vec![], Control::Return(Expr::load(c(0x1000), Width::U8))),
        ],
    )
    .unwrap();
    compare(
        &p,
        &[
            [0x1000, 0x1008],
            [0x1008, 0x1000],
            [0x1000, 0x1000],
            [0x1008, 0x1008],
            [0xffff, 0x1008],
            [0x1000, 0xffff],
        ],
    );
}

#[test]
fn sequencing_limits_return_an_error_instead_of_emitting_an_unordered_expression() {
    let mut value = r(0);
    for _ in 0..130 {
        value = load(value);
    }
    let program = Program::new(0, 2, vec![instruction(0, vec![], Control::Return(value))]).unwrap();
    let error = emit_readable_c_with_options(&program, ReadableOptions::default()).unwrap_err();
    assert!(
        matches!(error, nirvana::readable::ReadableError::Sequencing(_)),
        "{error}"
    );
}

#[test]
fn native_c_limit_identity_excludes_an_earlier_unrelated_byte_lifetime() {
    let program = Program::new(
        0,
        6,
        vec![
            instruction(
                0,
                vec![
                    Assignment {
                        destination: Reg(2).into(),
                        value: Expr::load(r(0), Width::U8),
                    },
                    store(c(0x100f), Width::U8, r(2)),
                    Assignment {
                        destination: Reg(3).into(),
                        value: b(
                            BinaryOp::Add,
                            b(BinaryOp::And, Expr::load(r(1), Width::U8), c(3)),
                            c(1),
                        ),
                    },
                    Assignment {
                        destination: Reg(4).into(),
                        value: c(0),
                    },
                    Assignment {
                        destination: Reg(5).into(),
                        value: c(0),
                    },
                ],
                Control::Next,
            ),
            instruction(
                1,
                vec![],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(4), r(3)),
                    target: 3,
                },
            ),
            instruction(
                2,
                vec![],
                Control::Return(b(BinaryOp::Xor, r(5), load(r(0)))),
            ),
            instruction(
                3,
                vec![
                    store(r(0), Width::U8, r(4)),
                    Assignment {
                        destination: Reg(5).into(),
                        value: b(BinaryOp::Add, r(5), r(4)),
                    },
                    Assignment {
                        destination: Reg(4).into(),
                        value: b(BinaryOp::Add, r(4), c(1)),
                    },
                ],
                Control::Jump(1),
            ),
        ],
    )
    .unwrap();
    let reduced = nirvana::reduce::reduce(&program).unwrap();
    let Place::Register(early_byte) =
        reduced.program().instructions()[0].assignments[0].destination
    else {
        panic!("fixture must retain the early faulting byte read");
    };
    let output = emit_readable_c_with_options(
        &program,
        ReadableOptions {
            coalesce_locals: true,
            compact_memory: true,
            ..Default::default()
        },
    )
    .unwrap();
    let limit = output
        .locals
        .iter()
        .find(|local| local.role == Some(nirvana::value_role::ValueRole::Limit))
        .expect("the cached loop bound has an invariant limit role");
    assert!(!limit.registers.contains(&early_byte), "{output:?}");
    assert!(output.local_plan.split_storage_groups > 0, "{output:?}");
    assert!(output.local_plan.local_variables > output.local_plan.storage_slots);
    assert_eq!(
        output.structure_evidence,
        Some(
            nirvana::structure::StructuredFunction::recover(reduced.program())
                .unwrap()
                .evidence()
        ),
        "local identity planning must not change the checked AST"
    );
    compare(
        &program,
        &[
            [0x1000, 0x1008],
            [0x1008, 0x1000],
            [0x100f, 0x1008],
            [0xffff, 0x1008],
            [0x1000, 0xffff],
            [0xffff, 0xffff],
        ],
    );
}

#[test]
fn native_c_input_register_reused_as_counter_gets_a_separate_definition_web() {
    let program = Program::new(
        0,
        5,
        vec![
            instruction(
                0,
                vec![
                    Assignment {
                        destination: Reg(2).into(),
                        value: Expr::load(r(0), Width::U8),
                    },
                    store(c(0x100f), Width::U8, r(2)),
                    Assignment {
                        destination: Reg(3).into(),
                        value: b(BinaryOp::And, Expr::load(r(1), Width::U8), c(3)),
                    },
                    Assignment {
                        destination: Reg(0).into(),
                        value: c(0),
                    },
                    Assignment {
                        destination: Reg(4).into(),
                        value: c(0),
                    },
                ],
                Control::Next,
            ),
            instruction(
                1,
                vec![],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(0), r(3)),
                    target: 3,
                },
            ),
            instruction(
                2,
                vec![],
                Control::Return(b(BinaryOp::Add, r(4), load(c(0x1000)))),
            ),
            instruction(
                3,
                vec![
                    Assignment {
                        destination: Reg(4).into(),
                        value: b(BinaryOp::Add, r(4), r(0)),
                    },
                    Assignment {
                        destination: Reg(0).into(),
                        value: b(BinaryOp::Add, r(0), c(1)),
                    },
                    store(c(0x100e), Width::U8, r(0)),
                    store(b(BinaryOp::Add, r(1), c(8)), Width::U8, r(0)),
                ],
                Control::Jump(1),
            ),
        ],
    )
    .unwrap();
    let reduced = nirvana::reduce::reduce(&program).unwrap();
    let output = emit_readable_c_with_options(
        &program,
        ReadableOptions {
            coalesce_locals: true,
            compact_memory: true,
            ..Default::default()
        },
    )
    .unwrap();
    assert_eq!(output.parameters, reduced.parameters());
    assert!(
        matches!(
            output.web_recovery,
            nirvana::readable::WebRecovery::Applied { .. }
        ),
        "{output:?}"
    );
    assert!(
        output
            .locals
            .iter()
            .any(|local| local.role == Some(nirvana::value_role::ValueRole::Counter)),
        "the counter must no longer be trapped in the input parameter's name: {output:?}"
    );
    assert_eq!(
        output.structure_evidence,
        Some(
            nirvana::structure::StructuredFunction::recover(reduced.program())
                .unwrap()
                .evidence()
        ),
    );
    assert!(output.display_structure_evidence.is_some());
    compare(
        &program,
        &[
            [0x1000, 0x1000],
            [0x1000, 0x1008],
            [0x100f, 0x1000],
            [0xffff, 0x1000],
            [0x1000, 0xffff],
            [0xffff, 0xffff],
        ],
    );
}

#[test]
fn native_c_web_rendering_retries_original_ir_when_temporary_ids_overflow() {
    // This sparse input is valid without allocating a register-count-sized
    // interpreter bank. Reduction uses two IDs; the optional web uses one more.
    // Two final Load temporaries fit only when the original IR is rendered.
    let program = Program::new(
        0,
        usize::MAX - 4,
        vec![
            instruction(
                0,
                vec![Assignment {
                    destination: Reg(0).into(),
                    value: c(1),
                }],
                Control::Jump(1),
            ),
            instruction(
                1,
                vec![
                    store(c(0x1000), Width::U8, r(0)),
                    Assignment {
                        destination: Reg(0).into(),
                        value: c(2),
                    },
                ],
                Control::Jump(2),
            ),
            instruction(
                2,
                vec![store(c(0x1008), Width::U8, r(0))],
                Control::Return(b(BinaryOp::Add, load(c(0x1000)), load(c(0x1008)))),
            ),
        ],
    )
    .unwrap();
    let scratch = Scratch::new();
    for compact in [false, true] {
        let output = emit_readable_c_with_options(
            &program,
            ReadableOptions {
                coalesce_locals: compact,
                compact_memory: compact,
                ..Default::default()
            },
        )
        .unwrap();
        assert!(
            matches!(
                output.web_recovery,
                nirvana::readable::WebRecovery::RenderingFallback(
                    nirvana::readable::ReadableError::Sequencing(_)
                )
            ),
            "{output:?}"
        );
        assert_eq!(output.structure_evidence, output.display_structure_evidence);
        assert!(output.parameters.is_empty());
        for opt in ["-O0", "-O2"] {
            let source = scratch.0.join(format!("web-fallback-{compact}{opt}.c"));
            std::fs::write(
                &source,
                output.code.clone()
                    + r#"
#include <stdio.h>
int main(void) {
    uint8_t memory[16] = {0};
    printf("%llu\n", (unsigned long long)nirvana_readable(memory, UINT64_C(4096), sizeof(memory)));
    return 0;
}
"#,
            )
            .unwrap();
            let compiled = source.with_extension("o");
            let binary = source.with_extension("bin");
            object(&source, &compiled, opt, "nirvana_readable");
            link(&[&compiled], &binary);
            assert_eq!(native::run_fields(&binary, "", 1), vec![vec![3]]);
        }
    }
}

#[test]
fn native_c_independent_pointer_reloads_can_share_an_address_local() {
    let program = Program::new(
        0,
        6,
        vec![instruction(
            0,
            vec![
                store(c(0x1000), Width::U64, c(0x1008)),
                store(c(0x1008), Width::U64, c(0x100f)),
                Assignment {
                    destination: Reg(2).into(),
                    value: load(r(0)),
                },
                Assignment {
                    destination: Reg(3).into(),
                    value: Expr::load(r(2), Width::U8),
                },
                store(c(0x100e), Width::U8, r(3)),
                Assignment {
                    destination: Reg(4).into(),
                    value: load(r(1)),
                },
                Assignment {
                    destination: Reg(5).into(),
                    value: Expr::load(r(4), Width::U8),
                },
            ],
            Control::Return(b(BinaryOp::Add, r(5), Expr::load(c(0x100e), Width::U8))),
        )],
    )
    .unwrap();
    let output = emit_readable_c_with_options(
        &program,
        ReadableOptions {
            coalesce_locals: true,
            compact_memory: true,
            ..Default::default()
        },
    )
    .unwrap();
    assert_eq!(
        output
            .locals
            .iter()
            .filter(|local| local.role == Some(nirvana::value_role::ValueRole::Address))
            .count(),
        1,
        "same-role pointer temporaries need not each get a declaration: {output:?}"
    );
    assert!(output.local_plan.identity_groups.unwrap() > output.local_plan.local_variables);
    compare(
        &program,
        &[
            [0x1000, 0x1000],
            [0x1000, 0x1008],
            [0x1000, 0xffff],
            [0x1008, 0x1000],
            [0xffff, 0x1000],
            [0xffff, 0xffff],
        ],
    );
}

#[test]
fn coalesced_load_chains_use_one_local_and_keep_faulting_memory_effects() {
    let p = Program::new(
        0,
        4,
        vec![instruction(
            0,
            vec![
                Assignment {
                    destination: Reg(1).into(),
                    value: load(r(0)),
                },
                store(b(BinaryOp::Add, r(0), c(8)), Width::U64, r(1)),
                Assignment {
                    destination: Reg(2).into(),
                    value: load(b(BinaryOp::Add, r(0), c(8))),
                },
                store(r(0), Width::U64, b(BinaryOp::Add, r(2), c(1))),
                Assignment {
                    destination: Reg(3).into(),
                    value: load(r(0)),
                },
            ],
            Control::Return(r(3)),
        )],
    )
    .unwrap();
    let separate = emit_readable_c_with_options(&p, ReadableOptions::default()).unwrap();
    let coalesced = emit_readable_c_with_options(
        &p,
        ReadableOptions {
            coalesce_locals: true,
            ..Default::default()
        },
    )
    .unwrap();
    assert!(separate.locals.len() <= 3);
    assert!(coalesced.locals.len() <= 1);
    compare(&p, &[[0x1000, 0], [0x1008, 0], [0xffff, 0]]);
}

#[test]
fn native_c_split_cycle_sequences_dispatch_faults_before_entering_a_cycle() {
    let increment = || Assignment {
        destination: Reg(2).into(),
        value: b(BinaryOp::Add, r(2), c(1)),
    };
    let p = Program::new(
        0,
        3,
        vec![
            instruction(
                0,
                vec![
                    Assignment {
                        destination: Reg(2).into(),
                        value: c(0),
                    },
                    store(c(0x1000), Width::U8, c(2)),
                ],
                Control::Branch {
                    condition: b(
                        BinaryOp::Eq,
                        Expr::load(r(0), Width::U8),
                        Expr::load(r(1), Width::U8),
                    ),
                    target: 2,
                },
            ),
            instruction(
                1,
                vec![increment()],
                Control::Branch {
                    condition: b(BinaryOp::Ule, c(3), r(2)),
                    target: 3,
                },
            ),
            instruction(
                2,
                vec![increment()],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(2), c(3)),
                    target: 1,
                },
            ),
            instruction(3, vec![], Control::Return(r(2))),
        ],
    )
    .unwrap();
    let output = emit_readable_c_with_options(&p, ReadableOptions::default()).unwrap();
    assert!(output.fallback_reason.is_none());
    assert!(output.structure_evidence.is_some());
    compare(
        &p,
        &[
            [0x1000, 0x1008],
            [0x1008, 0x1000],
            [0x1000, 0x1000],
            [0xffff, 0x1008],
            [0x1000, 0xffff],
            [0xffff, 0xffff],
        ],
    );
}

#[test]
fn native_c_goto_fallback_sequences_dispatch_faults_before_a_three_entry_cycle() {
    let mut instructions = vec![
        instruction(
            0,
            vec![
                Assignment {
                    destination: Reg(2).into(),
                    value: c(0),
                },
                store(c(0x1000), Width::U8, c(2)),
            ],
            Control::Branch {
                condition: b(
                    BinaryOp::Eq,
                    Expr::load(r(0), Width::U8),
                    Expr::load(r(1), Width::U8),
                ),
                target: 10,
            },
        ),
        instruction(
            1,
            vec![],
            Control::Branch {
                condition: b(BinaryOp::And, r(0), c(8)),
                target: 20,
            },
        ),
        instruction(2, vec![], Control::Jump(30)),
    ];
    for (entry, next) in [(10, 20), (20, 30), (30, 10)] {
        instructions.push(instruction(
            entry,
            vec![Assignment {
                destination: Reg(2).into(),
                value: b(BinaryOp::Add, r(2), c(1)),
            }],
            Control::Branch {
                condition: b(BinaryOp::Ule, c(3), r(2)),
                target: 40,
            },
        ));
        instructions.push(instruction(entry + 1, vec![], Control::Jump(next)));
    }
    instructions.push(instruction(40, vec![], Control::Return(r(2))));
    let p = Program::new(0, 3, instructions).unwrap();
    let output = emit_readable_c_with_options(&p, ReadableOptions::default()).unwrap();
    assert!(output.fallback_reason.is_some());
    assert!(output.code.contains("goto bb"));
    compare(
        &p,
        &[
            [0x1000, 0x1008],
            [0x1008, 0x1000],
            [0x1000, 0x1000],
            [0xffff, 0x1008],
            [0x1000, 0xffff],
            [0xffff, 0xffff],
        ],
    );
}

#[test]
fn native_c_while_setup_fault_after_multiple_iterations_keeps_body_writes() {
    let p = Program::new(
        0,
        4,
        vec![
            instruction(0, vec![], Control::Next),
            instruction(
                1,
                vec![
                    Assignment {
                        destination: Reg(2).into(),
                        value: Expr::load(r(0), Width::U8),
                    },
                    Assignment {
                        destination: Reg(3).into(),
                        value: Expr::load(r(1), Width::U8),
                    },
                ],
                Control::Branch {
                    condition: b(BinaryOp::Eq, r(2), c(0)),
                    target: 3,
                },
            ),
            instruction(
                2,
                vec![
                    store(c(0x1008), Width::U8, c(255)),
                    Assignment {
                        destination: Reg(0).into(),
                        value: b(BinaryOp::Add, r(0), c(1)),
                    },
                ],
                Control::Jump(1),
            ),
            instruction(3, vec![], Control::Return(c(7))),
        ],
    )
    .unwrap();
    compare(&p, &[[0x1000, 0x1008], [0x100f, 0x1008], [0x1000, 0xffff]]);
}

#[test]
fn native_c_while_setup_loads_repeat_in_order_including_final_visit_and_fault() {
    let p = Program::new(
        0,
        4,
        vec![
            instruction(
                0,
                vec![
                    store(c(0x1000), Width::U8, c(2)),
                    store(c(0x1008), Width::U8, c(5)),
                ],
                Control::Next,
            ),
            instruction(
                1,
                vec![
                    Assignment {
                        destination: Reg(2).into(),
                        value: Expr::load(r(0), Width::U8),
                    },
                    Assignment {
                        destination: Reg(3).into(),
                        value: Expr::load(r(1), Width::U8),
                    },
                ],
                Control::Branch {
                    condition: b(BinaryOp::Eq, r(2), r(3)),
                    target: 3,
                },
            ),
            instruction(
                2,
                vec![store(
                    c(0x1000),
                    Width::U8,
                    b(BinaryOp::Add, Expr::load(c(0x1000), Width::U8), c(1)),
                )],
                Control::Jump(1),
            ),
            instruction(3, vec![], Control::Return(Expr::load(c(0x1000), Width::U8))),
        ],
    )
    .unwrap();
    let output = emit_readable_c_with_options(&p, ReadableOptions::default()).unwrap();
    let header = output.code.find("while (1) {").expect("setup-bearing loop");
    let first = output.code[header..]
        .find("nirvana_load(&m, arg0, 1)")
        .unwrap()
        + header;
    let second = output.code[header..]
        .find("nirvana_load(&m, arg1, 1)")
        .unwrap()
        + header;
    let exit = output.code[header..].find("break;").unwrap() + header;
    assert!(
        header < first && first < second && second < exit,
        "{}",
        output.code
    );
    compare(
        &p,
        &[
            [0x1000, 0x1008],
            [0x1008, 0x1000],
            [0x1000, 0x1000],
            [0x1008, 0x1008],
            [0xffff, 0x1008],
            [0x1000, 0xffff],
        ],
    );
}

#[test]
fn native_c_width_normalization_keeps_dependencies_in_loop_and_diamond_guards() {
    // Width analysis exposes x ^ x. General algebra run only at C rendering
    // used to drop the last read after local allocation, producing a variable
    // that GCC rejected as unused-but-set under the fixture flags.
    for op in [BinaryOp::Xor, BinaryOp::Eq, BinaryOp::Ult, BinaryOp::Ule] {
        let same = || b(op, b(BinaryOp::And, r(2), c(0xffff_ffff)), r(2));
        let read = || {
            vec![Assignment {
                destination: Reg(2).into(),
                value: Expr::load(r(0), Width::U8),
            }]
        };
        let loop_program = Program::new(
            0,
            3,
            vec![
                instruction(
                    0,
                    read(),
                    Control::Branch {
                        condition: b(BinaryOp::Eq, same(), r(1)),
                        target: 2,
                    },
                ),
                instruction(1, vec![store(c(0xffff), Width::U8, c(9))], Control::Jump(0)),
                instruction(2, vec![], Control::Return(c(7))),
            ],
        )
        .unwrap();
        let diamond = Program::new(
            0,
            3,
            vec![
                instruction(
                    0,
                    read(),
                    Control::Branch {
                        condition: same(),
                        target: 2,
                    },
                ),
                instruction(1, vec![], Control::Return(c(7))),
                instruction(2, vec![], Control::Return(c(11))),
            ],
        )
        .unwrap();
        for program in [&loop_program, &diamond] {
            compare(
                program,
                &[[0x1000, 0], [0x1000, 1], [0xffff, 0], [0xffff, 1]],
            );
        }
    }
}

#[test]
fn native_c_for_updates_keep_setup_break_continue_and_fault_order() {
    for mode in 0..3 {
        let body_control = match mode {
            1 => Control::Branch {
                condition: b(BinaryOp::Eq, r(2), c(3)),
                target: 2,
            },
            2 => Control::Branch {
                condition: b(BinaryOp::Eq, r(2), c(2)),
                target: 1,
            },
            _ => Control::Next,
        };
        let mut body = vec![store(c(0x100f), Width::U8, r(2))];
        if mode == 2 {
            body.push(store(c(0x1000), Width::U8, b(BinaryOp::Add, r(2), c(1))));
        }
        let p = Program::new(
            0,
            4,
            vec![
                instruction(
                    0,
                    vec![
                        store(c(0x1000), Width::U8, c(2)),
                        store(c(0x1008), Width::U8, c(5)),
                    ],
                    Control::Next,
                ),
                instruction(
                    1,
                    vec![
                        Assignment {
                            destination: Reg(2).into(),
                            value: Expr::load(c(0x1000), Width::U8),
                        },
                        Assignment {
                            destination: Reg(3).into(),
                            value: Expr::load(r(1), Width::U8),
                        },
                    ],
                    Control::Branch {
                        condition: b(BinaryOp::Ult, r(2), r(3)),
                        target: 3,
                    },
                ),
                instruction(2, vec![], Control::Return(Expr::load(c(0x1000), Width::U8))),
                instruction(3, body, body_control),
                instruction(
                    4,
                    vec![Assignment {
                        destination: Reg(2).into(),
                        value: Expr::load(c(0x1000), Width::U8),
                    }],
                    Control::Next,
                ),
                // r0 may fault here, after body writes. It need not alias the load
                // for moving this exact suffix to a for update to be equivalent.
                instruction(
                    5,
                    vec![store(r(0), Width::U8, b(BinaryOp::Add, r(2), c(1)))],
                    Control::Jump(1),
                ),
            ],
        )
        .unwrap();
        let output = emit_readable_c_with_options(
            &p,
            ReadableOptions {
                coalesce_locals: true,
                compact_memory: true,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(
            output.code.contains("for (; ") || output.code.contains("for (;\n"),
            mode != 2,
            "mode={mode}: {}",
            output.code
        );
        compare(
            &p,
            &[
                [0x1000, 0x1008],
                [0xffff, 0x1008],
                [0x1000, 0xffff],
                [0xffff, 0xffff],
            ],
        );
    }
}

#[test]
fn native_c_compound_spines_keep_unsigned_wraparound_narrowing_and_faults() {
    for op in [
        BinaryOp::Add,
        BinaryOp::Mul,
        BinaryOp::And,
        BinaryOp::Or,
        BinaryOp::Xor,
    ] {
        let narrow = matches!(op, BinaryOp::And | BinaryOp::Or | BinaryOp::Xor);
        let width = if narrow { Width::U16 } else { Width::U64 };
        let constant = if narrow { 0x0fff } else { u64::MAX };
        let p = Program::new(
            0,
            3,
            vec![instruction(
                0,
                vec![
                    store(c(0x1000), width, r(1)),
                    Assignment {
                        destination: Reg(2).into(),
                        value: Expr::load(c(0x1000), width),
                    },
                    store(c(0x100e), Width::U8, c(0xaa)),
                    Assignment {
                        destination: Reg(2).into(),
                        value: b(op, b(op, r(2), c(constant)), Expr::load(r(0), Width::U16)),
                    },
                ],
                Control::Return(r(2)),
            )],
        )
        .unwrap();
        let output = emit_readable_c_with_options(
            &p,
            ReadableOptions {
                coalesce_locals: true,
                compact_memory: true,
                ..Default::default()
            },
        )
        .unwrap();
        let symbol = match op {
            BinaryOp::Add => "+=",
            BinaryOp::Mul => "*=",
            BinaryOp::And => "&=",
            BinaryOp::Or => "|=",
            BinaryOp::Xor => "^=",
            _ => unreachable!(),
        };
        assert!(output.code.contains(symbol), "op={op:?}: {}", output.code);
        compare(
            &p,
            &[
                [0x1000, 0],
                [0x1000, u64::MAX],
                [0x1008, 1 << 63],
                [0xffff, u64::MAX],
            ],
        );
    }
}

#[test]
fn native_c_guard_copyback_keeps_load_temporaries_when_address_views_hide_uses() {
    let p = Program::new(
        0,
        4,
        vec![
            instruction(
                0,
                vec![store(c(0x1008), Width::U64, b(BinaryOp::Add, r(0), c(8)))],
                Control::Branch {
                    condition: b(BinaryOp::Ne, r(0), r(1)),
                    target: 2,
                },
            ),
            instruction(1, vec![], Control::Jump(6)),
            instruction(
                2,
                vec![Assignment {
                    destination: Reg(3).into(),
                    value: load(r(0)),
                }],
                Control::Next,
            ),
            instruction(
                3,
                vec![Assignment {
                    destination: Reg(2).into(),
                    value: load(c(0x1008)),
                }],
                Control::Next,
            ),
            instruction(
                4,
                vec![Assignment {
                    destination: Reg(3).into(),
                    value: load(r(2)),
                }],
                Control::Next,
            ),
            instruction(
                5,
                vec![Assignment {
                    destination: Reg(0).into(),
                    value: r(2),
                }],
                Control::Branch {
                    condition: b(BinaryOp::Ne, r(2), r(1)),
                    target: 2,
                },
            ),
            instruction(6, vec![], Control::Return(c(7))),
        ],
    )
    .unwrap();
    // Copyback can be printed as a view address rather than a read of r2.
    // Removing r2 from the guard must not leave its checked load assigned to
    // an unread C local, or lose that load's modeled fault.
    compare(&p, &[[0x1000, 0x1008], [0x1000, 0x1000], [0xffff, 0x1008]]);
}

#[test]
fn native_c_guard_copyback_does_not_introduce_tautological_comparisons() {
    let p = Program::new(
        0,
        3,
        vec![
            instruction(
                0,
                vec![Assignment {
                    destination: Reg(0).into(),
                    value: c(0),
                }],
                Control::Jump(1),
            ),
            instruction(
                1,
                vec![],
                Control::Branch {
                    condition: b(BinaryOp::Eq, r(0), c(0)),
                    target: 5,
                },
            ),
            instruction(
                2,
                vec![Assignment {
                    destination: Reg(2).into(),
                    value: Expr::load(c(0x1000), Width::U8),
                }],
                Control::Jump(3),
            ),
            instruction(
                3,
                vec![Assignment {
                    destination: Reg(0).into(),
                    value: r(2),
                }],
                Control::Jump(4),
            ),
            instruction(
                4,
                vec![],
                Control::Branch {
                    condition: b(BinaryOp::Ne, r(2), r(0)),
                    target: 2,
                },
            ),
            instruction(5, vec![], Control::Return(c(7))),
        ],
    )
    .unwrap();
    // Initial constants make the entry false. Copy equivalence alone would
    // allow a while(x!=x), rejected by the same strict compiler flags. Keep
    // the original shape instead of introducing late dependency removal.
    compare(&p, &[[0x1000, 0x1008], [0xffff, u64::MAX]]);
}

#[test]
fn native_c_stack_lineage_names_keep_alias_writes_and_first_fault() {
    let second = b(BinaryOp::Add, r(0), c(8));
    let program = Program::new(
        0,
        4,
        vec![
            instruction(
                0,
                vec![
                    store(r(0), Width::U64, c(0)),
                    store(second.clone(), Width::U64, c(1)),
                ],
                Control::Next,
            ),
            instruction(
                1,
                vec![Assignment {
                    destination: Reg(2).into(),
                    value: load(r(0)),
                }],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(2), c(3)),
                    target: 3,
                },
            ),
            instruction(
                2,
                vec![store(r(1), Width::U8, c(0xaa))],
                Control::Return(load(second.clone())),
            ),
            instruction(
                3,
                vec![
                    Assignment {
                        destination: Reg(3).into(),
                        value: load(second.clone()),
                    },
                    store(second, Width::U64, b(BinaryOp::Add, r(3), r(2))),
                    store(r(0), Width::U64, b(BinaryOp::Add, r(2), c(1))),
                ],
                Control::Jump(1),
            ),
        ],
    )
    .unwrap();
    let output = emit_readable_c_with_options(
        &program,
        ReadableOptions {
            stack_register: Some(Reg(0)),
            coalesce_locals: true,
            compact_memory: true,
            ..Default::default()
        },
    )
    .unwrap();
    for role in [
        nirvana::value_role::ValueRole::Counter,
        nirvana::value_role::ValueRole::Accumulator,
    ] {
        assert!(
            output.locals.iter().any(|local| local.role == Some(role)),
            "missing {role:?} across stack reloads: {}",
            output.code
        );
    }
    let inputs: Vec<_> = [0x1000, 0x1008, 0x100f, 0xffff]
        .into_iter()
        .flat_map(|stack| {
            [0x1000, 0x1008, 0x100f, 0xffff]
                .into_iter()
                .map(move |alias| [stack, alias])
        })
        .collect();
    compare_with_stack(&program, &inputs, Some(Reg(0)));
}

#[test]
fn native_c_source_lineage_across_storage_widths_retains_full_values_and_faults() {
    let program = Program::new(
        0,
        4,
        vec![
            instruction(
                0,
                vec![Assignment {
                    destination: Reg(2).into(),
                    value: b(BinaryOp::Xor, r(1), c(u64::MAX)),
                }],
                Control::Jump(1),
            ),
            instruction(
                1,
                vec![
                    store(r(0), Width::U8, r(2)),
                    Assignment {
                        destination: Reg(3).into(),
                        value: Expr::load(r(0), Width::U8),
                    },
                ],
                Control::Return(r(3)),
            ),
        ],
    )
    .unwrap();
    let output = emit_readable_c_with_options(
        &program,
        ReadableOptions {
            stack_register: Some(Reg(0)),
            coalesce_locals: true,
            compact_memory: true,
            ..Default::default()
        },
    )
    .unwrap();
    if let Some(recovery) = output.local_plan.source_allocation {
        assert!(recovery.after.locals < recovery.before.locals);
    } else {
        // Checked reload identities can expose the full-width copy before
        // source-lineage allocation, making that later merge redundant.
        assert!(output.memory_values.is_some());
    }
    assert_eq!(
        output.locals.len(),
        1,
        "{:?}\n{}",
        output.local_plan,
        output.code
    );
    assert_eq!(output.locals[0].width, Width::U64);
    let inputs: Vec<_> = [0x1000, 0x100f, 0xffff]
        .into_iter()
        .flat_map(|stack| {
            [0, 255, 256, u64::MAX, 1 << 63]
                .into_iter()
                .map(move |value| [stack, value])
        })
        .collect();
    compare_with_stack(&program, &inputs, Some(Reg(0)));
}

#[test]
fn native_c_load_cell_identity_never_caches_a_value_across_an_aliasing_store() {
    let program = Program::new(
        0,
        4,
        vec![
            instruction(0, vec![store(r(0), Width::U64, c(1))], Control::Jump(1)),
            instruction(
                1,
                vec![Assignment {
                    destination: Reg(2).into(),
                    value: load(r(0)),
                }],
                Control::Jump(2),
            ),
            instruction(2, vec![store(r(1), Width::U8, c(0xaa))], Control::Jump(3)),
            instruction(
                3,
                vec![Assignment {
                    destination: Reg(3).into(),
                    value: load(r(0)),
                }],
                Control::Jump(4),
            ),
            instruction(
                4,
                vec![],
                Control::Return(b(BinaryOp::Xor, b(BinaryOp::Shl, r(2), c(16)), r(3))),
            ),
        ],
    )
    .unwrap();
    let output = emit_readable_c_with_options(
        &program,
        ReadableOptions {
            stack_register: Some(Reg(0)),
            coalesce_locals: true,
            compact_memory: true,
            ..Default::default()
        },
    )
    .unwrap();
    let cells = output.stack_cells.as_ref().unwrap();
    assert!(
        output
            .locals
            .iter()
            .flat_map(|local| &local.registers)
            .any(|&reg| {
                cells.location(reg).is_some()
                    && output
                        .stack_roles
                        .as_ref()
                        .and_then(|roles| roles.register_web(reg))
                        .is_none()
            }),
        "late load has a location without a reaching-store web"
    );
    assert!(
        output.local_plan.source_allocation.is_none(),
        "live old and new values must remain distinct"
    );
    let inputs: Vec<_> = [0x1000, 0x1008, 0x100f, 0xffff]
        .into_iter()
        .flat_map(|stack| {
            [0x1000, 0x1008, 0x100f, 0xffff]
                .into_iter()
                .map(move |alias| [stack, alias])
        })
        .collect();
    compare_with_stack(&program, &inputs, Some(Reg(0)));
}

fn compare(program: &Program, inputs: &[[u64; 2]]) {
    compare_with_stack(program, inputs, None);
}

fn compare_with_stack(program: &Program, inputs: &[[u64; 2]], stack_register: Option<Reg>) {
    let scratch = Scratch::new();
    let mut text = String::new();
    let mut expected = Vec::new();
    for input in inputs {
        writeln!(text, "{} {}", input[0], input[1]).unwrap();
        let mut registers = vec![0; program.register_count()];
        registers[..2].copy_from_slice(input);
        let report = program
            .run_with_memory(&registers, 0x1000, &(1..=16).collect::<Vec<u8>>(), 1000)
            .unwrap();
        let (fault, address, access, width, value) = match report.status {
            RunStatus::Fault(f) => (
                1,
                f.address,
                if f.access == AccessKind::Read { 1 } else { 2 },
                f.width.bytes() as u64,
                0,
            ),
            RunStatus::Returned(value) => (0, 0, 0, 0, value),
            RunStatus::Suspended => panic!("test unexpectedly suspended"),
        };
        let words: Vec<_> = report
            .state
            .memory
            .chunks_exact(8)
            .map(|x| u64::from_le_bytes(x.try_into().unwrap()))
            .collect();
        expected.push(vec![
            fault, address, access, width, words[0], words[1], value,
        ]);
    }
    for (views, compact_memory) in [(false, false), (true, false), (false, true), (true, true)] {
        let output = emit_readable_c_with_options(
            program,
            ReadableOptions {
                stack_register,
                recover_objects: views,
                coalesce_locals: true,
                compact_memory,
            },
        )
        .unwrap();
        let mut args = output
            .parameters
            .iter()
            .map(|r| format!("r[{}]", r.0))
            .collect::<Vec<_>>();
        args.extend(["memory", "UINT64_C(4096)", "sizeof(memory)"].map(String::from));
        let args = args.join(", ");
        let code = checked_c::instrument(&output.code);
        let register_count = program.register_count();
        let harness = format!(
            r#"
#undef abort
#include <stdio.h>
#include <inttypes.h>
static jmp_buf jump;
static uint8_t memory[16];
static uint64_t result;
static unsigned fault;
_Noreturn void nirvana_test_abort(void) {{longjmp(jump,1);}}
int main(void) {{
    uint64_t a,b;
    while (scanf("%" SCNu64 " %" SCNu64,&a,&b)==2) {{
        for(unsigned i=0;i<16;++i) memory[i]=(uint8_t)(i+1);
        result=0;fault=0;nirvana_test_address=0;nirvana_test_access=0;nirvana_test_width=0;
        uint64_t r[{register_count}]={{a,b}};
        (void)r;
        if(setjmp(jump)==0) result=nirvana_readable({args});
        else fault=1;
        uint64_t words[2]={{0,0}};
        for(unsigned i=0;i<16;++i) words[i/8]|=(uint64_t)memory[i]<<((i%8)*8);
        printf("%u %" PRIu64 " %u %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
               fault,fault?nirvana_test_address:UINT64_C(0),fault?nirvana_test_access:0,
               fault?nirvana_test_width:UINT64_C(0),words[0],words[1],result);
    }}
}}
"#
        );
        for opt in ["-O0", "-O2"] {
            let source = scratch.0.join(format!("evaluation{views}{opt}.c"));
            std::fs::write(&source, code.clone() + &harness).unwrap();
            let compiled = source.with_extension("o");
            let binary = source.with_extension("bin");
            object(&source, &compiled, opt, "nirvana_readable");
            link(&[&compiled], &binary);
            assert_eq!(
                run_fields(&binary, &text, 7),
                expected,
                "views={views}, {opt}"
            );
        }
    }
}
