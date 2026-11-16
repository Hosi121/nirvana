#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use native::{Scratch, link, object, run};
use nirvana::ir::{
    Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus, Width,
};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use std::fmt::Write as _;

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
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
    assert_eq!(separate.locals.len(), 3);
    assert_eq!(coalesced.locals.len(), 1);
    assert_eq!(coalesced.locals[0].registers.len(), 3);
    compare(&p, &[[0x1000, 0], [0x1008, 0], [0xffff, 0]]);
}

#[test]
fn native_c_goto_fallback_sequences_dispatch_faults_before_entering_a_cycle() {
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
    assert!(
        emit_readable_c_with_options(&p, ReadableOptions::default())
            .unwrap()
            .fallback_reason
            .is_some()
    );
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
    assert!(output.code.contains("while (("), "{}", output.code);
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

fn compare(program: &Program, inputs: &[[u64; 2]]) {
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
        let (fault, address, value) = match report.status {
            RunStatus::Fault(f) => (1, f.address, 0),
            RunStatus::Returned(value) => (0, 0, value),
            RunStatus::Suspended => panic!("test unexpectedly suspended"),
        };
        let words: Vec<_> = report
            .state
            .memory
            .chunks_exact(8)
            .map(|x| u64::from_le_bytes(x.try_into().unwrap()))
            .collect();
        expected.push(vec![fault, address, words[0], words[1], value]);
    }
    for (views, compact_memory) in [(false, false), (true, false), (false, true), (true, true)] {
        let output = emit_readable_c_with_options(
            program,
            ReadableOptions {
                stack_register: None,
                recover_objects: views,
                coalesce_locals: true,
                compact_memory,
            },
        )
        .unwrap();
        let args = output
            .parameters
            .iter()
            .map(|r| format!("r[{}]", r.0))
            .collect::<Vec<_>>()
            .join(", ");
        let code=output.code.replace(
            "static inline uint64_t nirvana_offset(struct nirvana_memory *m, uint64_t address, uint64_t width) {",
            "static inline uint64_t nirvana_offset(struct nirvana_memory *m, uint64_t address, uint64_t width) { nirvana_test_address=address;"
        );
        let prefix = "#include <stdint.h>\n#include <setjmp.h>\nstatic uint64_t nirvana_test_address;\n_Noreturn void nirvana_test_abort(void);\n#define abort nirvana_test_abort\n";
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
        result=0;fault=0;
        uint64_t r[{register_count}]={{a,b}};
        if(setjmp(jump)==0) result=nirvana_readable({args},memory,UINT64_C(4096),sizeof(memory));
        else fault=1;
        uint64_t words[2]={{0,0}};
        for(unsigned i=0;i<16;++i) words[i/8]|=(uint64_t)memory[i]<<((i%8)*8);
        printf("%u %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",fault,fault?nirvana_test_address:UINT64_C(0),words[0],words[1],result);
    }}
}}
"#
        );
        for opt in ["-O0", "-O2"] {
            let source = scratch.0.join(format!("evaluation{views}{opt}.c"));
            std::fs::write(&source, prefix.to_owned() + &code + &harness).unwrap();
            let compiled = source.with_extension("o");
            let binary = source.with_extension("bin");
            object(&source, &compiled, opt, "nirvana_readable");
            link(&[&compiled], &binary);
            assert_eq!(run(&binary, &text), expected, "views={views}, {opt}");
        }
    }
}
