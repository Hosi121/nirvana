#[path = "support/checked_c.rs"]
#[allow(dead_code)]
mod checked_c;
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use nirvana::ir::{
    Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, RunReport, RunStatus,
    Width,
};
use nirvana::{ssa, ssa_destroy, ssa_locals};
use std::collections::BTreeSet;
use std::process::Command;

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn op(op: BinaryOp, a: Expr, b: Expr) -> Expr {
    Expr::binary(op, a, b)
}
fn a(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}
fn i(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn programs() -> Vec<Program> {
    vec![
        Program::new(
            0,
            5,
            vec![
                i(
                    0,
                    vec![],
                    Control::Branch {
                        condition: r(3),
                        target: 2,
                    },
                ),
                i(1, vec![], Control::Return(op(BinaryOp::Xor, r(0), r(1)))),
                i(
                    2,
                    vec![
                        a(2, r(0)),
                        a(0, r(1)),
                        a(1, r(2)),
                        a(3, op(BinaryOp::Sub, r(3), c(1))),
                    ],
                    Control::Jump(0),
                ),
            ],
        )
        .unwrap(),
        Program::new(
            0,
            5,
            vec![
                i(
                    0,
                    vec![],
                    Control::Branch {
                        condition: r(2),
                        target: 3,
                    },
                ),
                i(
                    1,
                    vec![a(0, op(BinaryOp::Add, r(0), c(1)))],
                    Control::Branch {
                        condition: r(3),
                        target: 4,
                    },
                ),
                i(
                    2,
                    vec![a(0, op(BinaryOp::Add, r(1), c(2)))],
                    Control::Jump(3),
                ),
                i(
                    3,
                    vec![a(0, op(BinaryOp::Add, r(0), r(1)))],
                    Control::Jump(4),
                ),
                i(4, vec![], Control::Return(op(BinaryOp::Add, r(0), r(1)))),
            ],
        )
        .unwrap(),
        Program::new(
            0,
            5,
            vec![
                i(
                    0,
                    vec![
                        a(0, Expr::load(r(3), Width::U8)),
                        Assignment {
                            destination: Place::Memory {
                                address: r(4),
                                width: Width::U64,
                            },
                            value: Expr::select(r(2), Expr::load(r(4), Width::U64), c(9)),
                        },
                        a(1, op(BinaryOp::Add, r(0), r(1))),
                    ],
                    Control::Branch {
                        condition: Expr::load(r(3), Width::U8),
                        target: 2,
                    },
                ),
                i(1, vec![], Control::Return(r(1))),
                i(
                    2,
                    vec![a(2, Expr::load(r(4), Width::U64))],
                    Control::Return(r(2)),
                ),
            ],
        )
        .unwrap(),
        Program::new(
            0,
            5,
            vec![
                i(
                    0,
                    vec![a(0, op(BinaryOp::Add, r(1), c(1)))],
                    Control::Branch {
                        condition: Expr::load(r(3), Width::U64),
                        target: 2,
                    },
                ),
                i(1, vec![], Control::Return(r(0))),
                i(2, vec![], Control::Return(r(1))),
            ],
        )
        .unwrap(),
        Program::new(
            0,
            5,
            vec![
                i(
                    0,
                    vec![],
                    Control::Branch {
                        condition: r(2),
                        target: 1,
                    },
                ),
                i(1, vec![a(0, r(1))], Control::Return(r(0))),
            ],
        )
        .unwrap(),
        Program::new(
            0,
            5,
            vec![i(
                0,
                vec![a(0, op(BinaryOp::Add, r(0), c(1))), a(1, c(9))],
                Control::Return(r(0)),
            )],
        )
        .unwrap(),
        Program::new(
            0,
            5,
            vec![
                i(
                    0,
                    vec![],
                    Control::Branch {
                        condition: r(2),
                        target: 2,
                    },
                ),
                i(
                    1,
                    vec![a(0, op(BinaryOp::Add, r(0), c(1)))],
                    Control::Jump(3),
                ),
                i(2, vec![a(0, op(BinaryOp::Xor, r(0), r(1)))], Control::Next),
                i(
                    3,
                    vec![a(3, op(BinaryOp::Sub, r(3), c(1)))],
                    Control::Branch {
                        condition: r(3),
                        target: 1,
                    },
                ),
                i(4, vec![], Control::Return(r(0))),
            ],
        )
        .unwrap(),
    ]
}

fn cases(index: usize) -> Vec<Vec<u64>> {
    if index == 2 || index == 3 {
        let mut rows = Vec::new();
        for p in [0, 4095, 4096, 4104, 4111, u64::MAX] {
            for q in [0, 4096, 4104, 4112, u64::MAX] {
                for condition in [0, 1] {
                    rows.push(vec![u64::MAX, 7, condition, p, q]);
                }
            }
        }
        rows
    } else {
        let mut rows = Vec::new();
        for x in [0, 1, u64::MAX, 0x8000_0000_0000_0001] {
            for y in [0, 7, u64::MAX] {
                for condition in [0, 1] {
                    for count in [0, 1, 3, 7] {
                        rows.push(vec![x, y, condition, count, 4096]);
                    }
                }
            }
        }
        rows
    }
}

#[test]
fn original_and_lowered_ir_match_full_state_at_every_budget_and_first_fault() {
    let memory: Vec<_> = (0..16).map(|x| (x * 17 + 3) as u8).collect();
    let mut comparisons = 0;
    let mut temporary_edges = 0;
    for (index, source) in programs().iter().enumerate() {
        let graph = ssa::SsaFunction::build(source).unwrap();
        let grouped = ssa_destroy::lower(source, &graph, &BTreeSet::new()).unwrap();
        temporary_edges += grouped.stats().temporary_edges;
        let identity = ssa_destroy::lower_with_plan(
            source,
            &graph,
            ssa_locals::Plan {
                by_value: (0..graph.values.len()).collect(),
                local_count: graph.values.len(),
            },
        )
        .unwrap();
        assert!(grouped.plan().local_count <= identity.plan().local_count);
        assert_eq!(
            grouped
                .program()
                .instructions()
                .iter()
                .map(|i| (i.address, i.size))
                .collect::<Vec<_>>(),
            source
                .instructions()
                .iter()
                .map(|i| (i.address, i.size))
                .collect::<Vec<_>>()
        );
        for input in cases(index) {
            for budget in 0..=48 {
                let original = source
                    .run_with_memory(&input, 4096, &memory, budget)
                    .unwrap();
                for lowered in [&grouped, &identity] {
                    assert_eq!(
                        lowered
                            .run_with_memory(&input, 4096, &memory, budget)
                            .unwrap(),
                        original,
                        "program {index}, input {input:?}, budget {budget}"
                    );
                    comparisons += 1;
                }
            }
        }
    }
    assert!(
        temporary_edges > 0,
        "swap loop must exercise temporary edge copies"
    );
    println!("{comparisons} full-state IR comparisons including {temporary_edges} cycle edges");
}

fn fields(report: &RunReport) -> Vec<u64> {
    let mut result = match report.status {
        RunStatus::Returned(value) => vec![0, 0, 0, 0, value],
        RunStatus::Fault(fault) => vec![
            1,
            fault.address,
            if fault.access == nirvana::ir::AccessKind::Read {
                1
            } else {
                2
            },
            fault.width.bytes() as u64,
            0,
        ],
        RunStatus::Suspended => panic!("C cohort requires terminating inputs"),
    };
    result.extend(&report.state.registers);
    result.extend(report.state.memory.iter().map(|&b| u64::from(b)));
    result
}

#[test]
fn zero_locals_and_unreachable_instructions_keep_the_source_interface() {
    let source = Program::new(
        9,
        0,
        vec![
            i(9, vec![], Control::Return(c(17))),
            i(12, vec![], Control::Return(c(99))),
        ],
    )
    .unwrap();
    let graph = ssa::SsaFunction::build(&source).unwrap();
    let lowered = ssa_destroy::lower(&source, &graph, &BTreeSet::new()).unwrap();
    assert_eq!(lowered.plan().local_count, 0);
    for steps in [0, 1, 2] {
        assert_eq!(
            lowered.run_with_memory(&[], 0, &[], steps).unwrap(),
            source.run_with_memory(&[], 0, &[], steps).unwrap()
        );
    }
    assert!(matches!(
        lowered.initial_state(&[1]),
        Err(nirvana::ir::ExecutionError::RegisterCount {
            expected: 0,
            actual: 1
        })
    ));
    assert!(lowered.emit_c().unwrap().code.contains("nirvana_fn"));
}

#[test]
fn named_local_c_preserves_registers_ram_and_ordered_faults_at_o0_and_o2() {
    let scratch = native::Scratch::new();
    let memory: Vec<_> = (0..16).map(|x| (x * 17 + 3) as u8).collect();
    let mut comparisons = 0;
    for (index, source) in programs().iter().enumerate() {
        let graph = ssa::SsaFunction::build(source).unwrap();
        let lowered = ssa_destroy::lower(source, &graph, &BTreeSet::new()).unwrap();
        let output = lowered.emit_c().unwrap();
        assert!(output.code.contains("uint64_t v_"));
        let body = if source.uses_memory() {
            checked_c::instrument(&output.code)
        } else {
            format!(
                "static unsigned nirvana_test_access;\nstatic unsigned long long nirvana_test_address,nirvana_test_width;\n{}",
                output.code
            )
        };
        let call = if source.uses_memory() {
            "nirvana_fn(registers,memory,UINT64_C(4096),sizeof(memory))"
        } else {
            "nirvana_fn(registers)"
        };
        let harness = format!(
            r#"
#undef abort
#include <stdio.h>
#include <inttypes.h>
#include <setjmp.h>
static jmp_buf jump;
static uint64_t registers[5],result;
static uint8_t memory[16];
static unsigned fault;
_Noreturn void nirvana_test_abort(void) {{ longjmp(jump,1); }}
int main(void) {{
    while(scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,&registers[0],&registers[1],&registers[2],&registers[3],&registers[4])==5) {{
        for(unsigned i=0;i<16;++i)memory[i]=(uint8_t)(i*17+3);
        result=0;nirvana_test_address=0;nirvana_test_access=0;nirvana_test_width=0;
        fault=0;
        if(setjmp(jump)==0)result={call};else fault=1;
        printf("%u %" PRIu64 " %u %" PRIu64 " %" PRIu64,fault,(uint64_t)(fault?nirvana_test_address:0),fault?nirvana_test_access:0,(uint64_t)(fault?nirvana_test_width:0),result);
        for(unsigned i=0;i<5;++i)printf(" %" PRIu64,registers[i]);
        for(unsigned i=0;i<16;++i)printf(" %u",(unsigned)memory[i]);
        putchar('\n');
    }}
}}
"#
        );
        let cfile = scratch.0.join(format!("program-{index}.c"));
        std::fs::write(&cfile, body + &harness).unwrap();
        let inputs: Vec<_> = cases(index)
            .into_iter()
            .filter(|v| index != 6 || v[3] != 0)
            .collect();
        let text = inputs
            .iter()
            .map(|v| v.iter().map(u64::to_string).collect::<Vec<_>>().join(" ") + "\n")
            .collect::<String>();
        let expected: Vec<_> = inputs
            .iter()
            .map(|v| fields(&source.run_with_memory(v, 4096, &memory, 200).unwrap()))
            .collect();
        for opt in ["-O0", "-O2"] {
            let binary = scratch.0.join(format!("program-{index}{opt}"));
            let compiled = Command::new("cc")
                .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic", opt])
                .arg(&cfile)
                .arg("-o")
                .arg(&binary)
                .output()
                .unwrap();
            assert!(
                compiled.status.success(),
                "program{index} {opt}: {}",
                String::from_utf8_lossy(&compiled.stderr)
            );
            let actual = native::run_fields(&binary, &text, 26);
            assert_eq!(actual, expected, "program{index} {opt}");
            comparisons += actual.len();
        }
    }
    println!("{comparisons} compiled C full-register/RAM/fault comparisons");
}
