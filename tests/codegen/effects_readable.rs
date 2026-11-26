use crate::support::native;
use nirvana::effects::{
    CallInstruction, CallTarget, Instruction, Limits, Output, Program, PutsOutcome, Status, Suspend,
};
use nirvana::ir::{
    AccessKind, Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Reg, Width,
};
use std::fmt::Write as _;
const BASE: u64 = 4096;
const SIZE: usize = 128;
const PUTS: u64 = 0x9999;
const FIELDS: usize = 10 + 32 + SIZE / 8 + 128;
use crate::support::ir::c;
use crate::support::ir::r;
fn core(address: u64, assignments: Vec<Assignment>, control: Control) -> Instruction {
    Instruction::Core(IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    })
}
fn program(target: CallTarget, tail: bool) -> Program {
    let mut instructions = vec![
        core(
            0,
            vec![Assignment {
                destination: Place::Memory {
                    address: r(14),
                    width: Width::U8,
                },
                value: r(15),
            }],
            Control::Next,
        ),
        Instruction::Call(CallInstruction {
            address: 1,
            size: 1,
            target,
            tail,
        }),
    ];
    if !tail {
        instructions.push(core(
            2,
            vec![Assignment {
                destination: Reg(7).into(),
                value: Expr::binary(B::Add, r(12), c(1)),
            }],
            Control::Next,
        ));
        instructions.push(Instruction::Call(CallInstruction {
            address: 3,
            size: 1,
            target,
            tail: false,
        }));
        instructions.push(core(
            4,
            vec![Assignment {
                destination: Place::Memory {
                    address: c(BASE + 112),
                    width: Width::U64,
                },
                value: r(0),
            }],
            Control::Return(r(0)),
        ));
    }
    Program::new(0, 32, instructions, PUTS).unwrap()
}
#[derive(Clone, Copy)]
struct Case {
    arg: u64,
    sp: u64,
    target: u64,
    pattern: u64,
    mode: u64,
    limits: Limits,
    count: usize,
}
fn memory(pattern: u64, target: u64) -> Vec<u8> {
    let mut memory: Vec<_> = (0..SIZE)
        .map(|i| {
            if pattern == 2 {
                b'A'
            } else {
                (i * 29 + 7) as u8
            }
        })
        .collect();
    memory[..8].copy_from_slice(&target.to_le_bytes());
    if pattern != 2 {
        memory[16..20].copy_from_slice(b"abc\0");
    }
    if pattern == 1 {
        memory[16] = 0;
    }
    if pattern == 3 {
        memory[127] = 0;
    }
    memory
}
fn outcomes(mode: u64) -> Vec<PutsOutcome> {
    (0..2)
        .map(|i| {
            let mut outcome = PutsOutcome::success(0);
            for j in 0..14 {
                outcome.registers[j] = if j >= 9 {
                    (j as u64 + mode) & 1
                } else {
                    0x5151_0000_0000_0000
                        ^ ((j as u64 + 1) * 0x101)
                        ^ (mode << 12)
                        ^ ((i as u64) << 40)
                };
            }
            outcome.registers[0] = match mode {
                1 => 0x1234_5678_0000_0007,
                2 | 3 | 5 => u64::from(u32::MAX),
                _ => 0,
            };
            outcome.output = match mode {
                2 | 4 => Output::Prefix(0),
                3 => Output::Prefix(2),
                5 => Output::Prefix(usize::MAX),
                _ => Output::All,
            };
            if mode == 6 {
                outcome.registers[13] = 2;
            }
            outcome
        })
        .collect()
}
fn expected(program: &Program, case: Case) -> Vec<u64> {
    let mut registers: Vec<_> = (0..32)
        .map(|i| 0x1234_0000_0000_0000u64 ^ ((i + 1) * 0x101) as u64)
        .collect();
    registers[7] = case.arg;
    registers[4] = case.sp;
    registers[3] = case.target;
    registers[12] = case.arg;
    registers[14] = BASE + 120;
    registers[15] = 0x5a;
    let report = program
        .run(
            &registers,
            BASE,
            &memory(case.pattern, case.target),
            &outcomes(case.mode)[..case.count],
            case.limits,
        )
        .unwrap();
    let (status, value, fault, kind, width, unknown) = match report.status {
        Status::Returned(v) => (0, v, 0, 0, 0, 0),
        Status::Fault(f) => (
            1,
            0,
            f.address,
            if f.access == AccessKind::Read { 1 } else { 2 },
            f.width.bytes() as u64,
            0,
        ),
        Status::UnknownTarget(t) => (2, 0, 0, 0, 0, t),
        Status::EnvironmentExhausted => (3, 0, 0, 0, 0, 0),
        Status::InvalidOutcome => (4, 0, 0, 0, 0, 0),
        Status::Suspended(s) => (
            match s {
                Suspend::Instructions => 5,
                Suspend::Reads => 6,
                Suspend::Output => 7,
                Suspend::Calls => 8,
            },
            0,
            0,
            0,
            0,
            0,
        ),
    };
    let mut row = vec![
        status,
        value,
        fault,
        kind,
        width,
        unknown,
        report.consumed as u64,
        report.output.len() as u64,
        report.state.trace.len() as u64,
        report.state.instruction.unwrap_or(0),
    ];
    row.extend(report.state.registers);
    row.extend(
        report
            .state
            .memory
            .chunks_exact(8)
            .map(|w| u64::from_le_bytes(w.try_into().unwrap())),
    );
    for i in 0..128 {
        row.push(u64::from(report.output.get(i).copied().unwrap_or(0)));
    }
    assert_eq!(row.len(), FIELDS);
    row
}
fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    let limits = Limits {
        instructions: 100,
        external_reads: 256,
        output_bytes: 128,
        calls: 2,
    };
    for arg in [BASE - 1, BASE, BASE + 16, BASE + 17, BASE + 127, u64::MAX] {
        for sp in [BASE - 1, BASE, BASE + 8, BASE + 16, BASE + 128, u64::MAX] {
            for target in [PUTS, 0] {
                for pattern in 0..4 {
                    for mode in 0..7 {
                        cases.push(Case {
                            arg,
                            sp,
                            target,
                            pattern,
                            mode,
                            limits,
                            count: 2,
                        });
                    }
                }
            }
        }
    }
    for count in 0..=2 {
        for mode in 0..7 {
            let base = Case {
                arg: BASE + 16,
                sp: BASE + 128,
                target: PUTS,
                pattern: 0,
                mode,
                limits,
                count,
            };
            cases.push(base);
            for n in [0, 1, 2, 3, 4, 5, 7] {
                cases.push(Case {
                    limits: Limits {
                        instructions: n,
                        ..limits
                    },
                    ..base
                });
                cases.push(Case {
                    limits: Limits {
                        external_reads: n,
                        ..limits
                    },
                    ..base
                });
                cases.push(Case {
                    limits: Limits {
                        output_bytes: n,
                        ..limits
                    },
                    ..base
                });
                cases.push(Case {
                    limits: Limits { calls: n, ..limits },
                    ..base
                });
            }
        }
    }
    cases
}

const HARNESS: &str = r#"
#include <inttypes.h>
#include <stdio.h>
int main(void) {
    uint64_t arg,sp,target,pattern,mode,steps,reads,capacity,calls,count;
    while(scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,
        &arg,&sp,&target,&pattern,&mode,&steps,&reads,&capacity,&calls,&count)==10) {
        uint8_t memory[128],output[128]={0};uint64_t r[32];
        for(unsigned i=0;i<128;++i) memory[i]=pattern==2?'A':(uint8_t)(i*29+7);
        for(unsigned i=0;i<8;++i) memory[i]=(uint8_t)(target>>(i*8));
        if(pattern!=2){memory[16]='a';memory[17]='b';memory[18]='c';memory[19]=0;}
        if(pattern==1) {memory[16]=0;}
        if(pattern==3) {memory[127]=0;}
        for(unsigned i=0;i<32;++i)r[i]=UINT64_C(0x1234000000000000)^((i+1)*UINT64_C(0x101));
        r[7]=arg;r[4]=sp;r[3]=target;r[12]=arg;r[14]=4216;r[15]=0x5a;
        struct nirvana_puts_outcome tape[2]={0};
        for(unsigned i=0;i<2;++i) {
            for(unsigned j=0;j<14;++j)tape[i].registers[j]=j>=9?((j+mode)&1):UINT64_C(0x5151000000000000)^((j+1)*UINT64_C(0x101))^(mode<<12)^((uint64_t)i<<40);
            tape[i].registers[0]=mode==1?UINT64_C(0x1234567800000007):(mode==2||mode==3||mode==5)?UINT64_C(0xffffffff):0;
            tape[i].all=!(mode>=2&&mode<=5);tape[i].prefix=mode==3?2:mode==5?UINT64_MAX:0;
            if(mode==6)tape[i].registers[13]=2;
        }
        struct nirvana_effects e={0};e.outcomes=tape;e.outcome_count=count;e.output=output;e.output_capacity=capacity;
        e.instructions_left=steps;e.external_reads_left=reads;e.calls_left=calls;
        unsigned status=nirvana_effect_run(r,memory,4096,sizeof(memory),&e);
        printf("%u %" PRIu64 " %" PRIu64 " %u %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64,
            status,e.result,e.fault_address,e.fault_access,e.fault_width,e.unknown_target,e.consumed,e.output_size,e.started,e.instruction);
        for(unsigned i=0;i<32;++i)printf(" %" PRIu64,r[i]);
        for(unsigned i=0;i<16;++i){uint64_t v=0;for(unsigned j=0;j<8;++j)v|=(uint64_t)memory[i*8+j]<<(j*8);printf(" %" PRIu64,v);}
        for(unsigned i=0;i<128;++i)printf(" %u",i<e.output_size?output[i]:0);
        putchar('\n');
    }
}
"#;

#[test]
fn structured_effects_match_full_state_output_faults_and_every_stop_boundary() {
    let scratch = native::Scratch::new();
    let cases = cases();
    let mut input = String::new();
    for v in &cases {
        writeln!(
            input,
            "{} {} {} {} {} {} {} {} {} {}",
            v.arg,
            v.sp,
            v.target,
            v.pattern,
            v.mode,
            v.limits.instructions,
            v.limits.external_reads,
            v.limits.output_bytes,
            v.limits.calls,
            v.count
        )
        .unwrap();
    }
    let mut compared = 0;
    let mut completed = 0;
    for (id, (target, tail)) in [
        (CallTarget::Direct(PUTS), false),
        (CallTarget::Direct(PUTS), true),
        (CallTarget::Direct(0), false),
        (CallTarget::Register(Reg(4)), false),
        (CallTarget::Register(Reg(3)), false),
        (CallTarget::Memory(BASE), false),
        (CallTarget::Memory(BASE + 124), false),
        (CallTarget::Plt(BASE), false),
        (CallTarget::Plt(BASE + 124), false),
        (CallTarget::Plt(BASE), true),
    ]
    .into_iter()
    .enumerate()
    {
        let program = program(target, tail);
        let expected: Vec<_> = cases.iter().map(|&c| expected(&program, c)).collect();
        completed += expected.iter().filter(|row| row[0] <= 1).count() * 2;
        let source = scratch.0.join(format!("p{id}.c"));
        std::fs::write(
            &source,
            nirvana::effects_readable::emit_c(&program).unwrap().code + HARNESS,
        )
        .unwrap();
        for opt in ["-O0", "-O2"] {
            let object = scratch.0.join(format!("p{id}{opt}.o"));
            let bin = object.with_extension("bin");
            native::object(&source, &object, opt, "fixture");
            native::link(&[&object], &bin);
            let actual = native::run_fields(&bin, &input, FIELDS);
            assert_eq!(actual.len(), expected.len());
            for (i, (a, b)) in actual.iter().zip(&expected).enumerate() {
                assert_eq!(a, b, "program{id} {opt} case{i}");
            }
            compared += expected.len();
        }
    }
    println!(
        "{compared} effect C observations: {completed} completed return/fault observations; {} incomplete/invalid/unmodeled stop states. Full registers/RAM/output/status/consumption/pc/steps matched",
        compared - completed
    );
    assert!(compared > 20000);
}

#[test]
fn core_only_effect_program_omits_unreachable_labels_and_accepts_empty_output() {
    let program = Program::new(
        0,
        32,
        vec![
            core(0, vec![], Control::Return(c(7))),
            core(2, vec![], Control::Return(c(8))),
        ],
        PUTS,
    )
    .unwrap();
    let code = nirvana::effects_readable::emit_c(&program).unwrap().code;
    assert!(!code.contains("nirvana_pc_2:"));
    let scratch = native::Scratch::new();
    let source = scratch.0.join("empty.c");
    std::fs::write(&source,code+"\nint main(void){uint64_t r[32]={0};uint8_t m[1]={0};struct nirvana_effects e={0};e.instructions_left=1;return nirvana_effect_run(r,m,0,1,&e)==0&&e.result==7?0:1;}\n").unwrap();
    let object = source.with_extension("o");
    let bin = source.with_extension("bin");
    native::object(&source, &object, "-O2", "fixture");
    native::link(&[&object], &bin);
    assert!(std::process::Command::new(bin).status().unwrap().success());
}

fn compare(program: &Program, cases: &[Case], name: &str) -> usize {
    let output = nirvana::effects_readable::emit_c(program).unwrap();
    let scratch = native::Scratch::new();
    let source = scratch.0.join(format!("{name}.c"));
    std::fs::write(&source, output.code + HARNESS).unwrap();
    let mut input = String::new();
    for v in cases {
        writeln!(
            input,
            "{} {} {} {} {} {} {} {} {} {}",
            v.arg,
            v.sp,
            v.target,
            v.pattern,
            v.mode,
            v.limits.instructions,
            v.limits.external_reads,
            v.limits.output_bytes,
            v.limits.calls,
            v.count
        )
        .unwrap();
    }
    let expected: Vec<_> = cases.iter().map(|&case| expected(program, case)).collect();
    for opt in ["-O0", "-O2"] {
        let object = source.with_extension(format!("{opt}.o"));
        let bin = object.with_extension("bin");
        native::object(&source, &object, opt, "fixture");
        native::link(&[&object], &bin);
        let actual = native::run_fields(&bin, &input, FIELDS);
        assert_eq!(actual.len(), expected.len());
        for (i, (a, b)) in actual.iter().zip(&expected).enumerate() {
            assert_eq!(a, b, "{name} {opt} case{i}");
        }
    }
    2 * cases.len()
}

fn load(address: Expr) -> Expr {
    Expr::Load {
        address: Box::new(address),
        width: Width::U8,
    }
}

fn branch_loop(target: CallTarget) -> Program {
    Program::new(
        0,
        32,
        vec![
            core(
                0,
                vec![
                    Assignment {
                        destination: Place::Memory {
                            address: r(14),
                            width: Width::U8,
                        },
                        value: r(15),
                    },
                    Assignment {
                        destination: Reg(13).into(),
                        value: c(0),
                    },
                ],
                Control::Next,
            ),
            core(
                1,
                vec![],
                Control::Branch {
                    condition: Expr::binary(B::Eq, r(3), c(PUTS)),
                    target: 4,
                },
            ),
            core(
                2,
                vec![Assignment {
                    destination: Reg(6).into(),
                    value: Expr::Select {
                        condition: Box::new(Expr::binary(B::Eq, r(7), c(BASE + 16))),
                        taken: Box::new(c(5)),
                        not_taken: Box::new(Expr::binary(B::Add, load(r(7)), load(r(14)))),
                    },
                }],
                Control::Next,
            ),
            // An empty step is observable at instruction-budget boundaries.
            core(3, vec![], Control::Jump(4)),
            Instruction::Call(CallInstruction {
                address: 4,
                size: 1,
                target,
                tail: false,
            }),
            core(
                5,
                vec![Assignment {
                    destination: Reg(7).into(),
                    value: Expr::binary(B::Add, r(12), c(1)),
                }],
                // The condition is clobbered by the call's outcome tape.
                Control::Branch {
                    condition: r(16),
                    target: 7,
                },
            ),
            core(
                6,
                vec![Assignment {
                    destination: Reg(13).into(),
                    value: Expr::binary(B::Add, r(13), c(1)),
                }],
                Control::Branch {
                    condition: Expr::binary(B::Ult, r(13), c(2)),
                    target: 4,
                },
            ),
            core(
                7,
                vec![],
                Control::Return(Expr::Select {
                    condition: Box::new(r(0)),
                    taken: Box::new(load(r(7))),
                    not_taken: Box::new(c(0)),
                }),
            ),
        ],
        PUTS,
    )
    .unwrap()
}

#[test]
fn real_branches_loops_keep_call_clobbers_lazy_reads_and_all_steps() {
    let mut cases = cases();
    for mode in 0..7 {
        for instructions in 0..=15 {
            cases.push(Case {
                arg: BASE + 16,
                sp: BASE + SIZE as u64,
                target: PUTS,
                pattern: 0,
                mode,
                limits: Limits {
                    instructions,
                    external_reads: 256,
                    output_bytes: 128,
                    calls: 2,
                },
                count: 2,
            });
        }
    }
    let mut compared = 0;
    for (id, target) in [
        CallTarget::Direct(PUTS),
        CallTarget::Register(Reg(3)),
        CallTarget::Memory(BASE),
        CallTarget::Plt(BASE),
    ]
    .into_iter()
    .enumerate()
    {
        let program = branch_loop(target);
        let output = nirvana::effects_readable::emit_c(&program).unwrap();
        assert!(output.fallback_reason.is_none());
        let body = output
            .code
            .split("unsigned nirvana_effect_run")
            .nth(1)
            .unwrap();
        assert!(body.contains("while (1) {"));
        assert!(body.contains("if (r[16]) {"));
        assert!(body.contains("nirvana_call_puts(&m, r,"));
        assert!(!body.contains("nirvana_pc_"));
        for address in 0..=7 {
            assert!(body.contains(&format!("nirvana_step(&m, UINT64_C({address}))")));
        }
        compared += compare(&program, &cases, &format!("loop{id}"));
    }
    println!("{compared} branch/loop C observations matched full state and stops");
}

#[test]
fn ordered_stores_and_degenerate_branches_retain_the_first_fault() {
    let cases = cases();
    let store = Program::new(
        0,
        32,
        vec![core(
            0,
            vec![Assignment {
                destination: Place::Memory {
                    address: r(7),
                    width: Width::U64,
                },
                value: Expr::binary(B::Add, load(r(7)), load(c(0))),
            }],
            Control::Return(c(0)),
        )],
        PUTS,
    )
    .unwrap();
    compare(&store, &cases, "store-order");
    let degenerate = Program::new(
        0,
        32,
        vec![
            core(
                0,
                vec![],
                Control::Branch {
                    condition: Expr::binary(B::Add, load(r(7)), load(c(0))),
                    target: 1,
                },
            ),
            core(1, vec![], Control::Return(c(0))),
        ],
        PUTS,
    )
    .unwrap();
    compare(&degenerate, &cases, "degenerate-branch");
}

#[test]
fn nested_outer_transfers_preserve_instruction_budget_and_registers() {
    let set = |register, value| Assignment {
        destination: Reg(register).into(),
        value,
    };
    let add = |register, value| set(register, Expr::binary(B::Add, r(register), c(value)));
    let branch = |condition, target| Control::Branch { condition, target };
    let program = Program::new(
        0,
        32,
        vec![
            core(0, vec![set(13, c(0)), set(14, c(0))], Control::Next),
            core(1, vec![], branch(Expr::binary(B::Ult, r(13), c(3)), 3)),
            core(2, vec![], Control::Return(r(14))),
            core(3, vec![set(5, c(0))], Control::Next),
            core(4, vec![], branch(Expr::binary(B::Ult, r(5), c(2)), 6)),
            core(5, vec![add(13, 1), add(14, 100)], Control::Jump(1)),
            core(
                6,
                vec![add(5, 1), add(14, 1)],
                branch(Expr::binary(B::And, r(3), c(1)), 9),
            ),
            core(7, vec![], branch(Expr::binary(B::And, r(3), c(2)), 10)),
            core(8, vec![], Control::Jump(4)),
            core(9, vec![add(13, 1), add(14, 1000)], Control::Jump(1)),
            core(10, vec![add(14, 10000)], Control::Jump(2)),
        ],
        PUTS,
    )
    .unwrap();
    let output = nirvana::effects_readable::emit_c(&program).unwrap();
    assert!(output.fallback_reason.is_none());
    assert!(output.code.contains("goto nirvana_loop_"));
    assert!(output.code.contains("_continue: ;"));
    assert!(output.code.contains("_break: ;"));
    let base = cases()[0];
    let mut inputs = Vec::new();
    for target in 0..4 {
        for instructions in 0..=100 {
            inputs.push(Case {
                target,
                limits: Limits {
                    instructions,
                    ..base.limits
                },
                ..base
            });
        }
    }
    assert_eq!(compare(&program, &inputs, "nonlocal"), 808);
}

#[test]
fn returning_and_divergent_arms_use_the_structured_checked_renderer() {
    let program = Program::new(
        0,
        32,
        vec![
            core(
                0,
                vec![],
                Control::Branch {
                    condition: r(3),
                    target: 2,
                },
            ),
            core(1, vec![], Control::Return(c(1))),
            core(2, vec![], Control::Jump(2)),
        ],
        PUTS,
    )
    .unwrap();
    let output = nirvana::effects_readable::emit_c(&program).unwrap();
    assert!(output.fallback_reason.is_none());
    let inputs = branch_budget_cases();
    assert_eq!(compare(&program, &inputs, "divergent"), 52);
}

fn branch_budget_cases() -> Vec<Case> {
    let base = cases()[0];
    [0, 1]
        .into_iter()
        .flat_map(|target| {
            (0..=12).map(move |instructions| Case {
                target,
                limits: Limits {
                    instructions,
                    ..base.limits
                },
                ..base
            })
        })
        .collect()
}

#[test]
fn split_nested_loop_exits_use_the_structured_checked_renderer() {
    let branch = |target| Control::Branch {
        condition: r(3),
        target,
    };
    let program = Program::new(
        0,
        32,
        vec![
            core(0, vec![], branch(2)),
            core(1, vec![], branch(3)),
            core(2, vec![], branch(1)),
            core(3, vec![], Control::Jump(0)),
            core(4, vec![], Control::Return(c(1))),
        ],
        PUTS,
    )
    .unwrap();
    let output = nirvana::effects_readable::emit_c(&program).unwrap();
    assert!(output.fallback_reason.is_none());
    let inputs = branch_budget_cases();
    assert_eq!(compare(&program, &inputs, "split-loop-exits"), 52);
}

#[test]
fn unavailable_structure_falls_back_atomically_to_the_checked_renderer() {
    // Independent multiple-entry cycles need two separate entry redirects;
    // the bounded one-proposal split search retains the checked fallback.
    let branch = |target| Control::Branch {
        condition: r(3),
        target,
    };
    let program = Program::new(
        0,
        32,
        vec![
            core(0, vec![], branch(2)),
            core(1, vec![], Control::Jump(2)),
            core(2, vec![], branch(1)),
            core(3, vec![], branch(5)),
            core(4, vec![], Control::Jump(5)),
            core(5, vec![], branch(4)),
            core(6, vec![], Control::Return(c(1))),
        ],
        PUTS,
    )
    .unwrap();
    let output = nirvana::effects_readable::emit_c(&program).unwrap();
    assert!(matches!(
        output.fallback_reason,
        Some(nirvana::structure::StructureError::Irreducible)
    ));
    assert_eq!(
        output.code,
        nirvana::effects_emit::emit_c(&program).unwrap()
    );
    let inputs = branch_budget_cases();
    assert_eq!(compare(&program, &inputs, "fallback"), 52);
}

#[test]
fn initial_string_views_are_bounded_escaped_and_leave_mutable_ram_authoritative() {
    let program = Program::new(
        0,
        32,
        vec![
            core(
                0,
                vec![Assignment {
                    destination: Reg(7).into(),
                    // RIP-relative address with a negative displacement.
                    value: Expr::binary(B::Add, c(BASE + 128), c(u64::MAX - 111)),
                }],
                Control::Next,
            ),
            Instruction::Call(CallInstruction {
                address: 1,
                size: 1,
                target: CallTarget::Direct(PUTS),
                tail: true,
            }),
        ],
        PUTS,
    )
    .unwrap();
    let text = b"hello */??/\n\"\\tail\0";
    let mut memory = vec![0; SIZE];
    memory[16..16 + text.len()].copy_from_slice(text);
    let image = nirvana::loader::LinkedImage {
        memory_layout: None,
        memory_base: BASE,
        memory,
        function: nirvana::elf::FunctionImage {
            name: "fixture".into(),
            address: 0,
            bytes: vec![],
            relocations: vec![],
        },
        sections: vec![],
        puts_address: PUTS,
        stack_pointer: BASE + 120,
        external_data: Vec::new(),
        thread_local: None,
    };
    let output = nirvana::effects_readable::emit_image(&program, &image).unwrap();
    assert!(output.fallback_reason.is_none());
    assert!(
        output
            .code
            .contains("0x1010: \"hello \\052\\057\\077\\077\\057\\n\\\"\\\\tail\"")
    );
    assert_eq!(output.code.matches("Initial guest string views").count(), 1);
    let scratch = native::Scratch::new();
    let source = scratch.0.join("initial-strings.c");
    let harness = format!(
        r#"
int main(void) {{
    uint64_t r[NIRVANA_EFFECT_REGISTERS];
    uint8_t memory[NIRVANA_EFFECT_MEMORY_SIZE],output[128]={{0}};
    nirvana_effect_init(r,memory);
    memory[16]='X';
    struct nirvana_puts_outcome tape={{0}};
    tape.all=1;tape.registers[0]=7;
    struct nirvana_effects e={{0}};
    e.outcomes=&tape;e.outcome_count=1;e.output=output;e.output_capacity=sizeof(output);
    e.instructions_left=2;e.external_reads_left=128;e.calls_left=1;
    unsigned status=nirvana_effect_run(r,memory,NIRVANA_EFFECT_MEMORY_BASE,sizeof(memory),&e);
    return !(status==0 && e.result==7 && e.started==2 && e.consumed==1 &&
             e.output_size=={} && output[0]=='X' && output[e.output_size-1]=='\n');
}}
"#,
        text.len(),
    );
    std::fs::write(&source, output.code + &harness).unwrap();
    for opt in ["-O0", "-O2"] {
        let object = source.with_extension(format!("{opt}.o"));
        let bin = object.with_extension("bin");
        native::object(&source, &object, opt, "fixture");
        native::link(&[&object], &bin);
        assert!(std::process::Command::new(bin).status().unwrap().success());
    }

    let mut many = Vec::new();
    let mut image = image;
    image.memory = vec![0; 4096];
    for index in 0..40 {
        image.memory[index * 4..index * 4 + 3].copy_from_slice(b"abc");
        many.push(core(
            index as u64,
            vec![Assignment {
                destination: Reg(7).into(),
                value: c(BASE + index as u64 * 4),
            }],
            if index == 39 {
                Control::Return(c(0))
            } else {
                Control::Next
            },
        ));
    }
    let program = Program::new(0, 32, many, PUTS).unwrap();
    let output = nirvana::effects_readable::emit_image(&program, &image).unwrap();
    let preview = output.code.split("*/").next().unwrap();
    assert_eq!(preview.matches(": \"abc\"").count(), 16);
}
