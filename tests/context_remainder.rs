use nirvana::{context_remainder, ir};
#[path = "support/checked_c.rs"]
#[allow(dead_code)]
mod checked_c;
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use context_remainder::{ContextRemainders, validate};
use ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus, Width,
};
use std::fmt::Write as _;
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn r(i: usize) -> Expr {
    Expr::Register(Reg(i))
}
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(i: usize, x: Expr) -> Assignment {
    Assignment {
        destination: Reg(i).into(),
        value: x,
    }
}
fn store(a: Expr, x: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: a,
            width: Width::U64,
        },
        value: x,
    }
}
fn quotient(x: Expr) -> Expr {
    b(B::Shr, b(B::UMulHigh, x, c(0xcccccccccccccccd)), c(3))
}
fn remainder(x: Expr) -> Expr {
    b(B::Sub, x, b(B::Mul, r(1), c(10)))
}
fn ins(pc: u64, a: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address: pc,
        size: 1,
        assignments: a,
        control,
    }
}
fn single(a: Vec<Assignment>) -> Program {
    Program::new(0, 8, vec![ins(0, a, Control::Return(r(2)))]).unwrap()
}
fn sample() -> Program {
    single(vec![
        set(1, quotient(r(0))),
        store(r(3), r(1)),
        set(2, remainder(r(0))),
    ])
}
#[test]
fn sequential_same_instruction_points_prove_use_before_destination_write() {
    let p = sample();
    let plan = ContextRemainders::analyze(&p).unwrap();
    assert_eq!(plan.evidence().len(), 1);
    let proof = plan.evidence()[0];
    assert_eq!(
        (proof.definition_instruction, proof.definition_assignment),
        (0, 0)
    );
    assert_eq!((proof.keeper.instruction, proof.keeper.assignment), (0, 1));
    assert!(validate(&p, &proof));
    let view = plan
        .view(&p, 0, 2, &p.instructions()[0].assignments[2].value)
        .unwrap();
    assert_eq!(view.divisor, 10);
    assert_eq!(view.quotient, Reg(1));
    assert_eq!(view.maximum_remainder, 9);
    assert!(std::ptr::eq(
        view.value,
        match &p.instructions()[0].assignments[2].value {
            Expr::Binary(_, x, _) => &**x,
            _ => panic!(),
        }
    ));
}
#[test]
fn q_or_dividend_dependency_writes_kill_the_fact_in_assignment_order() {
    for write in [set(1, c(7)), set(0, c(7)), set(0, r(0))] {
        let p = single(vec![
            set(1, quotient(r(0))),
            store(r(3), r(1)),
            write,
            set(2, remainder(r(0))),
        ]);
        assert!(
            ContextRemainders::analyze(&p)
                .unwrap()
                .evidence()
                .is_empty()
        );
    }
    let x = b(B::Add, r(0), r(4));
    let p = single(vec![
        set(1, quotient(x.clone())),
        store(r(3), r(1)),
        set(4, c(99)),
        set(2, remainder(x)),
    ]);
    assert!(
        ContextRemainders::analyze(&p)
            .unwrap()
            .evidence()
            .is_empty()
    );
    let p = single(vec![
        set(1, quotient(r(1))),
        store(r(3), r(1)),
        set(2, remainder(r(1))),
    ]);
    assert!(
        ContextRemainders::analyze(&p)
            .unwrap()
            .evidence()
            .is_empty()
    );
}
#[test]
fn arbitrary_stores_do_not_invalidate_captured_register_dividends() {
    let p = single(vec![
        set(0, Expr::load(r(4), Width::U64)),
        set(1, quotient(r(0))),
        store(r(3), r(1)),
        store(r(4), c(77)),
        set(2, remainder(r(0))),
    ]);
    assert_eq!(ContextRemainders::analyze(&p).unwrap().evidence().len(), 1);
}
#[test]
fn keeper_must_be_a_same_generation_prefix_store_of_the_bare_quotient() {
    for a in [
        vec![
            set(1, quotient(r(0))),
            set(5, b(B::Add, r(1), c(1))),
            set(2, remainder(r(0))),
        ],
        vec![
            set(1, quotient(r(0))),
            store(r(1), c(0)),
            set(2, remainder(r(0))),
        ],
        vec![
            store(r(3), r(1)),
            set(1, quotient(r(0))),
            set(2, remainder(r(0))),
        ],
        vec![
            set(1, quotient(r(0))),
            store(r(3), r(1)),
            set(1, quotient(r(0))),
            set(2, remainder(r(0))),
        ],
        vec![
            set(1, quotient(r(0))),
            set(2, remainder(r(0))),
            set(5, remainder(r(0))),
        ],
        vec![
            set(1, quotient(r(0))),
            set(2, remainder(r(0))),
            store(r(3), r(1)),
        ],
    ] {
        assert!(
            ContextRemainders::analyze(&single(a))
                .unwrap()
                .evidence()
                .is_empty()
        );
    }
}
#[test]
fn fresh_block_facts_do_not_cross_jumps_joins_or_loop_backedges() {
    let p = Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![set(1, quotient(r(0))), store(r(3), r(1))],
                Control::Jump(1),
            ),
            ins(1, vec![set(2, remainder(r(0)))], Control::Return(r(2))),
        ],
    )
    .unwrap();
    assert!(
        ContextRemainders::analyze(&p)
            .unwrap()
            .evidence()
            .is_empty()
    );
    let p = Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![set(1, quotient(r(0))), store(r(3), r(1))],
                Control::Next,
            ),
            ins(
                1,
                vec![set(2, remainder(r(0)))],
                Control::Branch {
                    condition: r(4),
                    target: 1,
                },
            ),
            ins(2, vec![], Control::Return(r(2))),
        ],
    )
    .unwrap();
    assert!(
        ContextRemainders::analyze(&p)
            .unwrap()
            .evidence()
            .is_empty()
    );
}
#[test]
fn forged_source_points_quotient_certificate_keeper_or_new_program_fail() {
    let p = sample();
    let plan = ContextRemainders::analyze(&p).unwrap();
    let proof = plan.evidence()[0];
    for bad in [
        context_remainder::ContextEvidence {
            instruction: 99,
            ..proof
        },
        context_remainder::ContextEvidence {
            assignment: 0,
            ..proof
        },
        context_remainder::ContextEvidence {
            definition_assignment: 1,
            ..proof
        },
        context_remainder::ContextEvidence {
            quotient: Reg(0),
            ..proof
        },
        context_remainder::ContextEvidence {
            divisor: 9,
            ..proof
        },
        context_remainder::ContextEvidence {
            maximum_remainder: 0,
            ..proof
        },
        context_remainder::ContextEvidence {
            block_start: 99,
            ..proof
        },
        context_remainder::ContextEvidence {
            keeper: context_remainder::Keeper {
                instruction: 0,
                assignment: 0,
            },
            ..proof
        },
        context_remainder::ContextEvidence {
            keeper: context_remainder::Keeper {
                instruction: 0,
                assignment: 2,
            },
            ..proof
        },
    ] {
        assert!(!validate(&p, &bad));
    }
    let changed = single(vec![
        set(1, quotient(r(0))),
        store(r(3), r(1)),
        set(0, c(3)),
        set(2, remainder(r(0))),
    ]);
    assert!(!validate(&changed, &proof));
    assert!(
        plan.view(&p, 0, 2, &b(B::And, remainder(r(0)), c(0xffffffff)))
            .is_none()
    );
    assert!(plan.view(&p, 0, 2, &remainder(r(4))).is_none());
    assert!(plan.view(&p, 0, 8, &remainder(r(0))).is_none());
}
#[test]
fn loads_wrong_dividend_and_nonliteral_factors_decline() {
    let bad = Expr::select(c(1), r(0), Expr::load(c(u64::MAX), Width::U8));
    let p = single(vec![
        set(1, quotient(bad.clone())),
        store(r(3), r(1)),
        set(2, remainder(bad)),
    ]);
    assert!(
        ContextRemainders::analyze(&p)
            .unwrap()
            .evidence()
            .is_empty()
    );
    let p = single(vec![
        set(1, quotient(r(0))),
        store(r(3), r(1)),
        set(2, remainder(r(4))),
    ]);
    assert!(
        ContextRemainders::analyze(&p)
            .unwrap()
            .evidence()
            .is_empty()
    );
}
#[test]
fn whole_pass_bounds_discard_even_prior_valid_candidates() {
    let p = Program::new(0, 4097, vec![ins(0, vec![], Control::Return(c(0)))]).unwrap();
    assert!(ContextRemainders::analyze(&p).is_none());
    let mut a = sample().instructions()[0].assignments.clone();
    a.extend((10..2510).map(|i| set(i, quotient(r(0)))));
    let p = Program::new(0, 2510, vec![ins(0, a, Control::Return(r(2)))]).unwrap();
    assert!(ContextRemainders::analyze(&p).is_none());
    let mut deep = r(0);
    for _ in 0..130 {
        deep = b(B::Add, deep, c(0));
    }
    let p = Program::new(
        0,
        8,
        vec![
            ins(
                0,
                sample().instructions()[0].assignments.clone(),
                Control::Return(r(2)),
            ),
            ins(1, vec![store(deep, c(0))], Control::Return(c(0))),
        ],
    )
    .unwrap();
    assert!(ContextRemainders::analyze(&p).is_none());
}

fn actual_o2() -> Program {
    let out = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/context-remainder");
    std::fs::create_dir_all(&out).unwrap();
    let object = out.join("fixture-O2.o");
    native::object(
        &native::fixture_root().join("recovery/unsigned-div-constant.c"),
        &object,
        "-O2",
        "fixture",
    );
    let f = nirvana::frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
    let reduced = nirvana::reduce::reduce(&f.program).unwrap();
    let web = nirvana::web::split(reduced.program()).unwrap();
    nirvana::web_verify::validate(reduced.program(), web.program()).unwrap();
    let masked = nirvana::load_mask::propose(web.program(), reduced.parameters()).and_then(|p| {
        nirvana::load_mask::validate(web.program(), &p, reduced.parameters())
            .ok()
            .map(|_| p)
    });
    let selected = masked.as_ref().unwrap_or_else(|| web.program());
    let widths = nirvana::value_width::ValueWidths::analyze(selected);
    let width = |r| {
        if reduced.parameters().contains(&r) {
            Width::U64
        } else {
            widths.width(r)
        }
    };
    let mut ins = selected.instructions().to_vec();
    for i in &mut ins {
        for a in &mut i.assignments {
            a.value = nirvana::presentation::normalize(&a.value, width);
            if let Place::Memory { address, .. } = &mut a.destination {
                *address = nirvana::presentation::normalize(address, width);
            }
        }
        match &mut i.control {
            Control::Branch { condition, .. } | Control::Return(condition) => {
                *condition = nirvana::presentation::normalize(condition, width)
            }
            _ => {}
        }
    }
    Program::new(
        selected.cfg().block(selected.cfg().entry()).start,
        selected.register_count(),
        ins,
    )
    .unwrap()
}
#[test]
fn actual_o2_point_bound_view_keeps_the_captured_load_and_earlier_quotient_store() {
    let p = actual_o2();
    let before = p.instructions().to_vec();
    let plan = ContextRemainders::analyze(&p).unwrap();
    assert_eq!(plan.evidence().len(), 1);
    let proof = plan.evidence()[0];
    assert_eq!(
        (proof.definition_instruction, proof.definition_assignment),
        (27, 0)
    );
    assert_eq!((proof.keeper.instruction, proof.keeper.assignment), (35, 0));
    assert_eq!((proof.instruction, proof.assignment), (42, 0));
    assert_eq!(proof.quotient, Reg(59));
    assert!(validate(&p, &proof));
    assert_eq!(p.instructions(), before);
}

fn c_expr(e: &Expr) -> String {
    match e {
        Expr::Register(r) => format!("r[{}]", r.0),
        Expr::Const(x) => format!("UINT64_C({x})"),
        Expr::Binary(op, a, b) => format!(
            "((uint64_t)({} {} {}))",
            c_expr(a),
            match op {
                B::Sub => "-",
                B::Mul => "*",
                B::Add => "+",
                _ => panic!(),
            },
            c_expr(b)
        ),
        _ => panic!(),
    }
}
fn native_full_state(p: &Program, captured: bool, name: &str) {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/context-remainder")
        .join(name);
    std::fs::create_dir_all(&dir).unwrap();
    let plan = ContextRemainders::analyze(p).unwrap();
    assert_eq!(plan.evidence().len(), 1);
    let proof = plan.evidence()[0];
    let assignment = &p
        .instructions()
        .iter()
        .find(|i| i.address == proof.instruction)
        .unwrap()
        .assignments[proof.assignment];
    let view = plan
        .view(
            p,
            proof.instruction,
            proof.assignment,
            &assignment.value.clone(),
        )
        .unwrap();
    let raw = nirvana::emit::emit_c(p).unwrap().code;
    let old = c_expr(&assignment.value);
    assert_eq!(raw.matches(&old).count(), 1);
    let raw = raw.replace(
        &old,
        &format!("({} % UINT64_C({}))", c_expr(view.value), view.divisor),
    );
    let mut source = checked_c::instrument(&raw);
    let count = p.register_count();
    writeln!(source,"\n#undef abort\n#include <stdio.h>\n#include <inttypes.h>\nstatic jmp_buf jump;static uint64_t regs[{count}],result;static uint8_t memory[64];static unsigned fault,row;_Noreturn void nirvana_test_abort(void){{longjmp(jump,1);}}\nint main(void){{static const uint64_t xs[6]={{0,1,9,10,UINT64_MAX,UINT64_C(0x8000000000000000)}};static const uint64_t as[6]={{4096,4104,4128,4152,4159,UINT64_MAX}};for(row=0;row<36;++row){{for(unsigned i=0;i<{count};++i)regs[i]=UINT64_C(0xfedcba9876543210)^((uint64_t)i*UINT64_C(0x9e3779b9));for(unsigned i=0;i<64;++i)memory[i]=(uint8_t)(i*29+7);uint64_t x=xs[row/6];for(unsigned i=0;i<8;++i)memory[i]=(uint8_t)(x>>(i*8));").unwrap();
    if captured {
        source.push_str("regs[3]=as[row%6];regs[4]=4096;\n");
    } else {
        source.push_str("regs[7]=as[row%6];regs[4]=4152;\n");
    }
    source.push_str("result=0;fault=0;nirvana_test_address=0;nirvana_test_access=0;nirvana_test_width=0;if(setjmp(jump)==0)result=nirvana_fn(regs,memory,4096,64);else fault=1;printf(\"%u %\" PRIu64 \" %u %\" PRIu64 \" %\" PRIu64,fault,fault?nirvana_test_address:UINT64_C(0),fault?nirvana_test_access:0,fault?nirvana_test_width:UINT64_C(0),result);\n");
    writeln!(source,"for(unsigned i=0;i<{count};++i){{printf(\" %\" PRIu64,regs[i]);}}\nfor(unsigned i=0;i<64;++i){{printf(\" %u\",(unsigned)memory[i]);}}\nputchar('\\n');}}return 0;}}").unwrap();
    let path = dir.join("prototype.c");
    std::fs::write(&path, source).unwrap();
    let mut expected = vec![];
    for x in [0, 1, 9, 10, u64::MAX, 1 << 63] {
        for addr in [4096, 4104, 4128, 4152, 4159, u64::MAX] {
            let mut input: Vec<_> = (0..count)
                .map(|i| 0xfedcba9876543210 ^ ((i as u64) * 0x9e3779b9))
                .collect();
            if captured {
                input[3] = addr;
                input[4] = 4096;
            } else {
                input[7] = addr;
                input[4] = 4152;
            }
            let mut memory: Vec<_> = (0..64).map(|i| (i * 29 + 7) as u8).collect();
            memory[..8].copy_from_slice(&x.to_le_bytes());
            let run = p.run_with_memory(&input, 4096, &memory, 1000).unwrap();
            let mut fields = match run.status {
                RunStatus::Returned(v) => vec![0, 0, 0, 0, v],
                RunStatus::Fault(f) => vec![
                    1,
                    f.address,
                    if f.access == ir::AccessKind::Read {
                        1
                    } else {
                        2
                    },
                    f.width.bytes() as u64,
                    0,
                ],
                _ => panic!(),
            };
            fields.extend(run.state.registers);
            fields.extend(run.state.memory.into_iter().map(u64::from));
            expected.push(fields);
        }
    }
    for opt in ["-O0", "-O2"] {
        let object = dir.join(format!("prototype{opt}.o"));
        let binary = dir.join(format!("prototype{opt}"));
        native::object(&path, &object, opt, "unused");
        native::link(&[&object], &binary);
        assert_eq!(native::run_fields(&binary, "", 5 + count + 64), expected);
    }
}
#[test]
fn native_context_modulo_preserves_all_registers_memory_and_first_fault_prefix() {
    let p = single(vec![
        set(0, Expr::load(r(4), Width::U64)),
        set(1, quotient(r(0))),
        store(r(3), r(1)),
        set(2, remainder(r(0))),
    ]);
    native_full_state(&p, true, "captured-alias");
    native_full_state(&actual_o2(), false, "actual-O2");
}

#[test]
fn narrow_dividend_is_source_bound_and_width_erasure_cannot_reuse_a_stale_view() {
    let x = b(B::And, r(0), c(0xffffffff));
    let q = b(B::Shr, b(B::Mul, x.clone(), c(0xcccccccd)), c(35));
    let p = single(vec![set(1, q), store(r(3), r(1)), set(2, remainder(x))]);
    let plan = ContextRemainders::analyze(&p).unwrap();
    assert_eq!(plan.evidence().len(), 1);
    let source = &p.instructions()[0].assignments[2].value;
    assert!(plan.view(&p, 0, 2, &source.clone()).is_some());
    let normalized = nirvana::presentation::normalize(source, |_| Width::U32);
    assert_ne!(&normalized, source);
    assert!(plan.view(&p, 0, 2, &normalized).is_none());
    let p = single(vec![
        set(1, quotient(r(0))),
        store(r(3), r(1)),
        set(1, remainder(r(0))),
    ]);
    let plan = ContextRemainders::analyze(&p).unwrap();
    assert_eq!(plan.evidence().len(), 1);
    assert!(validate(&p, &plan.evidence()[0]));
}
