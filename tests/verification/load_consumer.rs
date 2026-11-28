//! Whole-word/RAM checks for the actual strict load-consumer constructor.
use crate::support::ir::{c, r};
use nirvana::block_verify::region::{self, Verdict};
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, UnaryOp, Width,
};
use nirvana::transform::load_consumer;
use nirvana::verify::Solver;

#[path = "load_consumer/stable.rs"]
mod stable;

fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn source(value: Expr) -> Program {
    Program::new(
        0,
        8,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Place::Memory {
                            address: c(4096),
                            width: Width::U8,
                        },
                        value: c(91),
                    },
                    set(1, Expr::load(r(0), Width::U64)),
                ],
                control: Control::Next,
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![
                    set(3, Expr::load(r(7), Width::U8)),
                    Assignment {
                        destination: Place::Memory {
                            address: c(4104),
                            width: Width::U8,
                        },
                        value: c(173),
                    },
                ],
                control: Control::Next,
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![set(2, value)],
                control: Control::Return(r(2)),
            },
        ],
    )
    .unwrap()
}
fn compare(before: &Program, after: &Program) -> region::Query {
    let inputs: Vec<_> = (0..8).map(Reg).collect();
    let outputs: Vec<_> = (0..8).filter(|n| *n != 1).map(Reg).collect();
    region::query(before, after, &inputs, &outputs).unwrap()
}

#[test]
#[ignore = "requires NIRVANA_Z3 and NIRVANA_LOAD_CONSUMER_OUT"]
fn strict_load_consumer_folds_cover_free_words_ram_aliases_and_ordered_faults() {
    let out = std::path::PathBuf::from(std::env::var_os("NIRVANA_LOAD_CONSUMER_OUT").unwrap());
    std::fs::create_dir_all(&out).unwrap();
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap());
    for (n, value) in [
        b(B::Add, b(B::And, r(1), c(3)), c(1)),
        b(B::SDiv, r(1), c(0)),
        Expr::unary(UnaryOp::SignExtend(Width::U8), r(1)),
        b(B::UMulHigh, r(1), c(1 << 63)),
    ]
    .into_iter()
    .enumerate()
    {
        let source = source(value);
        let candidate = load_consumer::propose(&source, &[Reg(0), Reg(7)]).unwrap();
        load_consumer::validate(&source, &candidate, &[Reg(0), Reg(7)]).unwrap();
        let query = compare(&source, &candidate);
        std::fs::write(out.join(format!("fold-{n}.smt2")), query.smt2()).unwrap();
        assert_eq!(query.check(&solver), Verdict::EquivalentUnderModel);
    }
    let source = source(b(B::And, r(1), c(0)));
    let candidate = load_consumer::propose(&source, &[]).unwrap();
    for n in 0..2 {
        let mut instructions = candidate.instructions().to_vec();
        instructions[0].assignments[1].value = c(0);
        if n == 1 {
            instructions[2].assignments[0].value = b(B::And, Expr::load(r(0), Width::U64), c(0));
        }
        let wrong = Program::new(0, 8, instructions).unwrap();
        assert!(load_consumer::validate(&source, &wrong, &[]).is_err());
        let query = compare(&source, &wrong);
        std::fs::write(out.join(format!("wrong-{n}.smt2")), query.smt2()).unwrap();
        let Verdict::Counterexample(witness) = query.check(&solver) else {
            panic!("load removal/order must replay a fault difference")
        };
        assert_ne!(witness.before.status, witness.after.status);
        std::fs::write(
            out.join(format!("wrong-{n}.txt")),
            format!("{witness:#?}\n"),
        )
        .unwrap();
    }
    println!("LOAD-CONSUMER 4 full-word/all-RAM UNSAT; 2 IR-replayed fault/order SAT controls");
}
