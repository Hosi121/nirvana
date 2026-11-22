use crate::support::ir::{c, r};
use nirvana::{
    block_verify::paths::{InputProfile, Reachability, SymbolicWord, path_query},
    ir::{Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, Width},
    verify::Solver,
};
use std::{path::Path, time::Duration};

fn ins(pc: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address: pc,
        size: 1,
        assignments,
        control,
    }
}
fn set(reg: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(reg).into(),
        value,
    }
}
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn load() -> Expr {
    Expr::load(c(100), Width::U64)
}
fn profile() -> InputProfile {
    InputProfile {
        registers: vec![0],
        memory_base: 100,
        memory: vec![0x71; 16],
        words: vec![SymbolicWord {
            offset: 0,
            width: Width::U64,
        }],
    }
}
fn check(
    name: &str,
    program: &Program,
    profile: &InputProfile,
    prefix: &[u64],
    next: u64,
) -> Reachability {
    let query = path_query(program, profile, prefix, next).unwrap();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/path-inputs");
    std::fs::create_dir_all(&root).unwrap();
    std::fs::write(
        root.join(format!("{name}.smt2")),
        format!("{}(check-sat)\n", query.smt2()),
    )
    .unwrap();
    let solver = Solver::new(std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into()))
        .with_timeout(Duration::from_secs(5));
    let result = query.check(&solver);
    std::fs::write(root.join(format!("{name}.out")), format!("{result:?}\n")).unwrap();
    result
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn path_inputs_replay_overflow_memory_aliases_lazy_faults_and_loop_iterations() {
    let branch = |condition| Control::Branch {
        condition,
        target: 2,
    };
    let make = |assignments, condition| {
        Program::new(
            0,
            1,
            vec![
                ins(0, assignments, branch(condition)),
                ins(1, vec![], Control::Return(c(0))),
                ins(2, vec![], Control::Return(c(1))),
            ],
        )
        .unwrap()
    };
    let overflow = make(vec![], b(B::Eq, b(B::Add, load(), c(1)), c(0)));
    let Reachability::Witness(w) = check("overflow", &overflow, &profile(), &[0], 2) else {
        panic!("overflow witness missing")
    };
    assert_eq!(w.words, [u64::MAX]);
    let mut narrow = profile();
    narrow.words[0].width = Width::U8;
    assert_eq!(
        check("fixed-other-bytes", &overflow, &narrow, &[0], 2),
        Reachability::InfeasiblePrefix
    );

    let alias = make(
        vec![Assignment {
            destination: Place::Memory {
                address: c(101),
                width: Width::U8,
            },
            value: Expr::load(c(100), Width::U8),
        }],
        b(B::Eq, Expr::load(c(101), Width::U8), c(0xa7)),
    );
    let Reachability::Witness(w) = check("partial-alias", &alias, &profile(), &[0], 2) else {
        panic!("alias witness missing")
    };
    assert_eq!(w.words[0] & 255, 0xa7);

    let lazy = make(
        vec![set(
            0,
            Expr::select(load(), Expr::load(c(999), Width::U8), c(7)),
        )],
        r(0),
    );
    let Reachability::Witness(w) = check("lazy-fault", &lazy, &profile(), &[0], 2) else {
        panic!("lazy witness missing")
    };
    assert_eq!(w.words, [0]);
    let fault = make(
        vec![Assignment {
            destination: Place::Memory {
                address: c(999),
                width: Width::U8,
            },
            value: load(),
        }],
        c(1),
    );
    assert_eq!(
        check("destination-fault", &fault, &profile(), &[0], 2),
        Reachability::InfeasiblePrefix
    );

    let loops = Program::new(
        0,
        1,
        vec![
            ins(0, vec![set(0, load())], Control::Next),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: b(B::Ule, r(0), c(2)),
                    target: 3,
                },
            ),
            ins(2, vec![], Control::Return(r(0))),
            ins(
                3,
                vec![Assignment {
                    destination: Place::Memory {
                        address: c(100),
                        width: Width::U64,
                    },
                    value: b(B::Add, r(0), c(1)),
                }],
                Control::Jump(0),
            ),
        ],
    )
    .unwrap();
    for iterations in 1..=4 {
        let prefix: Vec<_> = (0..iterations)
            .flat_map(|_| [0, 1, 3])
            .chain([0, 1])
            .collect();
        let result = check(
            &format!("loop-{iterations}"),
            &loops,
            &profile(),
            &prefix,
            2,
        );
        if iterations <= 3 {
            let Reachability::Witness(w) = result else {
                panic!("loop witness missing")
            };
            assert_eq!(w.words, [3 - iterations as u64]);
        } else {
            assert_eq!(result, Reachability::InfeasiblePrefix);
        }
    }

    let paths = Program::new(
        0,
        1,
        vec![
            ins(0, vec![], branch(load())),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: load(),
                    target: 3,
                },
            ),
            ins(2, vec![], Control::Jump(3)),
            ins(3, vec![], Control::Return(c(0))),
        ],
    )
    .unwrap();
    assert_eq!(
        check("one-infeasible-prefix", &paths, &profile(), &[0, 1], 3),
        Reachability::InfeasiblePrefix
    );
    assert!(matches!(
        check("another-feasible-prefix", &paths, &profile(), &[0, 2], 3),
        Reachability::Witness(_)
    ));
}
