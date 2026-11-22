//! Reordering adjacent stores after successful reads of both ranges.
//! The checked flat RW model observes all RAM and the exact first fault.
//! Prefix loads and pure RHS values are premises, not optimizer hints.
use crate::support::ir::{c, r};
use nirvana::{
    block_verify::{BlockVerdict, block_query},
    ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width},
    verify::Solver,
};
use std::{path::Path, process::Command, time::Duration};

fn add(a: Expr, b: Expr) -> Expr {
    Expr::binary(BinaryOp::Add, a, b)
}
fn set(reg: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(reg).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn pair(prefix: Vec<Assignment>, a: Assignment, b: Assignment) -> (Program, Program) {
    let build = |first, second| {
        let mut assignments = prefix.clone();
        assignments.extend([first, second]);
        Program::new(
            0,
            8,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments,
                control: Control::Return(c(0)),
            }],
        )
        .unwrap()
    };
    (build(a.clone(), b.clone()), build(b, a))
}
fn check(root: &Path, name: &str, a: &Program, b: &Program) -> BlockVerdict {
    let regs: Vec<_> = (0..8).map(Reg).collect();
    let query = block_query(a, b, 0, &regs, &[]).unwrap();
    std::fs::write(
        root.join(format!("{name}.smt2")),
        format!("{}(check-sat)\n", query.smt2()),
    )
    .unwrap();
    let solver = Solver::new(std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into()))
        .with_timeout(Duration::from_secs(10));
    let result = query.check(&solver);
    std::fs::write(root.join(format!("{name}.out")), format!("{result:?}\n")).unwrap();
    result
}
fn counterexample(root: &Path, name: &str, a: &Program, b: &Program) {
    let BlockVerdict::Counterexample(witness) = check(root, name, a, b) else {
        panic!("missing replayed witness: {name}")
    };
    let before = a
        .run_block_with_memory(
            0,
            &witness.before_registers,
            witness.memory_base,
            &witness.memory,
        )
        .unwrap();
    let after = b
        .run_block_with_memory(
            0,
            &witness.after_registers,
            witness.memory_base,
            &witness.memory,
        )
        .unwrap();
    assert!(
        before.exit != after.exit || before.state.memory != after.state.memory,
        "{name}"
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn successful_read_ranges_allow_disjoint_pure_store_permutations() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/store-order");
    std::fs::create_dir_all(&root).unwrap();
    let widths = [Width::U8, Width::U16, Width::U32, Width::U64];
    let mut proved = 0;
    for a_width in widths {
        for b_width in widths {
            let b = add(r(0), c(24));
            let (before, after) = pair(
                vec![
                    set(3, Expr::load(r(0), a_width)),
                    set(4, Expr::load(b.clone(), b_width)),
                ],
                store(r(0), a_width, r(1)),
                store(b, b_width, r(2)),
            );
            assert_eq!(
                check(
                    &root,
                    &format!("disjoint-{}-{}", a_width.bits(), b_width.bits()),
                    &before,
                    &after
                ),
                BlockVerdict::EquivalentUnderModel
            );
            proved += 1;
        }
    }
    for width in widths {
        let b = add(r(0), c((-16i64) as u64));
        let (before, after) = pair(
            vec![
                set(3, Expr::load(r(0), width)),
                set(4, Expr::load(b.clone(), width)),
            ],
            store(r(0), width, r(1)),
            store(b, width, r(2)),
        );
        assert_eq!(
            check(
                &root,
                &format!("negative-offset-{}", width.bits()),
                &before,
                &after
            ),
            BlockVerdict::EquivalentUnderModel
        );
        proved += 1;
    }
    // The implementation accepts any relative offset, including wraparound.
    // Bind the exact modular non-overlap premise to an otherwise arbitrary r6.
    // All byte values, inputs, base and size retain the block model's domains.
    for a_width in widths {
        for b_width in widths {
            let b = add(r(0), r(6));
            let (before, after) = pair(
                vec![
                    set(3, Expr::load(r(0), a_width)),
                    set(4, Expr::load(b.clone(), b_width)),
                ],
                store(r(0), a_width, r(1)),
                store(b, b_width, r(2)),
            );
            let regs: Vec<_> = (0..8).map(Reg).collect();
            let query = block_query(&before, &after, 0, &regs, &[]).unwrap();
            let script = format!(
                "{}; disjoint relative byte ranges modulo 2^64\n(assert (and (bvuge r6 (_ bv{} 64)) (bvuge (bvneg r6) (_ bv{} 64))))\n(check-sat)\n",
                query.smt2(),
                a_width.bytes(),
                b_width.bytes()
            );
            let name = format!("arbitrary-offset-{}-{}", a_width.bits(), b_width.bits());
            let path = root.join(format!("{name}.smt2"));
            std::fs::write(&path, script).unwrap();
            let output =
                Command::new(std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into()))
                    .args(["-T:10", "-smt2"])
                    .arg(path)
                    .output()
                    .unwrap();
            std::fs::write(root.join(format!("{name}.out")), &output.stdout).unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(
                String::from_utf8_lossy(&output.stdout).trim(),
                "unsat",
                "{name}"
            );
            proved += 1;
        }
    }
    let b = add(r(0), c(24));
    let (before, after) = pair(
        vec![],
        store(r(0), Width::U64, r(1)),
        store(b.clone(), Width::U64, r(2)),
    );
    counterexample(&root, "missing-range-premises", &before, &after);
    let (before, after) = pair(
        vec![set(
            3,
            Expr::select(
                r(5),
                Expr::load(r(0), Width::U64),
                Expr::load(b.clone(), Width::U64),
            ),
        )],
        store(r(0), Width::U64, r(1)),
        store(b.clone(), Width::U64, r(2)),
    );
    counterexample(&root, "conditional-reads", &before, &after);
    let overlap = add(r(0), c(4));
    let (before, after) = pair(
        vec![
            set(3, Expr::load(r(0), Width::U64)),
            set(4, Expr::load(overlap.clone(), Width::U64)),
        ],
        store(r(0), Width::U64, r(1)),
        store(overlap, Width::U64, r(2)),
    );
    counterexample(&root, "overlapping-ranges", &before, &after);
    let prefix = vec![
        set(3, Expr::load(r(0), Width::U64)),
        set(4, Expr::load(b.clone(), Width::U64)),
    ];
    let (before, after) = pair(
        prefix.clone(),
        store(r(0), Width::U64, Expr::load(b.clone(), Width::U64)),
        store(b.clone(), Width::U64, r(2)),
    );
    counterexample(&root, "rhs-reads-memory", &before, &after);
    let mut changed_base = prefix;
    changed_base.push(set(0, add(r(0), c(4096))));
    let (before, after) = pair(
        changed_base,
        store(r(0), Width::U64, r(1)),
        store(b, Width::U64, r(2)),
    );
    counterexample(&root, "changed-base-value", &before, &after);
    let (before, after) = pair(
        vec![
            set(3, Expr::load(r(0), Width::U64)),
            set(4, Expr::load(r(6), Width::U64)),
        ],
        store(r(0), Width::U64, r(1)),
        store(r(6), Width::U64, r(2)),
    );
    counterexample(&root, "distinct-inputs-can-alias", &before, &after);
    std::fs::write(root.join("result.json"), format!("{{\"model\":\"checked-memory-block-v1\",\"equivalent_queries\":{proved},\"replayed_counterexamples\":6}}\n")).unwrap();
}
