use super::*;
use crate::verification::block_verify::{self, BlockVerdict};
use crate::verification::verify::Solver;
#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn actual_lifting_clips_and_checked_reads_have_universal_correspondence() {
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/lifting-clips");
    std::fs::create_dir_all(&root).unwrap();
    let widths = [Width::U8, Width::U16, Width::U32, Width::U64];
    let mut values = vec![
        r(0),
        k(0),
        k(255),
        k(u64::MAX),
        add(r(0), r(1)),
        eq(r(0), r(1)),
        and(k(7), r(0)),
        and(r(0), k(65535)),
        and(r(0), k(1 << 63)),
    ];
    for width in widths {
        values.push(Expr::load(r(2), width));
        values.push(Expr::unary(
            crate::model::ir::UnaryOp::Extract { start: 8, width },
            r(0),
        ));
    }
    values.push(Expr::load(Expr::load(r(2), Width::U64), Width::U16));
    let program = |value| {
        Program::new(
            0,
            3,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(0).into(),
                    value,
                }],
                control: Control::Return(r(0)),
            }],
        )
        .unwrap()
    };
    let prefix: Vec<_> = (0..3).map(Reg).collect();
    let mut proved = 0;
    for width in widths {
        for (i, value) in values.iter().enumerate() {
            let source = program(and(value.clone(), k(width.mask())));
            let candidate = program(mask(value.clone(), width));
            let query =
                block_verify::block_query(&source, &candidate, 0, &prefix, &prefix).unwrap();
            let name = format!("clip-{}-{i}", width.bits());
            std::fs::write(
                root.join(format!("{name}.smt2")),
                format!("{}(check-sat)\n", query.smt2()),
            )
            .unwrap();
            let verdict = query.check(&solver);
            std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
            assert_eq!(verdict, BlockVerdict::EquivalentUnderModel, "{name}");
            proved += 1;
        }
    }
    for (name, a, z) in [
        ("lost-clip", and(r(0), k(255)), r(0)),
        ("lost-read", and(Expr::load(r(2), Width::U8), k(0)), k(0)),
    ] {
        let query =
            block_verify::block_query(&program(a), &program(z), 0, &prefix, &prefix).unwrap();
        std::fs::write(
            root.join(format!("{name}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let verdict = query.check(&solver);
        std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
        assert!(
            matches!(verdict, BlockVerdict::Counterexample(_)),
            "{name}: {verdict:?}"
        );
    }
    println!(
        "{proved} universal actual lifting clip/RAM/first-fault proofs; 2 IR-replayed width/read SAT controls"
    );
}
