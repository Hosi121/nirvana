//! SSE2 lane expressions versus byte permutations and scalar arithmetic.
use nirvana::{
    block_verify::{BlockVerdict, block_query},
    ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg},
    verify::Solver,
    x86,
};
use std::{path::Path, time::Duration};

fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn b(op: BinaryOp, x: Expr, y: Expr) -> Expr {
    Expr::binary(op, x, y)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Register(Reg(n)),
        value,
    }
}
fn program(size: u32, assignments: Vec<Assignment>) -> Program {
    Program::new(
        0,
        80,
        vec![IrInstruction {
            address: 0,
            size,
            assignments,
            control: Control::Return(c(0)),
        }],
    )
    .unwrap()
}
fn lanes(register: usize, low: Expr, high: Expr) -> Vec<Assignment> {
    vec![
        set(70, low),
        set(71, high),
        set(32 + register * 2, r(70)),
        set(33 + register * 2, r(71)),
    ]
}
fn bytes(register: usize, select: impl Fn(usize) -> Option<usize>) -> (Expr, Expr) {
    let output = |start| {
        (start..start + 8).fold(c(0), |word, i| {
            let Some(source) = select(i) else { return word };
            let byte = b(
                BinaryOp::And,
                b(
                    BinaryOp::Shr,
                    r(32 + register * 2 + source / 8),
                    c((source % 8 * 8) as u64),
                ),
                c(255),
            );
            b(
                BinaryOp::Or,
                word,
                b(BinaryOp::Mul, byte, c(1 << ((i - start) * 8))),
            )
        })
    };
    (output(0), output(8))
}
fn check(
    root: &Path,
    name: &str,
    code: &[u8],
    expected: Vec<Assignment>,
    solver: &Solver,
) -> BlockVerdict {
    let instruction = x86::decode_vector_at(code, 0).unwrap();
    assert!(instruction.memory.is_none());
    let a = program(instruction.size, instruction.assignments);
    let b = program(instruction.size, expected);
    let registers: Vec<_> = (0..64).map(Reg).collect();
    let query = block_query(&a, &b, 0, &registers, &registers).unwrap();
    std::fs::write(
        root.join(format!("{name}.smt2")),
        format!("{}(check-sat)\n", query.smt2()),
    )
    .unwrap();
    let verdict = query.check(solver);
    std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
    verdict
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn packed_sse2_results_preserve_arbitrary_architectural_registers() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/vector-lanes");
    std::fs::create_dir_all(&root).unwrap();
    let solver = Solver::new(std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into()))
        .with_timeout(Duration::from_secs(5));
    let mut proved = 0;
    for order in 0..=255_u8 {
        let (low, high) = bytes(15, |i| {
            Some(usize::from((order >> (i / 4 * 2)) & 3) * 4 + i % 4)
        });
        assert_eq!(
            check(
                &root,
                &format!("pshufd-{order}"),
                &[0x66, 0x45, 0x0f, 0x70, 0xff, order],
                lanes(15, low, high),
                &solver
            ),
            BlockVerdict::EquivalentUnderModel
        );
        proved += 1;
    }
    for count in (0..=65_u8).chain([255]) {
        let divided = |reg| {
            if count >= 64 {
                c(0)
            } else {
                b(BinaryOp::UDiv, r(reg), c(1_u64 << count))
            }
        };
        assert_eq!(
            check(
                &root,
                &format!("psrlq-{count}"),
                &[0x66, 0x41, 0x0f, 0x73, 0xd7, count],
                lanes(15, divided(62), divided(63)),
                &solver
            ),
            BlockVerdict::EquivalentUnderModel
        );
        proved += 1;
    }
    for count in (0..=16_u8).chain([255]) {
        let (low, high) = bytes(15, |i| {
            (i + usize::from(count) < 16).then_some(i + usize::from(count))
        });
        assert_eq!(
            check(
                &root,
                &format!("psrldq-{count}"),
                &[0x66, 0x41, 0x0f, 0x73, 0xdf, count],
                lanes(15, low, high),
                &solver
            ),
            BlockVerdict::EquivalentUnderModel
        );
        proved += 1;
    }
    for source in [0, 15] {
        let add = |n| {
            b(
                BinaryOp::Sub,
                r(62 + n),
                b(BinaryOp::Sub, c(0), r(32 + source * 2 + n)),
            )
        };
        assert_eq!(
            check(
                &root,
                &format!("paddq-{source}"),
                &[
                    0x66,
                    0x44 | u8::from(source >= 8),
                    0x0f,
                    0xd4,
                    0xf8 | (source as u8 & 7)
                ],
                lanes(15, add(0), add(1)),
                &solver
            ),
            BlockVerdict::EquivalentUnderModel
        );
        proved += 1;
        for gpr in [0, 10, 15] {
            let rex = 0x48 | if source >= 8 { 4 } else { 0 } | if gpr >= 8 { 1 } else { 0 };
            assert_eq!(
                check(
                    &root,
                    &format!("movq-{source}-{gpr}"),
                    &[
                        0x66,
                        rex,
                        0x0f,
                        0x7e,
                        0xc0 | ((source as u8 & 7) << 3) | (gpr as u8 & 7)
                    ],
                    vec![set(gpr, r(32 + source * 2))],
                    &solver
                ),
                BlockVerdict::EquivalentUnderModel
            );
            proved += 1;
        }
    }
    let bad = lanes(
        15,
        b(BinaryOp::Shr, r(62), c(64)),
        b(BinaryOp::Shr, r(63), c(64)),
    );
    let verdict = check(
        &root,
        "masked-shift-is-wrong",
        &[0x66, 0x41, 0x0f, 0x73, 0xd7, 64],
        bad,
        &solver,
    );
    let BlockVerdict::Counterexample(witness) = verdict else {
        panic!("missing replayed shift-width counterexample")
    };
    assert_ne!(
        witness.before.state.registers[62..64],
        witness.after.state.registers[62..64]
    );
    std::fs::write(root.join("result.json"),format!("{{\"model\":\"sse2-register-lanes-v1\",\"equivalent\":{proved},\"replayed_counterexamples\":1}}\n")).unwrap();
}
