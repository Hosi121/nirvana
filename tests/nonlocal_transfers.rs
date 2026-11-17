//! Regression cases with observable work on both sides of loop transfers.

use nirvana::emit::emit_c;
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Program, Reg};
use nirvana::structure::{Node, StructuredFunction};

fn reg(index: usize) -> Expr {
    Expr::Register(Reg(index))
}

fn constant(value: u64) -> Expr {
    Expr::Const(value)
}

fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}

fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}

fn add(index: usize, value: u64) -> Assignment {
    set(index, binary(BinaryOp::Add, reg(index), constant(value)))
}

fn branch(condition: Expr, target: u64) -> Control {
    Control::Branch { condition, target }
}

fn three_loops() -> Program {
    use Control::{Jump, Next, Return};
    let blocks = vec![
        (vec![set(1, constant(0)), set(4, constant(0))], Next),
        (
            vec![],
            branch(binary(BinaryOp::Ult, reg(1), constant(3)), 3),
        ),
        (vec![], Return(reg(4))),
        (vec![set(2, constant(0))], Next),
        (
            vec![],
            branch(binary(BinaryOp::Ult, reg(2), constant(2)), 6),
        ),
        (vec![add(1, 1), add(4, 100)], Jump(1)),
        (vec![set(3, constant(0))], Next),
        (
            vec![],
            branch(binary(BinaryOp::Ult, reg(3), constant(2)), 9),
        ),
        (vec![add(2, 1), add(4, 10)], Jump(4)),
        (
            vec![add(3, 1), add(4, 1)],
            branch(
                binary(
                    BinaryOp::And,
                    binary(BinaryOp::And, reg(0), constant(1)),
                    binary(BinaryOp::Eq, reg(1), constant(0)),
                ),
                12,
            ),
        ),
        (
            vec![],
            branch(binary(BinaryOp::And, reg(0), constant(2)), 13),
        ),
        (vec![], Jump(7)),
        // This tail continues the outermost loop from inside two loops.
        (vec![add(1, 1), add(4, 1000)], Jump(1)),
        // This tail breaks all three loops.
        (vec![add(4, 10000)], Jump(2)),
    ];
    Program::new(
        0,
        5,
        blocks
            .into_iter()
            .enumerate()
            .map(|(address, (assignments, control))| IrInstruction {
                address: address as u64,
                size: 1,
                assignments,
                control,
            })
            .collect(),
    )
    .unwrap()
}

fn contains_node(nodes: &[Node], expected: &Node) -> bool {
    nodes.iter().any(|node| {
        node == expected
            || match node {
                Node::Loop(body) => contains_node(body, expected),
                Node::If {
                    taken, not_taken, ..
                } => contains_node(taken, expected) || contains_node(not_taken, expected),
                _ => false,
            }
    })
}

fn loop_in_exit_tail() -> Program {
    use Control::{Jump, Next, Return};
    let blocks = vec![
        (vec![set(1, constant(0)), set(4, constant(0))], Next),
        (
            vec![],
            branch(binary(BinaryOp::Ult, reg(1), constant(3)), 3),
        ),
        (vec![], Return(reg(4))),
        (vec![set(2, constant(0))], Next),
        (
            vec![],
            branch(binary(BinaryOp::Ult, reg(2), constant(2)), 6),
        ),
        (vec![set(3, constant(0))], Jump(9)),
        (
            vec![add(2, 1), add(4, 1)],
            branch(binary(BinaryOp::And, reg(0), constant(1)), 8),
        ),
        (vec![], Jump(4)),
        (vec![add(1, 1), add(4, 100)], Jump(1)),
        (
            vec![],
            branch(binary(BinaryOp::Ult, reg(3), constant(2)), 11),
        ),
        (vec![add(1, 1), add(4, 10)], Jump(1)),
        (
            vec![add(3, 1), add(4, 1)],
            branch(
                binary(
                    BinaryOp::And,
                    binary(BinaryOp::And, reg(0), constant(2)),
                    // Normalize to a bit before combining with the mode mask.
                    binary(
                        BinaryOp::Mul,
                        binary(BinaryOp::Eq, reg(1), constant(0)),
                        constant(2),
                    ),
                ),
                8,
            ),
        ),
        (
            vec![],
            branch(binary(BinaryOp::And, reg(0), constant(4)), 14),
        ),
        (vec![], Jump(9)),
        (vec![add(4, 1000)], Jump(2)),
    ];
    Program::new(
        0,
        5,
        blocks
            .into_iter()
            .enumerate()
            .map(|(address, (assignments, control))| IrInstruction {
                address: address as u64,
                size: 1,
                assignments,
                control,
            })
            .collect(),
    )
    .unwrap()
}

#[test]
fn transfers_across_three_loops_preserve_every_instruction_and_register() {
    let program = three_loops();
    let function = StructuredFunction::recover(&program).unwrap();
    assert!(contains_node(
        function.body(),
        &Node::ContinueOuter { levels: 2 }
    ));
    assert!(contains_node(
        function.body(),
        &Node::BreakOuter { levels: 2 }
    ));
    let output = emit_c(&program);
    assert!(output.code.contains("goto nirvana_loop_"));
    assert!(!output.code.contains("nirvana_transfer"));
    assert!(!output.code.contains("nirvana_continue"));
    assert!(function.stats().emitted_block_copies <= function.stats().unique_blocks * 2);
    for mode in 0..4 {
        let input = [mode, 999, 998, 997, u64::MAX];
        for limit in 0..160 {
            assert_eq!(
                program.execute(&input, limit),
                function.execute(&input, limit),
                "mode={mode}, instruction limit={limit}"
            );
        }
        let execution = program.execute(&input, 160).unwrap();
        assert_eq!(execution.value, [372, 1249, 10001, 11002][mode as usize]);
    }
}

#[test]
fn moving_a_tail_preserves_transfers_inside_its_own_nested_loop() {
    let program = loop_in_exit_tail();
    let function = StructuredFunction::recover(&program).unwrap();
    assert!(contains_node(
        function.body(),
        &Node::ContinueOuter { levels: 2 }
    ));
    assert!(contains_node(
        function.body(),
        &Node::BreakOuter { levels: 2 }
    ));
    let output = emit_c(&program);
    assert!(output.code.contains("goto nirvana_loop_"));
    assert!(!output.code.contains("nirvana_transfer"));
    assert!(!output.code.contains("nirvana_continue"));
    for mode in 0..8 {
        let input = [mode, 999, 998, 997, u64::MAX];
        for limit in 0..160 {
            assert_eq!(
                program.execute(&input, limit),
                function.execute(&input, limit),
                "mode={mode}, limit={limit}"
            );
        }
        let result = program.execute(&input, 160).unwrap().value;
        assert_eq!(
            result,
            [42, 303, 131, 303, 1003, 303, 1106, 303][mode as usize]
        );
    }
}

#[test]
fn emitted_c_targets_the_correct_outer_loop_without_transfer_state() {
    check_native(&three_loops(), 4);
    check_native(&loop_in_exit_tail(), 8);
}

fn check_native(program: &Program, mode_count: u64) {
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

    struct Scratch(std::path::PathBuf);
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let scratch = Scratch(
        std::env::temp_dir().join(format!("nirvana-transfers-{}-{nonce}", std::process::id())),
    );
    std::fs::create_dir(&scratch.0).unwrap();
    let mut source = emit_c(program).code;
    source.push_str(&format!("\n#define MODE_COUNT {mode_count}\n"));
    source.push_str(
        r#"
#include <inttypes.h>
#include <stdio.h>
int main(void) {
    for (uint64_t mode = 0; mode < MODE_COUNT; ++mode) {
        uint64_t r[5] = {mode, 999, 998, 997, UINT64_MAX};
        uint64_t result = nirvana_fn(r);
        printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
               result, r[0], r[1], r[2], r[3], r[4]);
    }
    return 0;
}
"#,
    );
    let source_path = scratch.0.join("transfers.c");
    std::fs::write(&source_path, source).unwrap();
    for optimization in ["-O0", "-O2"] {
        let binary = scratch.0.join(format!("transfers{optimization}"));
        let compilation = Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                optimization,
            ])
            .arg(&source_path)
            .arg("-o")
            .arg(&binary)
            .output()
            .unwrap();
        assert!(
            compilation.status.success(),
            "{optimization}: {}",
            String::from_utf8_lossy(&compilation.stderr)
        );
        let mut child = Command::new(&binary)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(5);
        while child.try_wait().unwrap().is_none() {
            if Instant::now() >= deadline {
                let _ = child.kill();
                let _ = child.wait();
                panic!("{optimization}: generated C exceeded the execution timeout");
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success());
        let stdout = String::from_utf8(output.stdout).unwrap();
        let lines: Vec<_> = stdout.lines().collect();
        assert_eq!(lines.len(), mode_count as usize);
        for (mode, line) in lines.into_iter().enumerate() {
            let expected = program
                .execute(&[mode as u64, 999, 998, 997, u64::MAX], 160)
                .unwrap();
            let mut expected_values = vec![expected.value];
            expected_values.extend(expected.registers);
            let actual: Vec<u64> = line
                .split_whitespace()
                .map(|value| value.parse().unwrap())
                .collect();
            assert_eq!(actual, expected_values, "{optimization}, mode={mode}");
        }
    }
}
