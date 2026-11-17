//! Evaluation-only entry-stack facts for an original nondebug ELF function.
use std::collections::BTreeSet;

use nirvana::{
    frontend,
    ir::{AccessKind, Expr, Reg},
    stack::StackAnalysis,
    x86,
};

fn offset(value: Option<i64>) -> String {
    value.map_or_else(|| "?".to_owned(), |value| value.to_string())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args_os().skip(1);
    let first = args
        .next()
        .ok_or("usage: inspect_stack_frame [--symbol NAME] FILE.o")?;
    let (symbol, object) = if first == "--symbol" {
        let symbol = args
            .next()
            .ok_or("--symbol requires a name")?
            .into_string()
            .map_err(|_| "invalid symbol")?;
        (symbol, args.next().ok_or("missing object")?)
    } else {
        (String::from("fixture"), first)
    };
    if args.next().is_some() {
        return Err("expected one original nondebug object".into());
    }
    let input = frontend::lift_elf(&std::fs::read(object)?, &symbol)?;
    let program = &input.program;
    let stack =
        StackAnalysis::try_analyze(program, Reg(x86::RSP)).ok_or("stack analysis unavailable")?;
    let reachable: BTreeSet<_> = program
        .cfg()
        .reachable_blocks()
        .into_iter()
        .flat_map(|id| program.cfg().block(id).instructions.clone())
        .collect();
    println!("FORMAT\tnirvana-stack-frame-v1");
    for (index, instruction) in program.instructions().iter().enumerate() {
        if reachable.contains(&index) {
            println!(
                "POINT\t{}\t{}\t{}",
                instruction.address,
                offset(stack.offset_before(instruction.address, 0, &Expr::Register(Reg(x86::RSP)))),
                offset(stack.offset_before(instruction.address, 0, &Expr::Register(Reg(x86::RBP))))
            );
        }
    }
    for access in stack.accesses() {
        println!(
            "ACCESS\t{}\t{}\t{}\t{}\t{}",
            access.instruction,
            access.assignment,
            access.offset,
            access.width.bytes(),
            if access.kind == AccessKind::Read {
                "read"
            } else {
                "write"
            }
        );
    }
    Ok(())
}
