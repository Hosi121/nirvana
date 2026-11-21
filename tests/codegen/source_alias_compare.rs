use crate::support::native;

use nirvana::ir::{
    Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus, Width,
};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use std::fmt::Write as _;
use std::path::Path;
use std::process::Command;

use crate::support::ir::r;

fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}

fn instruction(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}

// Explicit jumps keep store, reload, copy, and comparison in separate blocks:
// block-local substitution must not make this a same-Reg comparison first.
fn program(op: BinaryOp, arithmetic_operands: bool) -> Program {
    let cell = binary(BinaryOp::Sub, r(0), Expr::Const(8));
    let operand = |index| {
        if arithmetic_operands {
            binary(BinaryOp::Add, r(index), Expr::Const(1))
        } else {
            r(index)
        }
    };
    Program::new(
        0,
        4,
        vec![
            instruction(
                0,
                vec![Assignment {
                    destination: Place::Memory {
                        address: cell.clone(),
                        width: Width::U64,
                    },
                    value: r(1),
                }],
                Control::Jump(1),
            ),
            instruction(
                1,
                vec![Assignment {
                    destination: Reg(2).into(),
                    value: Expr::load(cell, Width::U64),
                }],
                Control::Jump(2),
            ),
            instruction(
                2,
                vec![Assignment {
                    destination: Reg(3).into(),
                    value: r(2),
                }],
                Control::Jump(3),
            ),
            instruction(
                3,
                vec![],
                Control::Branch {
                    condition: binary(op, operand(2), operand(3)),
                    target: 5,
                },
            ),
            instruction(4, vec![], Control::Return(Expr::Const(0))),
            instruction(5, vec![], Control::Return(Expr::Const(1))),
        ],
    )
    .unwrap()
}

fn instrument(code: &str, args: &str) -> String {
    let code = code.replace(
        "static inline uint64_t nirvana_offset(struct nirvana_memory *m, uint64_t address, uint64_t width) {",
        "static inline uint64_t nirvana_offset(struct nirvana_memory *m, uint64_t address, uint64_t width) { nirvana_test_address=address; nirvana_test_width=width;",
    );
    let prefix = "#include <stdint.h>\n#include <setjmp.h>\nstatic uint64_t nirvana_test_address;\nstatic uint64_t nirvana_test_width;\n_Noreturn void nirvana_test_abort(void);\n#define abort nirvana_test_abort\n";
    let harness = format!(
        r#"
#undef abort
#include <stdio.h>
#include <inttypes.h>
static jmp_buf jump;
static uint8_t memory[16];
static uint64_t result;
static unsigned fault;
_Noreturn void nirvana_test_abort(void) {{longjmp(jump,1);}}
int main(void) {{
    uint64_t a,b;
    while (scanf("%" SCNu64 " %" SCNu64,&a,&b)==2) {{
        for(unsigned i=0;i<16;++i) memory[i]=(uint8_t)(i+1);
        result=0;fault=0;
        uint64_t r[4]={{a,b}};
        (void)r;
        if(setjmp(jump)==0) result=nirvana_readable({args});
        else fault=1;
        uint64_t words[2]={{0,0}};
        for(unsigned i=0;i<16;++i) words[i/8]|=(uint64_t)memory[i]<<((i%8)*8);
        printf("%u %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",fault,fault?nirvana_test_address:UINT64_C(0),fault?nirvana_test_width:UINT64_C(0),words[0],words[1],result);
    }}
}}
"#
    );
    prefix.to_owned() + &code + &harness
}

fn compile(source: &Path, object: &Path, optimization: &str) -> std::process::Output {
    native::compile_output(
        Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                "-fno-lto",
                optimization,
                "-c",
            ])
            .arg(source)
            .arg("-o")
            .arg(object),
    )
}

#[test]
fn copied_stack_values_compare_without_strict_c_warnings_and_keep_guest_behavior() {
    // Keep the C and diagnostics available when a compilation assertion fails.
    let artifacts = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join(format!("source-alias-compare-{}", std::process::id()));
    std::fs::create_dir_all(&artifacts).unwrap();
    let inputs: Vec<_> = [0x1008, 0x1010, 0x1007, 0x1011, 0, u64::MAX]
        .into_iter()
        .flat_map(|stack| {
            [0, 1, 255, 1 << 63, u64::MAX]
                .into_iter()
                .map(move |value| [stack, value])
        })
        .collect();
    let mut failures = Vec::new();
    let mut compilations = 0;
    let mut executions = 0;
    for (name, op) in [
        ("eq", BinaryOp::Eq),
        ("ne", BinaryOp::Ne),
        ("ult", BinaryOp::Ult),
        ("ule", BinaryOp::Ule),
    ] {
        for (arithmetic, coalesce) in [(false, false), (true, false), (false, true), (true, true)] {
            let program = program(op, arithmetic);
            let output = emit_readable_c_with_options(
                &program,
                ReadableOptions {
                    stack_register: Some(Reg(0)),
                    recover_objects: true,
                    coalesce_locals: coalesce,
                    compact_memory: true,
                },
            )
            .unwrap();
            let case = format!(
                "{name}-{}-{}",
                if arithmetic { "add" } else { "bare" },
                if coalesce { "coalesced" } else { "separate" }
            );
            std::fs::write(artifacts.join(format!("{case}-emitted.c")), &output.code).unwrap();
            std::fs::write(
                artifacts.join(format!("{case}-locals.txt")),
                format!("{:?}\n{:?}\n", output.locals, output.local_plan),
            )
            .unwrap();
            let mut args: Vec<_> = output
                .parameters
                .iter()
                .map(|reg| format!("r[{}]", reg.0))
                .collect();
            args.extend(["memory", "UINT64_C(4096)", "sizeof(memory)"].map(String::from));
            let source_text = instrument(&output.code, &args.join(", "));
            let mut input_text = String::new();
            let expected: Vec<_> = inputs
                .iter()
                .map(|input| {
                    writeln!(input_text, "{} {}", input[0], input[1]).unwrap();
                    let report = program
                        .run_with_memory(
                            &[input[0], input[1], 0, 0],
                            0x1000,
                            &(1..=16).collect::<Vec<u8>>(),
                            1000,
                        )
                        .unwrap();
                    let (fault, address, width, value) = match report.status {
                        RunStatus::Fault(f) => (1, f.address, f.width.bytes() as u64, 0),
                        RunStatus::Returned(value) => (0, 0, 0, value),
                        RunStatus::Suspended => panic!("finite probe unexpectedly suspended"),
                    };
                    let words: Vec<_> = report
                        .state
                        .memory
                        .chunks_exact(8)
                        .map(|bytes| u64::from_le_bytes(bytes.try_into().unwrap()))
                        .collect();
                    vec![fault, address, width, words[0], words[1], value]
                })
                .collect();
            for optimization in ["-O0", "-O2"] {
                let source = artifacts.join(format!("{case}{optimization}.c"));
                let object = source.with_extension("o");
                let binary = source.with_extension("bin");
                std::fs::write(&source, &source_text).unwrap();
                let compilation = compile(&source, &object, optimization);
                compilations += 1;
                std::fs::write(source.with_extension("stderr"), &compilation.stderr).unwrap();
                if !compilation.status.success() {
                    failures.push(format!(
                        "{case} {optimization}: {}",
                        String::from_utf8_lossy(&compilation.stderr)
                    ));
                    continue;
                }
                native::link(&[&object], &binary);
                assert_eq!(
                    native::run_fields(&binary, &input_text, 6),
                    expected,
                    "{case} {optimization}"
                );
                executions += inputs.len();
            }
        }
    }
    eprintln!(
        "source-alias probe: {compilations} compilations, {executions} full-memory/fault executions; artifacts {}",
        artifacts.display()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
