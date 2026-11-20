//! Function-scope declaration/initializer placement, checked by native strict C.
#[allow(dead_code)]
#[path = "support/checked_c.rs"]
mod checked_c;
#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus,
    Width,
};
use nirvana::readable::{ReadableC, ReadableOptions, emit_readable_c_with_options};
use std::fmt::Write as _;
use std::path::PathBuf;

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn b(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn load(address: Expr, width: Width) -> Expr {
    Expr::load(address, width)
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn instruction(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}

fn directory(label: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/declaration-backend-tests")
        .join(format!("{label}-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&path).unwrap();
    path
}
fn body(output: &ReadableC) -> &str {
    output
        .code
        .split_once("uint64_t nirvana_readable(")
        .unwrap()
        .1
}
fn bare(output: &ReadableC, local: &nirvana::readable::LocalValue) -> usize {
    let ty = local.address_width.map_or_else(
        || format!("uint{}_t", local.width.bits()),
        |w| format!("nirvana_u{}_address", w.bits()),
    );
    body(output)
        .matches(&format!("{ty} {};", local.name))
        .count()
}
fn initialized(output: &ReadableC, local: &nirvana::readable::LocalValue) -> usize {
    let ty = local.address_width.map_or_else(
        || format!("uint{}_t", local.width.bits()),
        |w| format!("nirvana_u{}_address", w.bits()),
    );
    body(output)
        .matches(&format!("{ty} {} = ", local.name))
        .count()
}

fn compare(program: &Program, inputs: &[[u64; 2]], label: &str) -> Vec<ReadableC> {
    let directory = directory(label);
    let original = program.instructions().to_vec();
    let mut text = String::new();
    let mut expected = Vec::new();
    for input in inputs {
        writeln!(text, "{} {}", input[0], input[1]).unwrap();
        let mut registers = vec![0; program.register_count()];
        registers[..2].copy_from_slice(input);
        for (index, value) in registers.iter_mut().enumerate().skip(2) {
            *value = 0x0123_4567_89ab_cdefu64.wrapping_mul(index as u64 + 1);
        }
        let report = program
            .run_with_memory(&registers, 4096, &(1..=16).collect::<Vec<u8>>(), 1000)
            .unwrap();
        let (fault, address, access, width, value) = match report.status {
            RunStatus::Fault(f) => (
                1,
                f.address,
                if f.access == AccessKind::Read { 1 } else { 2 },
                f.width.bytes() as u64,
                0,
            ),
            RunStatus::Returned(value) => (0, 0, 0, 0, value),
            RunStatus::Suspended => panic!("{label}: bounded case suspended"),
        };
        let words: Vec<_> = report
            .state
            .memory
            .chunks_exact(8)
            .map(|bytes| u64::from_le_bytes(bytes.try_into().unwrap()))
            .collect();
        expected.push(vec![
            fault, address, access, width, words[0], words[1], value,
        ]);
    }
    std::fs::write(directory.join("inputs.txt"), &text).unwrap();
    let mut outputs = Vec::new();
    for (coalesce_locals, recover_objects, compact_memory) in [
        (false, false, false),
        (true, false, false),
        (true, true, false),
        (true, true, true),
    ] {
        let output = emit_readable_c_with_options(
            program,
            ReadableOptions {
                stack_register: None,
                recover_objects,
                coalesce_locals,
                compact_memory,
            },
        )
        .unwrap();
        // Every local has exactly one C declaration. Alias writes reuse it.
        for local in &output.locals {
            assert_eq!(
                bare(&output, local) + initialized(&output, local),
                1,
                "{label}: {}\n{}",
                local.name,
                output.code
            );
        }
        let mut args: Vec<_> = output
            .parameters
            .iter()
            .map(|reg| format!("r[{}]", reg.0))
            .collect();
        args.extend(["memory", "UINT64_C(4096)", "sizeof(memory)"].map(String::from));
        let args = args.join(", ");
        let register_count = program.register_count();
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
    while(scanf("%" SCNu64 " %" SCNu64,&a,&b)==2) {{
        for(unsigned i=0;i<16;++i) memory[i]=(uint8_t)(i+1);
        result=0;fault=0;nirvana_test_address=0;nirvana_test_access=0;nirvana_test_width=0;
        uint64_t r[{register_count}]={{a,b}};
        for(unsigned i=2;i<{register_count};++i) r[i]=UINT64_C(81985529216486895)*(i+1);
        (void)r;
        if(setjmp(jump)==0) result=nirvana_readable({args}); else fault=1;
        uint64_t words[2]={{0,0}};
        for(unsigned i=0;i<16;++i) words[i/8]|=(uint64_t)memory[i]<<((i%8)*8);
        printf("%u %" PRIu64 " %u %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
          fault,fault?nirvana_test_address:UINT64_C(0),fault?nirvana_test_access:0,
          fault?nirvana_test_width:UINT64_C(0),words[0],words[1],result);
    }}
}}
"#
        );
        for optimization in ["-O0", "-O2"] {
            let source = directory.join(format!(
                "c{coalesce_locals}-v{recover_objects}-m{compact_memory}{optimization}.c"
            ));
            std::fs::write(&source, checked_c::instrument(&output.code) + &harness).unwrap();
            let object = source.with_extension("o");
            let binary = source.with_extension("bin");
            native::object(&source, &object, optimization, "nirvana_readable");
            native::link(&[&object], &binary);
            assert_eq!(
                native::run_fields(&binary, &text, 7),
                expected,
                "{label} coalesce={coalesce_locals} views={recover_objects} compact={compact_memory} {optimization}"
            );
        }
        outputs.push(output);
    }
    assert_eq!(program.instructions(), original);
    outputs
}

#[test]
fn prefix_initializer_survives_diamond_while_branch_definitions_stay_in_prolog() {
    let program = Program::new(
        0,
        4,
        vec![
            instruction(
                0,
                vec![
                    set(2, load(r(0), Width::U16)),
                    store(c(0x100f), Width::U8, r(2)),
                ],
                Control::Branch {
                    condition: r(1),
                    target: 3,
                },
            ),
            instruction(
                1,
                vec![
                    set(3, load(c(0x1008), Width::U32)),
                    store(c(0x1004), Width::U32, r(3)),
                ],
                Control::Jump(4),
            ),
            instruction(
                3,
                vec![
                    set(3, b(BinaryOp::Add, r(2), c(1))),
                    store(c(0x1000), Width::U16, r(3)),
                ],
                Control::Jump(4),
            ),
            instruction(
                4,
                vec![store(c(0x1008), Width::U32, r(3))],
                Control::Return(b(BinaryOp::Add, r(2), r(3))),
            ),
        ],
    )
    .unwrap();
    let inputs: Vec<_> = [0x1000, 0x1008, 0x100f, 0xffff]
        .into_iter()
        .flat_map(|address| {
            [0, 1, u64::MAX]
                .into_iter()
                .map(move |condition| [address, condition])
        })
        .collect();
    for output in compare(&program, &inputs, "diamond") {
        assert!(
            output
                .locals
                .iter()
                .any(|local| initialized(&output, local) == 1),
            "{}",
            output.code
        );
        assert!(
            output.locals.iter().any(|local| bare(&output, local) == 1),
            "{}",
            output.code
        );
    }
}

#[test]
fn initialized_locals_remain_in_function_scope_for_zero_trip_loops() {
    let program = Program::new(
        0,
        4,
        vec![
            instruction(
                0,
                vec![set(2, load(r(0), Width::U16)), set(3, c(0))],
                Control::Next,
            ),
            instruction(
                1,
                vec![],
                Control::Branch {
                    condition: b(BinaryOp::Ule, b(BinaryOp::And, r(1), c(3)), r(3)),
                    target: 4,
                },
            ),
            instruction(
                2,
                vec![
                    store(c(0x1008), Width::U8, r(2)),
                    set(2, b(BinaryOp::Add, r(2), c(1))),
                    set(3, b(BinaryOp::Add, r(3), c(1))),
                ],
                Control::Jump(1),
            ),
            instruction(4, vec![], Control::Return(b(BinaryOp::Add, r(2), r(3)))),
        ],
    )
    .unwrap();
    let inputs: Vec<_> = [0x1000, 0x1008, 0x100f, 0xffff]
        .into_iter()
        .flat_map(|address| {
            [0, 1, 2, 3, u64::MAX]
                .into_iter()
                .map(move |count| [address, count])
        })
        .collect();
    for output in compare(&program, &inputs, "zero-loop") {
        assert!(
            output
                .locals
                .iter()
                .any(|local| initialized(&output, local) == 1),
            "{}",
            output.code
        );
    }
}

#[test]
fn aliased_storage_has_one_declaration_and_later_assignments_reuse_it() {
    let program = Program::new(
        0,
        4,
        vec![
            instruction(
                0,
                vec![
                    set(2, load(r(0), Width::U16)),
                    store(c(0x100e), Width::U8, r(2)),
                    store(c(0x100f), Width::U8, b(BinaryOp::Shr, r(2), c(8))),
                ],
                Control::Jump(1),
            ),
            instruction(
                1,
                vec![
                    set(3, load(r(1), Width::U16)),
                    store(c(0x1008), Width::U16, r(3)),
                ],
                Control::Return(r(3)),
            ),
        ],
    )
    .unwrap();
    let inputs: Vec<_> = [0x1000, 0x1008, 0x100e, 0x100f, 0xffff]
        .into_iter()
        .flat_map(|a| {
            [0x1000, 0x1008, 0x100e, 0x100f, 0xffff]
                .into_iter()
                .map(move |b| [a, b])
        })
        .collect();
    let outputs = compare(&program, &inputs, "aliases");
    assert!(
        outputs
            .iter()
            .skip(1)
            .any(|output| output.locals.iter().any(|local| local.registers.len() > 1)),
        "case must exercise a reused storage name"
    );
}

#[test]
fn nested_and_multiple_load_initializers_keep_prolog_scope_and_exact_faults() {
    let program = Program::new(
        0,
        4,
        vec![
            instruction(
                0,
                vec![
                    store(c(0x1000), Width::U64, c(0x1008)),
                    store(c(0x100f), Width::U8, c(0x5a)),
                    set(2, load(load(r(0), Width::U64), Width::U16)),
                    store(c(0x1004), Width::U16, r(2)),
                    set(
                        3,
                        b(
                            BinaryOp::Add,
                            load(r(0), Width::U64),
                            load(r(1), Width::U64),
                        ),
                    ),
                ],
                Control::Jump(1),
            ),
            instruction(
                1,
                vec![store(c(0x1008), Width::U64, r(3))],
                Control::Return(b(BinaryOp::Xor, r(2), r(3))),
            ),
        ],
    )
    .unwrap();
    let inputs: Vec<_> = [0x1000, 0x1008, 0x100f, 0xffff]
        .into_iter()
        .flat_map(|a| {
            [0x1000, 0x1008, 0x100f, 0xffff]
                .into_iter()
                .map(move |b| [a, b])
        })
        .collect();
    for output in compare(&program, &inputs, "nested-loads") {
        assert!(
            output.locals.iter().any(|local| bare(&output, local) == 1),
            "{}",
            output.code
        );
    }
}

#[test]
fn reads_of_original_input_registers_do_not_redeclare_parameters_as_locals() {
    let program = Program::new(
        0,
        3,
        vec![
            instruction(
                0,
                vec![
                    store(c(0x1000), Width::U64, r(2)),
                    set(2, load(r(0), Width::U16)),
                    store(c(0x1008), Width::U16, r(2)),
                ],
                Control::Jump(1),
            ),
            instruction(1, vec![], Control::Return(b(BinaryOp::Add, r(2), r(1)))),
        ],
    )
    .unwrap();
    let inputs: Vec<_> = [0x1000, 0x1008, 0x100f, 0xffff]
        .into_iter()
        .flat_map(|address| {
            [0, 0xffff, u64::MAX]
                .into_iter()
                .map(move |value| [address, value])
        })
        .collect();
    for output in compare(&program, &inputs, "input-reads") {
        assert!(output.parameters.contains(&Reg(2)));
        for index in 0..output.parameters.len() {
            assert!(!body(&output).contains(&format!("uint64_t arg{index} = ")));
        }
    }
}

#[test]
fn irreducible_goto_fallback_keeps_every_local_in_the_prolog() {
    let increment = || set(2, b(BinaryOp::Add, r(2), c(1)));
    let program = Program::new(
        0,
        3,
        vec![
            instruction(
                0,
                vec![set(2, c(0)), store(c(0x1000), Width::U8, c(2))],
                Control::Branch {
                    condition: b(BinaryOp::Eq, load(r(0), Width::U8), load(r(1), Width::U8)),
                    target: 2,
                },
            ),
            instruction(
                1,
                vec![increment()],
                Control::Branch {
                    condition: b(BinaryOp::Ule, c(3), r(2)),
                    target: 3,
                },
            ),
            instruction(
                2,
                vec![increment()],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(2), c(3)),
                    target: 1,
                },
            ),
            // A second independent cycle keeps this a genuine fallback case:
            // the optional proposal splits at most one incoming edge.
            instruction(
                3,
                vec![set(2, c(0))],
                Control::Branch {
                    condition: r(0),
                    target: 5,
                },
            ),
            instruction(4, vec![increment()], Control::Jump(5)),
            instruction(
                5,
                vec![increment()],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(2), c(3)),
                    target: 4,
                },
            ),
            instruction(6, vec![], Control::Return(r(2))),
        ],
    )
    .unwrap();
    let inputs: Vec<_> = [0x1000, 0x1008, 0x100f, 0xffff]
        .into_iter()
        .flat_map(|a| {
            [0x1000, 0x1008, 0x100f, 0xffff]
                .into_iter()
                .map(move |b| [a, b])
        })
        .collect();
    for output in compare(&program, &inputs, "gotos") {
        assert!(output.fallback_reason.is_some());
        for local in &output.locals {
            assert_eq!(bare(&output, local), 1);
            assert_eq!(initialized(&output, local), 0);
        }
    }
}

#[test]
fn materialized_address_views_receive_a_typed_initializer_before_index_changes() {
    let address = b(
        BinaryOp::Add,
        r(0),
        b(BinaryOp::Mul, b(BinaryOp::And, r(1), c(3)), c(4)),
    );
    let program = Program::new(
        0,
        5,
        vec![
            instruction(
                0,
                vec![set(2, address), set(1, b(BinaryOp::Add, r(1), c(1)))],
                Control::Jump(1),
            ),
            instruction(
                1,
                vec![
                    set(3, load(r(2), Width::U32)),
                    store(
                        b(BinaryOp::Add, r(2), c(1)),
                        Width::U8,
                        b(BinaryOp::Xor, r(3), c(171)),
                    ),
                    set(4, load(r(2), Width::U32)),
                ],
                Control::Return(b(BinaryOp::Add, b(BinaryOp::Xor, r(3), r(4)), r(1))),
            ),
        ],
    )
    .unwrap();
    let inputs: Vec<_> = [0x1000, 0x1008, 0xffff]
        .into_iter()
        .flat_map(|base| {
            [0, 1, 2, 3, 4, 63, u64::MAX]
                .into_iter()
                .map(move |index| [base, index])
        })
        .collect();
    for output in compare(&program, &inputs, "address-views").iter().skip(2) {
        assert!(
            output
                .object_views
                .iter()
                .flat_map(|object| &object.indexed)
                .any(|view| view.address_sites > 0)
        );
        assert!(
            body(output)
                .lines()
                .any(|line| line.trim_start().starts_with("uint64_t ")
                    && line.contains(" = ")
                    && (line.contains("element(") || line.contains("nirvana_view_index("))),
            "{}",
            output.code
        );
    }
}
