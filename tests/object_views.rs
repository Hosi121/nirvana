#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use native::{Scratch, link, object, run};
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use std::fmt::Write as _;

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn add(a: Expr, b: u64) -> Expr {
    Expr::binary(BinaryOp::Add, a, c(b))
}
fn slot() -> Expr {
    Expr::binary(BinaryOp::Sub, r(0), c(8))
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}

#[test]
fn spilled_input_pointer_fields_share_memory_with_stack_and_overlapping_fields() {
    let program = Program::new(
        0,
        6,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                store(slot(), Width::U64, r(1)),
                set(2, Expr::load(slot(), Width::U64)),
                set(3, Expr::load(add(r(2), 8), Width::U64)),
                store(add(r(2), 9), Width::U8, c(0xfe)),
                set(4, Expr::load(slot(), Width::U64)),
                set(5, Expr::load(add(r(2), 8), Width::U64)),
            ],
            control: Control::Return(Expr::binary(
                BinaryOp::Xor,
                r(4),
                Expr::binary(BinaryOp::Xor, r(3), r(5)),
            )),
        }],
    )
    .unwrap();
    let output = emit_readable_c_with_options(
        &program,
        ReadableOptions {
            stack_register: Some(Reg(0)),
            recover_objects: true,
        },
    )
    .unwrap();
    assert_eq!(output.object_views.len(), 1);
    let object_view = &output.object_views[0];
    assert_eq!(object_view.register, Reg(1));
    assert_eq!(
        object_view
            .fields
            .iter()
            .map(|f| f.offset)
            .collect::<Vec<_>>(),
        [8, 9]
    );
    assert_eq!(object_view.fields[0].overlaps, [1]);
    assert!(output.code.contains("object_0.field_8"));
    assert!(output.code.contains("object_0.field_9"));
    let scratch = Scratch::new();
    let arguments = output
        .parameters
        .iter()
        .map(|r| format!("r[{}]", r.0))
        .collect::<Vec<_>>()
        .join(", ");
    let harness = format!(
        r#"
#include <stdio.h>
#include <inttypes.h>
int main(void) {{
    uint64_t stack, pointer;
    while (scanf("%" SCNu64 " %" SCNu64, &stack, &pointer) == 2) {{
        uint8_t memory[32];
        for (unsigned i = 0; i < 32; ++i) memory[i] = (uint8_t)(i*7+3);
        uint64_t r[6] = {{stack,pointer,9,13,17,21}};
        uint64_t value = nirvana_readable({arguments}, memory, UINT64_C(4096), sizeof(memory));
        printf("%" PRIu64, value);
        for (unsigned i = 0; i < 4; ++i) {{
            uint64_t word = 0;
            for (unsigned j = 0; j < 8; ++j) word |= (uint64_t)memory[i*8+j] << (j*8);
            printf(" %" PRIu64, word);
        }}
        puts("");
    }}
}}
"#
    );
    let mut inputs = String::new();
    let mut expected = Vec::new();
    for stack in [0x1008, 0x1010, 0x1018, 0x1020] {
        for pointer in [0x1000, 0x1008, 0x1010] {
            writeln!(inputs, "{stack} {pointer}").unwrap();
            let memory: Vec<_> = (0..32).map(|i| (i * 7 + 3) as u8).collect();
            let execution = program
                .execute_with_memory(&[stack, pointer, 9, 13, 17, 21], 0x1000, &memory, 1)
                .unwrap();
            let mut result = vec![execution.value];
            result.extend(
                execution
                    .memory
                    .chunks_exact(8)
                    .map(|word| u64::from_le_bytes(word.try_into().unwrap())),
            );
            expected.push(result);
        }
    }
    for optimization in ["-O0", "-O2"] {
        let source = scratch.0.join(format!("objects{optimization}.c"));
        std::fs::write(&source, output.code.clone() + &harness).unwrap();
        let compiled = source.with_extension("o");
        let binary = source.with_extension("bin");
        object(&source, &compiled, optimization, "nirvana_readable");
        link(&[&compiled], &binary);
        assert_eq!(run(&binary, &inputs), expected);
    }
}

#[test]
fn differing_origins_at_a_merge_do_not_make_a_fictitious_field() {
    let program = Program::new(
        0,
        4,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Branch {
                    condition: r(3),
                    target: 3,
                },
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![set(2, r(0))],
                control: Control::Jump(4),
            },
            IrInstruction {
                address: 3,
                size: 1,
                assignments: vec![set(2, r(1))],
                control: Control::Next,
            },
            IrInstruction {
                address: 4,
                size: 1,
                assignments: vec![set(2, Expr::load(add(r(2), 8), Width::U64))],
                control: Control::Return(r(2)),
            },
        ],
    )
    .unwrap();
    let output = emit_readable_c_with_options(
        &program,
        ReadableOptions {
            stack_register: None,
            recover_objects: true,
        },
    )
    .unwrap();
    assert!(output.object_views.is_empty());
    assert!(output.code.contains("nirvana_load(&m,"));
}

#[test]
fn impure_address_summaries_do_not_declare_unusable_objects() {
    let program = Program::new(
        0,
        3,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![store(r(0), Width::U64, r(1)), set(2, load_twice(r(0)))],
            control: Control::Return(r(2)),
        }],
    )
    .unwrap();
    let output = emit_readable_c_with_options(
        &program,
        ReadableOptions {
            stack_register: None,
            recover_objects: true,
        },
    )
    .unwrap();
    // The outer load has a successful-value origin, but its address contains a
    // load and cannot be replaced. Only the actual pure store address is named.
    assert_eq!(output.object_views.len(), 1);
    assert_eq!(output.object_views[0].register, Reg(0));
}

fn load_twice(address: Expr) -> Expr {
    Expr::load(Expr::load(address, Width::U64), Width::U8)
}
