use crate::support::native;
use native::{Scratch, link, object, run_fields};
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use std::fmt::Write as _;

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: BinaryOp, a: Expr, b: Expr) -> Expr {
    Expr::binary(op, a, b)
}
fn address(stride: u64, offset: u64) -> Expr {
    b(
        BinaryOp::Add,
        b(
            BinaryOp::Add,
            r(0),
            b(BinaryOp::Mul, b(BinaryOp::And, r(1), c(3)), c(stride)),
        ),
        c(offset),
    )
}

#[test]
fn indexed_views_use_current_indices_and_entry_bases_across_register_changes() {
    let p = Program::new(
        0,
        4,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Reg(2).into(),
                        value: Expr::load(address(8, 2), Width::U32),
                    },
                    Assignment {
                        destination: Place::Memory {
                            address: address(8, 3),
                            width: Width::U8,
                        },
                        value: b(BinaryOp::Xor, r(2), c(171)),
                    },
                    Assignment {
                        destination: Reg(0).into(),
                        value: b(BinaryOp::Add, r(0), c(8)),
                    },
                ],
                control: Control::Jump(1),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Reg(1).into(),
                        value: b(BinaryOp::Add, r(1), c(1)),
                    },
                    Assignment {
                        destination: Reg(3).into(),
                        value: Expr::load(address(8, 2), Width::U32),
                    },
                ],
                control: Control::Return(b(BinaryOp::Xor, r(2), r(3))),
            },
        ],
    )
    .unwrap();
    check(&p, &[0x1000, 0x1008]);
}

#[test]
fn indexed_views_preserve_non_power_of_two_strides_and_negative_wrapping_offsets() {
    let p = Program::new(
        0,
        4,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                Assignment {
                    destination: Reg(2).into(),
                    value: Expr::load(address(3, u64::MAX - 7), Width::U32),
                },
                Assignment {
                    destination: Place::Memory {
                        address: address(3, u64::MAX - 6),
                        width: Width::U8,
                    },
                    value: b(BinaryOp::Xor, r(2), c(171)),
                },
            ],
            control: Control::Return(r(2)),
        }],
    )
    .unwrap();
    check(&p, &[0x1008, 0x1010]);
}

#[test]
fn materialized_index_addresses_capture_the_index_before_a_cfg_edge_update() {
    let p = Program::new(
        0,
        5,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Reg(2).into(),
                        value: address(8, 0),
                    },
                    Assignment {
                        destination: Reg(1).into(),
                        value: b(BinaryOp::Add, r(1), c(1)),
                    },
                ],
                control: Control::Jump(1),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Reg(3).into(),
                        value: Expr::load(r(2), Width::U32),
                    },
                    Assignment {
                        destination: Place::Memory {
                            address: b(BinaryOp::Add, r(2), c(1)),
                            width: Width::U8,
                        },
                        value: b(BinaryOp::Xor, r(3), c(171)),
                    },
                    Assignment {
                        destination: Reg(4).into(),
                        value: Expr::load(r(2), Width::U32),
                    },
                ],
                control: Control::Return(b(BinaryOp::Add, b(BinaryOp::Xor, r(3), r(4)), r(1))),
            },
        ],
    )
    .unwrap();
    let output = emit_readable_c_with_options(
        &p,
        ReadableOptions {
            stack_register: None,
            recover_objects: true,
            coalesce_locals: true,
            compact_memory: false,
        },
    )
    .unwrap();
    assert!(
        output
            .object_views
            .iter()
            .flat_map(|o| &o.indexed)
            .any(|i| i.address_sites > 0)
    );
    check(&p, &[0x1000, 0x1008]);
}

fn check(program: &Program, bases: &[u64]) {
    for compact_memory in [false, true] {
        let output = emit_readable_c_with_options(
            program,
            ReadableOptions {
                stack_register: None,
                recover_objects: true,
                coalesce_locals: true,
                compact_memory,
            },
        )
        .unwrap();
        assert!(!output.object_views.is_empty());
        assert!(output.object_views.iter().any(|o| !o.indexed.is_empty()));
        assert!(output.code.contains(if compact_memory {
            "element("
        } else {
            "nirvana_view_index(object_0.base"
        }));
        let args = output
            .parameters
            .iter()
            .map(|r| format!("r[{}]", r.0))
            .collect::<Vec<_>>()
            .join(", ");
        let register_count = program.register_count();
        let harness = format!(
            r#"
#include <stdio.h>
#include <inttypes.h>
int main(void) {{
    uint64_t base,index;
    while(scanf("%" SCNu64 " %" SCNu64,&base,&index)==2) {{
        uint8_t memory[64];
        for(unsigned i=0;i<64;++i) memory[i]=(uint8_t)(i*17+5);
        uint64_t r[{register_count}]={{base,index,13,17}};
        uint64_t value=nirvana_readable({args},memory,UINT64_C(4096),sizeof(memory));
        printf("%" PRIu64,value);
        for(unsigned i=0;i<8;++i) {{uint64_t word=0;for(unsigned j=0;j<8;++j) word|=(uint64_t)memory[i*8+j]<<(j*8);printf(" %" PRIu64,word);}}
        puts("");
    }}
}}
"#
        );
        let scratch = Scratch::new();
        let mut inputs = String::new();
        let mut expected = Vec::new();
        for &base in bases {
            for index in [0, 1, 2, 3, 4, 63, u64::MAX] {
                writeln!(inputs, "{base} {index}").unwrap();
                let memory: Vec<u8> = (0..64).map(|i| (i * 17 + 5) as u8).collect();
                let mut registers = vec![0; program.register_count()];
                registers[..4].copy_from_slice(&[base, index, 13, 17]);
                let result = program
                    .execute_with_memory(&registers, 4096, &memory, 2)
                    .unwrap();
                let mut row = vec![result.value];
                row.extend(
                    result
                        .memory
                        .chunks_exact(8)
                        .map(|w| u64::from_le_bytes(w.try_into().unwrap())),
                );
                expected.push(row);
            }
        }
        for opt in ["-O0", "-O2"] {
            let source = scratch.0.join(format!("index{opt}.c"));
            std::fs::write(&source, output.code.clone() + &harness).unwrap();
            let compiled = source.with_extension("o");
            let binary = source.with_extension("bin");
            object(&source, &compiled, opt, "nirvana_readable");
            link(&[&compiled], &binary);
            assert_eq!(run_fields(&binary, &inputs, 9), expected);
        }
    }
}
