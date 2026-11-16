#[path = "support/native.rs"]
mod native;
use native::{Scratch, fixture_root, link, object, run};
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Program, Reg, Width};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use std::fmt::Write as _;

#[test]
fn narrowed_unsigned_locals_preserve_u64_products_above_int_and_u32_limits() {
    let r = |i| Expr::Register(Reg(i));
    let add = |a, b| Expr::binary(BinaryOp::Add, a, b);
    let mul = |a, b| Expr::binary(BinaryOp::Mul, a, b);
    let p = Program::new(
        0,
        4,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                Assignment {
                    destination: Reg(1).into(),
                    value: Expr::load(r(0), Width::U16),
                },
                Assignment {
                    destination: Reg(2).into(),
                    value: Expr::load(add(r(0), Expr::Const(2)), Width::U16),
                },
                Assignment {
                    destination: Reg(3).into(),
                    value: Expr::load(r(0), Width::U32),
                },
            ],
            control: Control::Return(add(mul(r(1), r(2)), mul(r(3), r(3)))),
        }],
    )
    .unwrap();
    let scratch = Scratch::new();
    let mut inputs = String::new();
    let mut expected = Vec::new();
    for a in [0, 1, 0x7fff, 0x8000, 0xffff, 0x1ffff, u64::MAX] {
        for b in [0, 1, 0x7fff, 0x8000, 0xffff, 0x1ffff, u64::MAX] {
            writeln!(inputs, "{a} {b} 17 19").unwrap();
            let mut memory = vec![0; 8];
            memory[..2].copy_from_slice(&(a as u16).to_le_bytes());
            memory[2..4].copy_from_slice(&(b as u16).to_le_bytes());
            let result = p
                .execute_with_memory(&[4096, 0, 0, 0], 4096, &memory, 1)
                .unwrap();
            expected.push(vec![result.value, a, b, 17, 19]);
        }
    }
    for views in [false, true] {
        let output = emit_readable_c_with_options(
            &p,
            ReadableOptions {
                stack_register: None,
                recover_objects: views,
            },
        )
        .unwrap();
        assert!(output.locals.iter().any(|v| v.width == Width::U16));
        assert!(output.locals.iter().any(|v| v.width == Width::U32));
        let args = output
            .parameters
            .iter()
            .map(|r| format!("machine[{}]", r.0))
            .collect::<Vec<_>>()
            .join(", ");
        let wrapper = format!(
            r#"
uint64_t fixture(uint64_t *state) {{
    uint8_t memory[8]={{0}};
    for(unsigned i=0;i<2;++i) {{ memory[i]=(uint8_t)(state[0]>>(i*8)); memory[i+2]=(uint8_t)(state[1]>>(i*8)); }}
    uint64_t machine[4]={{4096,0,0,0}};
    return nirvana_readable({args},memory,UINT64_C(4096),sizeof(memory));
}}
"#
        );
        for opt in ["-O0", "-O2"] {
            let source = scratch.0.join(format!("types{views}{opt}.c"));
            std::fs::write(&source, output.code.clone() + &wrapper).unwrap();
            let compiled = source.with_extension("o");
            let harness = scratch.0.join(format!("harness{views}{opt}.o"));
            let binary = source.with_extension("bin");
            object(&source, &compiled, opt, "fixture");
            object(&fixture_root().join("harness.c"), &harness, opt, "fixture");
            link(&[&compiled, &harness], &binary);
            assert_eq!(run(&binary, &inputs), expected, "{views} {opt}");
        }
    }
}
