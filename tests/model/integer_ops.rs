use nirvana::ir::{BinaryOp, Control, Expr, IrInstruction, Program, Reg};

fn program(op: BinaryOp) -> Program {
    Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(Expr::binary(
                op,
                Expr::Register(Reg(0)),
                Expr::Register(Reg(1)),
            )),
        }],
    )
    .unwrap()
}

#[test]
#[cfg(target_arch = "x86_64")]
fn signed_integer_operations_match_native_full_products_and_masked_shifts() {
    use std::arch::asm;
    let mut values = vec![
        0,
        1,
        2,
        31,
        32,
        63,
        64,
        65,
        255,
        u32::MAX as u64,
        1 << 32,
        (1 << 63) - 1,
        1 << 63,
        (1 << 63) + 1,
        u64::MAX - 1,
        u64::MAX,
    ];
    let mut seed = 0x8123_4567_89ab_cdefu64;
    for _ in 0..64 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        values.push(seed);
    }
    let multiply = program(BinaryOp::SMulHigh);
    let shift = program(BinaryOp::AShr);
    for &a in &values {
        for &b in &values {
            let high: u64;
            // RAX holds the low product; RDX receives the signed high word.
            unsafe {
                asm!("imul {b}", b=in(reg)b, inout("rax")a=>_, lateout("rdx")high);
            }
            assert_eq!(BinaryOp::SMulHigh.evaluate(a, b), high, "{a:#x} * {b:#x}");
            assert_eq!(multiply.execute(&[a, b], 1).unwrap().value, high);
        }
        for count in (0..=255u64).chain([u64::MAX, 1 << 63, (1 << 63) + 63]) {
            let mut actual = a;
            unsafe {
                asm!("sar rax,cl", inout("rax")actual, in("cl")count as u8);
            }
            assert_eq!(
                BinaryOp::AShr.evaluate(a, count),
                actual,
                "{a:#x} >> {count}"
            );
            assert_eq!(shift.execute(&[a, count], 1).unwrap().value, actual);
        }
    }
    println!(
        "{} native signed high products and {} native masked shifts",
        values.len() * values.len(),
        values.len() * 259
    );
}
