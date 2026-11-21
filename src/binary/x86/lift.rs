use std::fmt;

use super::decode::{
    Addressing, Alu, DecodeError, DecodedInstruction, Operand, Operation, Register, Rotate, Shift,
    Unary, decode_reachable,
};
use super::{CF, OF, PF, RAX, RBP, RDX, REGISTER_COUNT, RSP, SF, ZF};
use crate::control_flow::cfg::{BuildError, Cfg};
use crate::model::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, ProgramError, Reg,
    Width,
};

const A: usize = 21;
const V: usize = 22;
const C: usize = 23;
const RESULT: usize = 24;
const ADDRESS: usize = 25;
const PARITY: usize = 26;
const LOW: usize = 27;
const HIGH: usize = 28;
const F_CF: u8 = 1;
const F_ZF: u8 = 2;
const F_SF: u8 = 4;
const F_OF: u8 = 8;
const F_PF: u8 = 16;
const ALL: u8 = 31;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LiftError {
    Decode(DecodeError),
    Layout(BuildError),
    Program(ProgramError),
    UndefinedFlags { address: u64, mask: u8 },
}

impl fmt::Display for LiftError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Decode(error) => error.fmt(f),
            Self::Layout(error) => error.fmt(f),
            Self::Program(error) => error.fmt(f),
            Self::UndefinedFlags { address, mask } => write!(
                f,
                "x86 lift at {address:#x}: condition reads unavailable flags (CF/ZF/SF/OF/PF mask {mask:#x})"
            ),
        }
    }
}
impl std::error::Error for LiftError {}

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn k(value: u64) -> Expr {
    Expr::Const(value)
}
fn b(op: B, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn and(left: Expr, right: Expr) -> Expr {
    b(B::And, left, right)
}
fn or(left: Expr, right: Expr) -> Expr {
    b(B::Or, left, right)
}
fn xor(left: Expr, right: Expr) -> Expr {
    b(B::Xor, left, right)
}
fn add(left: Expr, right: Expr) -> Expr {
    b(B::Add, left, right)
}
fn sub(left: Expr, right: Expr) -> Expr {
    b(B::Sub, left, right)
}
fn eq(left: Expr, right: Expr) -> Expr {
    b(B::Eq, left, right)
}
fn ne(left: Expr, right: Expr) -> Expr {
    b(B::Ne, left, right)
}
fn bit(value: Expr, shift: u32) -> Expr {
    and(b(B::Shr, value, k(u64::from(shift))), k(1))
}
fn mask(value: Expr, width: Width) -> Expr {
    if width == Width::U64 {
        value
    } else {
        and(value, k(width.mask()))
    }
}
fn sext(value: Expr, width: Width) -> Expr {
    if width == Width::U64 {
        value
    } else {
        let sign = k(1 << (width.bits() - 1));
        sub(xor(mask(value, width), sign.clone()), sign)
    }
}

fn condition(code: u8) -> Expr {
    let positive = match code >> 1 {
        0 => r(OF),
        1 => r(CF),
        2 => r(ZF),
        3 => or(r(CF), r(ZF)),
        4 => r(SF),
        5 => r(PF),
        6 => xor(r(SF), r(OF)),
        7 => or(r(ZF), xor(r(SF), r(OF))),
        _ => unreachable!(),
    };
    if code & 1 == 0 {
        positive
    } else {
        xor(positive, k(1))
    }
}

fn condition_flags(code: u8) -> u8 {
    [
        F_OF,
        F_CF,
        F_ZF,
        F_CF | F_ZF,
        F_SF,
        F_PF,
        F_SF | F_OF,
        F_ZF | F_SF | F_OF,
    ][(code >> 1) as usize]
}

// (flags read, definitely defined, undefined). Entry flags are unavailable;
// preserving an unknown flag does not make it defined. Undefined flags from
// IMUL and variable shifts must never silently become branch inputs.
fn flag_effect(operation: Operation) -> (u8, u8, u8) {
    match operation {
        Operation::Branch { condition, .. }
        | Operation::Set { condition, .. }
        | Operation::Cmov { condition, .. } => (condition_flags(condition), 0, 0),
        Operation::Alu { kind, .. } => (
            if matches!(kind, Alu::Adc | Alu::Sbb) {
                F_CF
            } else {
                0
            },
            ALL,
            0,
        ),
        Operation::Unary {
            kind: Unary::Inc | Unary::Dec,
            ..
        } => (0, ALL & !F_CF, 0),
        Operation::Unary {
            kind: Unary::Neg, ..
        } => (0, ALL, 0),
        Operation::Imul { .. } | Operation::Mul { .. } => (0, F_CF | F_OF, F_ZF | F_SF | F_PF),
        Operation::Divide { .. } => (0, 0, ALL),
        // BT defines CF, preserves ZF, and leaves OF/SF/PF undefined.
        Operation::BitTest { .. } => (0, F_CF, F_OF | F_SF | F_PF),
        Operation::Rotate {
            destination, count, ..
        } => {
            let width = destination.width().unwrap();
            match count {
                Operand::Immediate(value) => {
                    // Flags use the masked count BEFORE modulo operand width.
                    let count = value & if width == Width::U64 { 63 } else { 31 };
                    match count {
                        0 => (0, 0, 0),
                        1 => (0, F_CF | F_OF, 0),
                        _ => (0, F_CF, F_OF),
                    }
                }
                // A variable zero count can preserve an unavailable CF. Keep
                // prior CF availability; all nonzero counts define it. OF may
                // be undefined, so reject its later use conservatively.
                _ => (0, 0, F_OF),
            }
        }
        Operation::Shift {
            destination, count, ..
        } => {
            let width = destination.width().unwrap();
            match count {
                Operand::Immediate(value) => {
                    let count = value & if width == Width::U64 { 63 } else { 31 };
                    if count == 0 {
                        (0, 0, 0)
                    } else {
                        (
                            0,
                            F_ZF | F_SF
                                | F_PF
                                | if count < u64::from(width.bits()) {
                                    F_CF
                                } else {
                                    0
                                }
                                | if count == 1 { F_OF } else { 0 },
                            if count >= u64::from(width.bits()) {
                                F_CF
                            } else {
                                0
                            } | if count != 1 { F_OF } else { 0 },
                        )
                    }
                }
                _ => (0, 0, F_CF | F_OF),
            }
        }
        Operation::DoubleShift {
            destination, count, ..
        } => {
            let width = destination.width().unwrap();
            let count = u64::from(count) & if width == Width::U64 { 63 } else { 31 };
            match count {
                0 => (0, 0, 0),
                1 => (0, ALL, 0),
                _ => (0, ALL & !F_OF, F_OF),
            }
        }
        _ => (0, 0, 0),
    }
}

fn check_flags(cfg: &Cfg, decoded: &[DecodedInstruction]) -> Result<(), LiftError> {
    check_flags_with_calls(cfg, decoded, false)
}

// The effect environment supplies all five modeled flag values explicitly.
// Legacy decoding/lifting never gains this definition for opaque calls.
pub(crate) fn check_effect_flags(
    cfg: &Cfg,
    decoded: &[DecodedInstruction],
) -> Result<(), LiftError> {
    check_flags_with_calls(cfg, decoded, true)
}

fn check_flags_with_calls(
    cfg: &Cfg,
    decoded: &[DecodedInstruction],
    calls_define_flags: bool,
) -> Result<(), LiftError> {
    let effect = |operation| {
        if calls_define_flags
            && matches!(operation, Operation::Call(_) | Operation::IndirectCall(_))
        {
            (0, ALL, 0)
        } else {
            flag_effect(operation)
        }
    };
    let reachable = cfg.reachable_blocks();
    let mut incoming = vec![ALL; cfg.blocks().len()];
    let mut outgoing = vec![ALL; cfg.blocks().len()];
    loop {
        let mut changed = false;
        for &id in &reachable {
            let block = cfg.block(id);
            let start = if id == cfg.entry() {
                0
            } else {
                block
                    .predecessors
                    .iter()
                    .filter(|id| reachable.contains(id))
                    .fold(ALL, |known, pred| known & outgoing[pred.index()])
            };
            let mut known = start;
            for instruction in &decoded[block.instructions.clone()] {
                let (_, defined, undefined) = effect(instruction.operation);
                known = (known & !undefined) | defined;
            }
            if incoming[id.index()] != start || outgoing[id.index()] != known {
                incoming[id.index()] = start;
                outgoing[id.index()] = known;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for &id in &reachable {
        let mut known = incoming[id.index()];
        for instruction in &decoded[cfg.block(id).instructions.clone()] {
            let (read, defined, undefined) = effect(instruction.operation);
            if read & !known != 0 {
                return Err(LiftError::UndefinedFlags {
                    address: instruction.address,
                    mask: read & !known,
                });
            }
            known = (known & !undefined) | defined;
        }
    }
    Ok(())
}

struct Lifter {
    next: u64,
    assignments: Vec<Assignment>,
}

impl Lifter {
    fn set(&mut self, index: usize, value: Expr) {
        self.assignments.push(Assignment {
            destination: Reg(index).into(),
            value,
        });
    }
    fn address(&self, address: Addressing) -> Expr {
        let mut value = k(address.displacement as u64);
        if address.rip_relative {
            value = add(value, k(self.next));
        }
        if let Some(base) = address.base {
            value = add(value, r(base as usize));
        }
        if let Some(index) = address.index {
            value = add(
                value,
                b(B::Mul, r(index as usize), k(u64::from(address.scale))),
            );
        }
        value
    }
    fn read_register(&self, register: Register) -> Expr {
        let value = if register.shift == 0 {
            r(register.index as usize)
        } else {
            b(
                B::Shr,
                r(register.index as usize),
                k(u64::from(register.shift)),
            )
        };
        mask(value, register.width)
    }
    fn read(&self, operand: Operand) -> Expr {
        match operand {
            Operand::Register(register) => self.read_register(register),
            Operand::Immediate(value) => k(value),
            Operand::Memory { address, width } => Expr::load(self.address(address), width),
        }
    }
    fn write_register(&mut self, register: Register, value: Expr) {
        let value = mask(value, register.width);
        let value = if matches!(register.width, Width::U32 | Width::U64) {
            value
        } else {
            or(
                and(
                    r(register.index as usize),
                    k(!(register.width.mask() << register.shift)),
                ),
                b(B::Shl, value, k(u64::from(register.shift))),
            )
        };
        self.set(register.index as usize, value);
    }
    fn snapshot_destination(&mut self, destination: Operand) -> (Operand, Expr) {
        match destination {
            Operand::Memory { address, width } => {
                self.set(ADDRESS, self.address(address));
                // Use a frozen address even when the destination register of a
                // later write also appeared in the original addressing mode.
                let frozen = Addressing {
                    base: Some(ADDRESS as u8),
                    index: None,
                    scale: 1,
                    displacement: 0,
                    rip_relative: false,
                };
                (
                    Operand::Memory {
                        address: frozen,
                        width,
                    },
                    Expr::load(r(ADDRESS), width),
                )
            }
            _ => (destination, self.read(destination)),
        }
    }
    fn write(&mut self, destination: Operand, value: Expr) {
        match destination {
            Operand::Register(register) => self.write_register(register, value),
            Operand::Memory { address, width } => self.assignments.push(Assignment {
                destination: Place::Memory {
                    address: self.address(address),
                    width,
                },
                value,
            }),
            Operand::Immediate(_) => unreachable!("decoded writable destination"),
        }
    }
    fn parity(&mut self) -> Expr {
        self.set(PARITY, xor(r(RESULT), b(B::Shr, r(RESULT), k(4))));
        self.set(PARITY, xor(r(PARITY), b(B::Shr, r(PARITY), k(2))));
        self.set(PARITY, xor(r(PARITY), b(B::Shr, r(PARITY), k(1))));
        eq(and(r(PARITY), k(1)), k(0))
    }
    fn result_flags(&mut self, width: Width) {
        self.set(ZF, eq(r(RESULT), k(0)));
        self.set(SF, bit(r(RESULT), width.bits() - 1));
        let parity = self.parity();
        self.set(PF, parity);
    }
    fn alu_core(&mut self, kind: Alu, width: Width, left: Expr, right: Expr, preserve_carry: bool) {
        self.set(A, mask(left, width));
        self.set(V, mask(right, width));
        self.set(
            C,
            if matches!(kind, Alu::Adc | Alu::Sbb) {
                r(CF)
            } else {
                k(0)
            },
        );
        let arithmetic = matches!(kind, Alu::Add | Alu::Adc | Alu::Sub | Alu::Sbb | Alu::Cmp);
        let addition = matches!(kind, Alu::Add | Alu::Adc);
        let result = match kind {
            Alu::Add | Alu::Adc => add(add(r(A), r(V)), r(C)),
            Alu::Sub | Alu::Sbb | Alu::Cmp => sub(sub(r(A), r(V)), r(C)),
            Alu::Or => or(r(A), r(V)),
            Alu::Xor => xor(r(A), r(V)),
            Alu::And | Alu::Test => and(r(A), r(V)),
        };
        self.set(RESULT, mask(result, width));
        if !preserve_carry {
            let carry = if !arithmetic {
                k(0)
            } else if addition {
                or(b(B::Ult, r(RESULT), r(A)), and(r(C), eq(r(RESULT), r(A))))
            } else {
                or(b(B::Ult, r(A), r(V)), and(r(C), eq(r(A), r(V))))
            };
            self.set(CF, carry);
        }
        let overflow = if !arithmetic {
            k(0)
        } else {
            let signs = xor(r(A), r(V));
            let signs = if addition {
                xor(signs, k(u64::MAX))
            } else {
                signs
            };
            ne(
                and(and(signs, xor(r(A), r(RESULT))), k(1 << (width.bits() - 1))),
                k(0),
            )
        };
        self.set(OF, overflow);
        self.result_flags(width);
    }
    fn shift(&mut self, kind: Shift, destination: Operand, count: Operand) {
        let width = destination.width().unwrap();
        let (destination, left) = self.snapshot_destination(destination);
        self.set(A, left);
        self.set(
            C,
            and(
                self.read(count),
                k(if width == Width::U64 { 63 } else { 31 }),
            ),
        );
        let sign = bit(r(A), width.bits() - 1);
        let result = match kind {
            Shift::Left => b(B::Shl, r(A), r(C)),
            Shift::Right => b(B::Shr, r(A), r(C)),
            Shift::ArithmeticRight => {
                let extended = sext(r(A), width);
                Expr::select(
                    eq(r(C), k(0)),
                    extended.clone(),
                    or(
                        b(B::Shr, extended, r(C)),
                        b(B::Shl, sub(k(0), sign.clone()), sub(k(64), r(C))),
                    ),
                )
            }
        };
        self.set(RESULT, mask(result, width));
        let new_carry = match kind {
            Shift::Left => and(b(B::Shr, r(A), sub(k(u64::from(width.bits())), r(C))), k(1)),
            Shift::Right => and(b(B::Shr, r(A), sub(r(C), k(1))), k(1)),
            Shift::ArithmeticRight => Expr::select(
                b(B::Ule, k(u64::from(width.bits())), r(C)),
                sign.clone(),
                and(b(B::Shr, r(A), sub(r(C), k(1))), k(1)),
            ),
        };
        self.set(CF, Expr::select(eq(r(C), k(0)), r(CF), new_carry));
        let overflow = match kind {
            Shift::Left => xor(bit(r(RESULT), width.bits() - 1), r(CF)),
            Shift::Right => sign,
            Shift::ArithmeticRight => k(0),
        };
        self.set(
            OF,
            Expr::select(
                eq(r(C), k(0)),
                r(OF),
                Expr::select(eq(r(C), k(1)), overflow, k(0)),
            ),
        );
        self.set(ZF, Expr::select(eq(r(C), k(0)), r(ZF), eq(r(RESULT), k(0))));
        self.set(
            SF,
            Expr::select(eq(r(C), k(0)), r(SF), bit(r(RESULT), width.bits() - 1)),
        );
        let parity = self.parity();
        self.set(PF, Expr::select(eq(r(C), k(0)), r(PF), parity));
        self.write(destination, r(RESULT));
    }
    // Intel SDM vol.2B SHLD/SHRD: defined nonzero counts, a preserved zero
    // count, and OF available only for a one-bit shift. AF is outside this IR.
    fn double_shift(&mut self, left: bool, destination: Operand, source: Register, count: u8) {
        let width = destination.width().unwrap();
        let count = u64::from(count) & if width == Width::U64 { 63 } else { 31 };
        let (destination, value) = self.snapshot_destination(destination);
        self.set(A, value);
        self.set(V, self.read_register(source));
        if count == 0 {
            self.write(destination, r(A));
            return;
        }
        let complement = u64::from(width.bits()) - count;
        let value = if left {
            or(b(B::Shl, r(A), k(count)), b(B::Shr, r(V), k(complement)))
        } else {
            or(b(B::Shr, r(A), k(count)), b(B::Shl, r(V), k(complement)))
        };
        self.set(RESULT, mask(value, width));
        self.set(
            CF,
            bit(
                r(A),
                if left {
                    width.bits() - count as u32
                } else {
                    count as u32 - 1
                },
            ),
        );
        self.set(
            OF,
            if count == 1 {
                xor(
                    bit(r(A), width.bits() - 1),
                    bit(r(RESULT), width.bits() - 1),
                )
            } else {
                k(0)
            },
        );
        self.result_flags(width);
        self.write(destination, r(RESULT));
    }
    // Intel SDM vol. 2B, RCL/RCR/ROL/ROR operation and flags (4-529/4-530).
    // https://cdrdv2-public.intel.com/782151/253667-sdm-vol-2b.pdf
    fn rotate(&mut self, kind: Rotate, destination: Operand, count: Operand) {
        let width = destination.width().unwrap();
        let (destination, left) = self.snapshot_destination(destination);
        // Freeze both data and CL before any architectural destination write,
        // including AL/AH/CL/CH and ECX/RCX aliases of the count register.
        self.set(A, left);
        self.set(
            C,
            and(
                self.read(count),
                k(if width == Width::U64 { 63 } else { 31 }),
            ),
        );
        self.set(V, and(r(C), k(u64::from(width.bits() - 1))));
        let complement = and(sub(k(0), r(V)), k(u64::from(width.bits() - 1)));
        let (first, second) = match kind {
            Rotate::Left => (b(B::Shl, r(A), r(V)), b(B::Shr, r(A), complement)),
            Rotate::Right => (b(B::Shr, r(A), r(V)), b(B::Shl, r(A), complement)),
        };
        self.set(RESULT, mask(or(first, second), width));
        let carry = match kind {
            Rotate::Left => bit(r(RESULT), 0),
            Rotate::Right => bit(r(RESULT), width.bits() - 1),
        };
        self.set(CF, Expr::select(eq(r(C), k(0)), r(CF), carry));
        let overflow = match kind {
            Rotate::Left => xor(bit(r(RESULT), width.bits() - 1), r(CF)),
            Rotate::Right => xor(
                bit(r(RESULT), width.bits() - 1),
                bit(r(RESULT), width.bits() - 2),
            ),
        };
        self.set(
            OF,
            Expr::select(
                eq(r(C), k(0)),
                r(OF),
                Expr::select(eq(r(C), k(1)), overflow, k(0)),
            ),
        );
        // ZF/SF/PF are untouched. Retain the read and write even at zero count:
        // memory still faults, and a 32-bit destination still clears upper32.
        self.write(destination, r(RESULT));
    }
    fn swapped_bytes(&mut self, value: Expr, width: Width) -> Expr {
        // Shared by BSWAP and MOVBE. Capture the source exactly once, then
        // swap byte pairs, 16-bit halves and (for 64 bits) 32-bit halves.
        self.set(A, value);
        for (shift, bits) in [
            (8, 0x00ff_00ff_00ff_00ff),
            (16, 0x0000_ffff_0000_ffff),
            (32, 0x0000_0000_ffff_ffff),
        ] {
            if shift >= width.bits() {
                break;
            }
            let bits = bits & width.mask();
            self.set(
                A,
                or(
                    b(B::Shl, and(r(A), k(bits)), k(u64::from(shift))),
                    and(b(B::Shr, r(A), k(u64::from(shift))), k(bits)),
                ),
            );
        }
        r(A)
    }
    fn byte_swap(&mut self, destination: Register) {
        let value = self.swapped_bytes(self.read_register(destination), destination.width);
        // The common register writer also zero-extends the 32-bit form.
        // BSWAP leaves every arithmetic flag unchanged.
        self.write_register(destination, value);
    }
    fn movbe(&mut self, destination: Operand, source: Operand) {
        // Intel SDM vol.2B 4-52..4-54. MOVBE is one same-width memory
        // access, never read/modify/write, and preserves every flag.
        match (destination, source) {
            (Operand::Register(destination), Operand::Memory { address, width }) => {
                self.set(ADDRESS, self.address(address));
                let value = self.swapped_bytes(Expr::load(r(ADDRESS), width), width);
                self.write_register(destination, value);
            }
            (Operand::Memory { address, width }, Operand::Register(source)) => {
                // Freeze the address before reading the source, including
                // aliases. There is deliberately no old-destination load.
                self.set(ADDRESS, self.address(address));
                let value = self.swapped_bytes(self.read_register(source), width);
                self.assignments.push(Assignment {
                    destination: Place::Memory {
                        address: r(ADDRESS),
                        width,
                    },
                    value,
                });
            }
            _ => unreachable!("decoder enforces MOVBE register/memory operands"),
        }
    }
    fn bit_test(&mut self, base: Register, index: Operand) {
        // Intel SDM vol.2A 3-130/3-131: register bit offsets wrap modulo
        // operand width. The base is read-only, including the 32-bit form.
        self.set(
            CF,
            and(
                b(
                    B::Shr,
                    self.read_register(base),
                    and(self.read(index), k(u64::from(base.width.bits() - 1))),
                ),
                k(1),
            ),
        );
        // Deterministic placeholders for flags which check_flags makes
        // unavailable. ZF is preserved; neither input GPR is written.
        for flag in [OF, SF, PF] {
            self.set(flag, k(0));
        }
    }
    fn pop(&mut self, destination: Register) {
        self.set(A, Expr::load(r(RSP), Width::U64));
        self.set(RSP, add(r(RSP), k(8)));
        self.write_register(destination, r(A));
    }
    fn instruction(mut self, decoded: DecodedInstruction) -> Result<IrInstruction, LiftError> {
        let mut control = Control::Next;
        match decoded.operation {
            Operation::Nop => {}
            Operation::Mov {
                destination,
                source,
            } => {
                self.set(A, self.read(source));
                self.write(destination, r(A));
            }
            Operation::Extend {
                destination,
                source,
                signed,
            } => {
                let value = self.read(source);
                self.write_register(
                    destination,
                    if signed {
                        sext(value, source.width().unwrap())
                    } else {
                        value
                    },
                );
            }
            Operation::Lea {
                destination,
                address,
            } => self.write_register(destination, self.address(address)),
            Operation::Alu {
                kind,
                destination,
                source,
            } => {
                let width = destination.width().unwrap();
                let (destination, left) = self.snapshot_destination(destination);
                self.alu_core(kind, width, left, self.read(source), false);
                if !matches!(kind, Alu::Cmp | Alu::Test) {
                    self.write(destination, r(RESULT));
                }
            }
            Operation::Unary { kind, destination } => {
                let width = destination.width().unwrap();
                let (destination, value) = self.snapshot_destination(destination);
                match kind {
                    Unary::Not => {
                        self.set(A, value);
                        self.write(destination, xor(r(A), k(width.mask())));
                    }
                    Unary::Neg => {
                        self.alu_core(Alu::Sub, width, k(0), value, false);
                        self.write(destination, r(RESULT));
                    }
                    Unary::Inc | Unary::Dec => {
                        self.alu_core(
                            if kind == Unary::Inc {
                                Alu::Add
                            } else {
                                Alu::Sub
                            },
                            width,
                            value,
                            k(1),
                            true,
                        );
                        self.write(destination, r(RESULT));
                    }
                }
            }
            Operation::Shift {
                kind,
                destination,
                count,
            } => self.shift(kind, destination, count),
            Operation::DoubleShift {
                left,
                destination,
                source,
                count,
            } => self.double_shift(left, destination, source, count),
            Operation::Rotate {
                kind,
                destination,
                count,
            } => self.rotate(kind, destination, count),
            Operation::ByteSwap { destination } => self.byte_swap(destination),
            Operation::Movbe {
                destination,
                source,
            } => self.movbe(destination, source),
            Operation::BitTest { base, index } => self.bit_test(base, index),
            Operation::SignDividend { width } => {
                self.write_register(
                    Register {
                        index: RDX as u8,
                        width,
                        shift: 0,
                    },
                    sub(k(0), bit(r(RAX), width.bits() - 1)),
                );
            }
            Operation::Mul { source } => {
                let width = source.width().unwrap();
                // Read both original operands before changing AX or DX. A
                // memory source occurs exactly once, even when its address
                // uses RAX/RDX or its register aliases either destination.
                self.set(A, mask(r(RAX), width));
                self.set(V, self.read(source));
                self.set(LOW, b(B::Mul, r(A), r(V)));
                self.set(
                    HIGH,
                    if width == Width::U64 {
                        b(B::UMulHigh, r(A), r(V))
                    } else {
                        b(B::Shr, r(LOW), k(u64::from(width.bits())))
                    },
                );
                self.set(CF, ne(r(HIGH), k(0)));
                self.set(OF, r(CF));
                let accumulator = Register {
                    index: RAX as u8,
                    width: if width == Width::U8 {
                        Width::U16
                    } else {
                        width
                    },
                    shift: 0,
                };
                self.write_register(accumulator, r(LOW));
                if width != Width::U8 {
                    self.write_register(
                        Register {
                            index: RDX as u8,
                            width,
                            shift: 0,
                        },
                        r(HIGH),
                    );
                }
            }
            Operation::Imul {
                destination,
                left,
                right,
            } => {
                let width = destination.width;
                self.set(A, sext(self.read(left), width));
                self.set(V, sext(self.read(right), width));
                self.set(LOW, b(B::Mul, r(A), r(V)));
                self.set(
                    HIGH,
                    sub(
                        sub(b(B::UMulHigh, r(A), r(V)), b(B::Mul, bit(r(A), 63), r(V))),
                        b(B::Mul, bit(r(V), 63), r(A)),
                    ),
                );
                self.set(RESULT, mask(r(LOW), width));
                self.set(
                    CF,
                    or(
                        ne(r(LOW), sext(r(RESULT), width)),
                        ne(r(HIGH), sub(k(0), bit(r(RESULT), width.bits() - 1))),
                    ),
                );
                self.set(OF, r(CF));
                self.write_register(destination, r(RESULT));
            }
            Operation::Exchange { left, right } => {
                let (left, value) = self.snapshot_destination(left);
                self.set(A, value);
                self.set(V, self.read_register(right));
                self.write(left, r(V));
                self.write_register(right, r(A));
            }
            Operation::Set {
                condition: code,
                destination,
            } => self.write(destination, condition(code)),
            Operation::Cmov {
                condition: code,
                destination,
                source,
            } => {
                self.set(A, self.read_register(destination));
                // x86 loads a memory source even when the condition is false.
                self.set(V, self.read(source));
                self.write_register(destination, Expr::select(condition(code), r(V), r(A)));
            }
            Operation::Push(source) => {
                self.set(A, self.read(source));
                self.set(RSP, sub(r(RSP), k(8)));
                self.assignments.push(Assignment {
                    destination: Place::Memory {
                        address: r(RSP),
                        width: Width::U64,
                    },
                    value: r(A),
                });
            }
            Operation::Pop(destination) => self.pop(destination),
            Operation::Leave => {
                self.set(RSP, r(RBP));
                self.pop(Register {
                    index: RBP as u8,
                    width: Width::U64,
                    shift: 0,
                });
            }
            Operation::Divide { .. } => {
                return Err(LiftError::Decode(DecodeError {
                    address: decoded.address,
                    reason: "DIV/IDIV requires the module divide-error model".into(),
                }));
            }
            Operation::Call(_) | Operation::IndirectCall(_) | Operation::IndirectJump(_) => {
                return Err(LiftError::Decode(DecodeError {
                    address: decoded.address,
                    reason: "calls and indirect jumps are supported only for reference inspection"
                        .into(),
                }));
            }
            Operation::Jump(target) => control = Control::Jump(target),
            Operation::Branch {
                condition: code,
                target,
            } => {
                control = Control::Branch {
                    condition: condition(code),
                    target,
                }
            }
            Operation::Return { extra_pop } => {
                self.set(RSP, add(r(RSP), k(8 + u64::from(extra_pop))));
                control = Control::Return(r(RAX));
            }
        }
        Ok(IrInstruction {
            address: decoded.address,
            size: u32::from(decoded.size),
            assignments: self.assignments,
            control,
        })
    }
}

pub fn lift(bytes: &[u8], base: u64, entry: u64) -> Result<Program, LiftError> {
    let decoded = decode_reachable(bytes, base, entry).map_err(LiftError::Decode)?;
    let cfg = Cfg::build(
        entry,
        decoded
            .iter()
            .copied()
            .map(DecodedInstruction::layout)
            .collect(),
    )
    .map_err(LiftError::Layout)?;
    check_flags(&cfg, &decoded)?;
    let instructions = decoded
        .into_iter()
        .map(lift_instruction)
        .collect::<Result<_, _>>()?;
    Program::new(entry, REGISTER_COUNT, instructions).map_err(LiftError::Program)
}

// Decode/layout/flags stay the caller's responsibility. The instruction's
// assignments and fault order are shared exactly with the legacy frontend.
pub(crate) fn lift_instruction(
    instruction: DecodedInstruction,
) -> Result<IrInstruction, LiftError> {
    Lifter {
        next: instruction.address + u64::from(instruction.size),
        assignments: Vec::new(),
    }
    .instruction(instruction)
}
