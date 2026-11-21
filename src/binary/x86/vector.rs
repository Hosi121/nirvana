//! Opt-in legacy SSE data movement for the whole-module runner.
//!
//! XMM0..15 occupy pairs of 64-bit registers at 32..63. Scratch registers
//! 64..68 are private to an instruction. The caller must charge its instruction
//! budget and check `memory` in full, including alignment, BEFORE executing any
//! assignment. In particular, two U64 stores are one guarded vector store.
//! This models ordinary contiguous RAM, not MMIO or concurrent memory.

use super::{Addressing, DecodeError};
use crate::model::ir::{AccessKind, Assignment, BinaryOp, Expr, Place, Reg, Width};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VectorMemory {
    pub address: Expr,
    pub width: u32,
    pub access: AccessKind,
    pub alignment: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VectorInstruction {
    pub address: u64,
    pub size: u32,
    pub assignments: Vec<Assignment>,
    pub memory: Option<VectorMemory>,
}

const ADDRESS: usize = 64;
const SOURCE_LOW: usize = 65;
const SOURCE_HIGH: usize = 66;
const RESULT_LOW: usize = 67;
const RESULT_HIGH: usize = 68;

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}

fn add(left: Expr, right: Expr) -> Expr {
    Expr::binary(BinaryOp::Add, left, right)
}

fn lane(register: u8, high: bool) -> usize {
    32 + usize::from(register) * 2 + usize::from(high)
}

fn assign(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Register(Reg(register)),
        value,
    }
}

#[derive(Clone, Copy)]
enum Source {
    Register(u8),
    Memory(Addressing),
}

#[derive(Clone, Copy)]
enum Operation {
    Move { store: bool, alignment: u32 },
    Xor,
    UnpackLow,
    MoveQuadword,
    MoveHigh,
}

struct Decoder<'a> {
    bytes: &'a [u8],
    address: u64,
    pos: usize,
    rex: u8,
}

impl Decoder<'_> {
    fn error(&self, reason: impl Into<String>) -> DecodeError {
        DecodeError {
            address: self.address,
            reason: reason.into(),
        }
    }

    fn byte(&mut self) -> Result<u8, DecodeError> {
        if self.pos >= 15 {
            return Err(self.error("instruction exceeds 15 bytes"));
        }
        let byte = *self
            .bytes
            .get(self.pos)
            .ok_or_else(|| self.error("truncated vector instruction"))?;
        self.pos += 1;
        Ok(byte)
    }

    fn signed(&mut self, size: usize) -> Result<i64, DecodeError> {
        let mut value = 0_u64;
        for shift in 0..size {
            value |= u64::from(self.byte()?) << (shift * 8);
        }
        Ok(((value << (64 - size * 8)) as i64) >> (64 - size * 8))
    }

    fn operation(&mut self) -> Result<Operation, DecodeError> {
        // Deliberately accept one mandatory prefix and one optional REX in
        // architectural order. Redundant/conflicting/segment/address/LOCK
        // prefixes stay unsupported instead of changing instruction identity.
        let mut opcode = self.byte()?;
        let mandatory = if matches!(opcode, 0x66 | 0xf3) {
            let prefix = opcode;
            opcode = self.byte()?;
            Some(prefix)
        } else {
            None
        };
        if (0x40..=0x4f).contains(&opcode) {
            self.rex = opcode & 15;
            opcode = self.byte()?;
        }
        if opcode != 0x0f {
            return Err(self.error("unsupported vector opcode or prefix sequence"));
        }
        let opcode = self.byte()?;
        match (mandatory, opcode) {
            (None, 0x10 | 0x11) => Ok(Operation::Move {
                store: opcode == 0x11,
                alignment: 1,
            }),
            (None, 0x28 | 0x29) => Ok(Operation::Move {
                store: opcode == 0x29,
                alignment: 16,
            }),
            (Some(0x66), 0x6f | 0x7f) => Ok(Operation::Move {
                store: opcode == 0x7f,
                alignment: 16,
            }),
            (Some(0xf3), 0x6f | 0x7f) => Ok(Operation::Move {
                store: opcode == 0x7f,
                alignment: 1,
            }),
            (None, 0x57) | (Some(0x66), 0xef) => Ok(Operation::Xor),
            (Some(0x66), 0x6c) => Ok(Operation::UnpackLow),
            (Some(0x66), 0x6e) if self.rex & 8 != 0 => Ok(Operation::MoveQuadword),
            // Observed in the non-PIE O2 HTTP fixture. The register form of
            // 0F16 is MOVLHPS and is intentionally not accepted as MOVHPS.
            (None, 0x16) => Ok(Operation::MoveHigh),
            _ => Err(self.error("unsupported vector opcode or mandatory prefix")),
        }
    }

    fn modrm(&mut self) -> Result<(u8, Source), DecodeError> {
        let byte = self.byte()?;
        let mode = byte >> 6;
        let register = ((byte >> 3) & 7) | ((self.rex & 4) << 1);
        let rm = byte & 7;
        if mode == 3 {
            return Ok((register, Source::Register(rm | ((self.rex & 1) << 3))));
        }
        let mut address = Addressing {
            base: None,
            index: None,
            scale: 1,
            displacement: 0,
            rip_relative: false,
        };
        if rm == 4 {
            let sib = self.byte()?;
            let index = (sib >> 3) & 7;
            let base = sib & 7;
            address.scale = 1 << (sib >> 6);
            if index != 4 || self.rex & 2 != 0 {
                address.index = Some(index | ((self.rex & 2) << 2));
            }
            if mode == 0 && base == 5 {
                address.displacement = self.signed(4)?;
            } else {
                address.base = Some(base | ((self.rex & 1) << 3));
            }
        } else if mode == 0 && rm == 5 {
            address.rip_relative = true;
            address.displacement = self.signed(4)?;
        } else {
            address.base = Some(rm | ((self.rex & 1) << 3));
        }
        match mode {
            1 => address.displacement = self.signed(1)?,
            2 => address.displacement = self.signed(4)?,
            _ => {}
        }
        Ok((register, Source::Memory(address)))
    }
}

fn address_expr(address: Addressing, next: u64) -> Expr {
    let mut value = Expr::Const(address.displacement as u64);
    if address.rip_relative {
        value = add(value, Expr::Const(next));
    }
    if let Some(base) = address.base {
        value = add(value, r(usize::from(base)));
    }
    if let Some(index) = address.index {
        value = add(
            value,
            Expr::binary(
                BinaryOp::Mul,
                r(usize::from(index)),
                Expr::Const(u64::from(address.scale)),
            ),
        );
    }
    value
}

/// Decode and lift one supported legacy SSE instruction at `address`.
///
/// This does not change `decode_at` or `decode_reference_at`. Supported forms
/// are PXOR/XORPS, MOVAPS/UPS/DQA/DQU (register or m128), PUNPCKLQDQ (register
/// or m128), MOVQ from a 64-bit GPR, and MOVHPS from m64. Legacy XOR/unpack
/// memory operands, MOVAPS, and MOVDQA require 16-byte alignment. Other SIMD,
/// VEX/EVEX, memory MOVQ, and redundant prefixes return `DecodeError`.
pub fn decode_vector_at(bytes: &[u8], address: u64) -> Result<VectorInstruction, DecodeError> {
    let mut decoder = Decoder {
        bytes,
        address,
        pos: 0,
        rex: 0,
    };
    let operation = decoder.operation()?;
    let (register, source) = decoder.modrm()?;
    if matches!(operation, Operation::MoveQuadword) && !matches!(source, Source::Register(_)) {
        return Err(decoder.error("only GPR to XMM MOVQ is supported"));
    }
    if matches!(operation, Operation::MoveHigh) && !matches!(source, Source::Memory(_)) {
        return Err(decoder.error("MOVLHPS register form is unsupported"));
    }
    let next = address
        .checked_add(decoder.pos as u64)
        .ok_or_else(|| decoder.error("address overflow"))?;
    let mut instruction = VectorInstruction {
        address,
        size: decoder.pos as u32,
        assignments: Vec::new(),
        memory: None,
    };
    if let Operation::Move {
        store: true,
        alignment,
    } = operation
    {
        match source {
            Source::Register(destination) => {
                commit(
                    &mut instruction.assignments,
                    destination,
                    r(lane(register, false)),
                    r(lane(register, true)),
                );
            }
            Source::Memory(memory) => {
                let address = address_expr(memory, next);
                instruction.memory = Some(VectorMemory {
                    address: address.clone(),
                    width: 16,
                    access: AccessKind::Write,
                    alignment,
                });
                instruction.assignments.extend([
                    assign(ADDRESS, address),
                    assign(SOURCE_LOW, r(lane(register, false))),
                    assign(SOURCE_HIGH, r(lane(register, true))),
                    Assignment {
                        destination: Place::Memory {
                            address: r(ADDRESS),
                            width: Width::U64,
                        },
                        value: r(SOURCE_LOW),
                    },
                    Assignment {
                        destination: Place::Memory {
                            address: add(r(ADDRESS), Expr::Const(8)),
                            width: Width::U64,
                        },
                        value: r(SOURCE_HIGH),
                    },
                ]);
            }
        }
        return Ok(instruction);
    }
    let (source_low, source_high) = match source {
        Source::Register(source) => {
            if matches!(operation, Operation::MoveQuadword) {
                (r(usize::from(source)), Expr::Const(0))
            } else {
                (r(lane(source, false)), r(lane(source, true)))
            }
        }
        Source::Memory(memory) => {
            let (width, alignment) = match operation {
                Operation::Move { alignment, .. } => (16, alignment),
                Operation::MoveHigh => (8, 1),
                _ => (16, 16),
            };
            let address = address_expr(memory, next);
            instruction.memory = Some(VectorMemory {
                address: address.clone(),
                width,
                access: AccessKind::Read,
                alignment,
            });
            instruction.assignments.extend([
                assign(ADDRESS, address),
                assign(SOURCE_LOW, Expr::load(r(ADDRESS), Width::U64)),
            ]);
            if width == 16 {
                instruction.assignments.push(assign(
                    SOURCE_HIGH,
                    Expr::load(add(r(ADDRESS), Expr::Const(8)), Width::U64),
                ));
            }
            (r(SOURCE_LOW), r(SOURCE_HIGH))
        }
    };
    let (low, high) = match operation {
        Operation::Move { .. } | Operation::MoveQuadword => (source_low, source_high),
        Operation::Xor => (
            Expr::binary(BinaryOp::Xor, r(lane(register, false)), source_low),
            Expr::binary(BinaryOp::Xor, r(lane(register, true)), source_high),
        ),
        Operation::UnpackLow => (r(lane(register, false)), source_low),
        Operation::MoveHigh => (r(lane(register, false)), source_low),
    };
    commit(&mut instruction.assignments, register, low, high);
    Ok(instruction)
}

fn commit(assignments: &mut Vec<Assignment>, register: u8, low: Expr, high: Expr) {
    // Compute both outputs before either architectural lane is overwritten.
    // This also handles aliased PUNPCKLQDQ and source=destination correctly.
    assignments.extend([
        assign(RESULT_LOW, low),
        assign(RESULT_HIGH, high),
        assign(lane(register, false), r(RESULT_LOW)),
        assign(lane(register, true), r(RESULT_HIGH)),
    ]);
}
