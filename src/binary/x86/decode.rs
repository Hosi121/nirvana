use std::collections::BTreeMap;
use std::fmt;

use crate::control_flow::cfg::{Flow, Instruction};
use crate::model::ir::Width;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Register {
    pub index: u8,
    pub width: Width,
    pub shift: u8,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Addressing {
    pub base: Option<u8>,
    pub index: Option<u8>,
    pub scale: u8,
    pub displacement: i64,
    pub rip_relative: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Operand {
    Register(Register),
    Memory { address: Addressing, width: Width },
    Immediate(u64),
}

impl Operand {
    pub fn width(self) -> Option<Width> {
        match self {
            Self::Register(reg) => Some(reg.width),
            Self::Memory { width, .. } => Some(width),
            Self::Immediate(_) => None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Alu {
    Add,
    Or,
    Adc,
    Sbb,
    And,
    Sub,
    Xor,
    Cmp,
    Test,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unary {
    Inc,
    Dec,
    Not,
    Neg,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Shift {
    Left,
    Right,
    ArithmeticRight,
}

/// Rotate within the operand width, without carrying CF through the value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Rotate {
    Left,
    Right,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Operation {
    Nop,
    Mov {
        destination: Operand,
        source: Operand,
    },
    Extend {
        destination: Register,
        source: Operand,
        signed: bool,
    },
    Lea {
        destination: Register,
        address: Addressing,
    },
    Alu {
        kind: Alu,
        destination: Operand,
        source: Operand,
    },
    Unary {
        kind: Unary,
        destination: Operand,
    },
    Shift {
        kind: Shift,
        destination: Operand,
        count: Operand,
    },
    DoubleShift {
        left: bool,
        destination: Operand,
        source: Register,
        count: u8,
    },
    Rotate {
        kind: Rotate,
        destination: Operand,
        count: Operand,
    },
    ByteSwap {
        destination: Register,
    },
    Movbe {
        destination: Operand,
        source: Operand,
    },
    BitTest {
        base: Register,
        index: Operand,
    },
    Imul {
        destination: Register,
        left: Operand,
        right: Operand,
    },
    /// Unsigned implicit-accumulator multiply, F6/F7 /4.
    Mul {
        source: Operand,
    },
    /// Reference/module decoding: DIV/IDIV has a checked #DE outcome.
    Divide {
        source: Operand,
        signed: bool,
    },
    /// CWD/CDQ/CQO: sign of AX/EAX/RAX into DX/EDX/RDX.
    SignDividend {
        width: Width,
    },
    Exchange {
        left: Operand,
        right: Register,
    },
    Set {
        condition: u8,
        destination: Operand,
    },
    Cmov {
        condition: u8,
        destination: Register,
        source: Operand,
    },
    Push(Operand),
    Pop(Register),
    Leave,
    /// Inspection only; executable decoding and lifting reject calls.
    Call(u64),
    /// Near 64-bit call through a register or memory operand; inspection only.
    IndirectCall(Operand),
    /// Near 64-bit jump through a register or memory operand; inspection only.
    IndirectJump(Operand),
    Jump(u64),
    Branch {
        condition: u8,
        target: u64,
    },
    Return {
        extra_pop: u16,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DecodedInstruction {
    pub address: u64,
    pub size: u8,
    pub operation: Operation,
}

impl DecodedInstruction {
    pub fn layout(self) -> Instruction {
        let flow = match self.operation {
            Operation::Jump(target) => Flow::Jump(target),
            Operation::IndirectJump(_) => Flow::IndirectJump,
            Operation::Branch { target, .. } => Flow::Branch(target),
            Operation::Return { .. } => Flow::Return,
            _ => Flow::Next,
        };
        Instruction::new(self.address, u32::from(self.size), flow)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecodeError {
    pub address: u64,
    pub reason: String,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x86 decode at {:#x}: {}", self.address, self.reason)
    }
}
impl std::error::Error for DecodeError {}

#[derive(Clone, Copy, Eq, PartialEq)]
enum DecodePolicy {
    Executable,
    ReferenceInspection,
}

struct Decoder<'a> {
    bytes: &'a [u8],
    address: u64,
    pos: usize,
    rex: u8,
    rex_seen: bool,
    operand16: bool,
    policy: DecodePolicy,
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
            .ok_or_else(|| self.error("truncated instruction"))?;
        self.pos += 1;
        Ok(byte)
    }
    fn unsigned(&mut self, size: usize) -> Result<u64, DecodeError> {
        let mut bytes = [0; 8];
        for byte in &mut bytes[..size] {
            *byte = self.byte()?;
        }
        Ok(u64::from_le_bytes(bytes))
    }
    fn signed(&mut self, size: usize) -> Result<i64, DecodeError> {
        let value = self.unsigned(size)?;
        Ok(((value << (64 - size * 8)) as i64) >> (64 - size * 8))
    }
    fn width(&self) -> Width {
        if self.rex & 8 != 0 {
            Width::U64
        } else if self.operand16 {
            Width::U16
        } else {
            Width::U32
        }
    }
    fn register(&self, code: u8, width: Width) -> Register {
        if width == Width::U8 && !self.rex_seen && (4..8).contains(&code) {
            Register {
                index: code - 4,
                width,
                shift: 8,
            }
        } else {
            Register {
                index: code,
                width,
                shift: 0,
            }
        }
    }
    fn modrm(&mut self, width: Width) -> Result<(Register, Operand, u8), DecodeError> {
        let byte = self.byte()?;
        let mode = byte >> 6;
        let group = (byte >> 3) & 7;
        let reg = self.register(group | ((self.rex & 4) << 1), width);
        let rm = byte & 7;
        if mode == 3 {
            return Ok((
                reg,
                Operand::Register(self.register(rm | ((self.rex & 1) << 3), width)),
                group,
            ));
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
        Ok((reg, Operand::Memory { address, width }, group))
    }
    fn immediate(&mut self, width: Width) -> Result<Operand, DecodeError> {
        Ok(Operand::Immediate(if width == Width::U64 {
            self.signed(4)? as u64
        } else {
            self.unsigned(width.bytes())?
        }))
    }
    fn relative(&mut self, bytes: usize) -> Result<u64, DecodeError> {
        let displacement = self.signed(bytes)?;
        let next = self
            .address
            .checked_add(self.pos as u64)
            .ok_or_else(|| self.error("address overflow"))?;
        Ok(next.wrapping_add_signed(displacement))
    }
    fn alu(group: u8) -> Alu {
        [
            Alu::Add,
            Alu::Or,
            Alu::Adc,
            Alu::Sbb,
            Alu::And,
            Alu::Sub,
            Alu::Xor,
            Alu::Cmp,
        ][group as usize]
    }

    fn operation(&mut self) -> Result<Operation, DecodeError> {
        let mut repeat = false;
        // Keep executable prefix handling unchanged. Reference-only control
        // transfers accept one optional REX. Near indirect transfers also
        // accept one 3E NOTRACK prefix; the execution model has no CET tracker.
        // Operand overrides, BND and ambiguous prefix combinations stay out.
        let mut reference_prefixes_supported = true;
        let mut notrack = false;
        let opcode = loop {
            let byte = self.byte()?;
            match byte {
                0x66 => {
                    if self.rex_seen {
                        return Err(self.error("legacy prefix after REX is unsupported"));
                    }
                    self.operand16 = true;
                    reference_prefixes_supported = false;
                }
                0x40..=0x4f => {
                    reference_prefixes_supported &= !self.rex_seen;
                    self.rex = byte & 15;
                    self.rex_seen = true;
                }
                0xf3 => {
                    if self.rex_seen {
                        return Err(self.error("legacy prefix after REX is unsupported"));
                    }
                    repeat = true;
                    reference_prefixes_supported = false;
                }
                0x3e => {
                    if self.rex_seen {
                        return Err(self.error("legacy prefix after REX is unsupported"));
                    }
                    reference_prefixes_supported &= !notrack;
                    notrack = true;
                }
                0x26 | 0x2e | 0x36 => {
                    if self.rex_seen {
                        return Err(self.error("legacy prefix after REX is unsupported"));
                    }
                    reference_prefixes_supported = false;
                }
                0x64 | 0x65 | 0x67 | 0xf0 | 0xf2 => {
                    return Err(self.error(format!("unsupported prefix {byte:#04x}")));
                }
                _ => break byte,
            }
        };
        if repeat {
            if opcode == 0x90 {
                return Ok(Operation::Nop);
            }
            if opcode == 0x0f && self.byte()? == 0x1e && self.byte()? == 0xfa {
                return Ok(Operation::Nop);
            }
            return Err(self.error("unsupported REP-prefixed instruction"));
        }
        let width = self.width();
        if opcode <= 0x3d && opcode & 7 <= 5 {
            let kind = Self::alu(opcode >> 3);
            let size = if opcode & 1 == 0 { Width::U8 } else { width };
            let (destination, source) = match opcode & 7 {
                0 | 1 => {
                    let (reg, rm, _) = self.modrm(size)?;
                    (rm, Operand::Register(reg))
                }
                2 | 3 => {
                    let (reg, rm, _) = self.modrm(size)?;
                    (Operand::Register(reg), rm)
                }
                4 | 5 => (
                    Operand::Register(self.register(0, size)),
                    self.immediate(size)?,
                ),
                _ => unreachable!(),
            };
            return Ok(Operation::Alu {
                kind,
                destination,
                source,
            });
        }
        Ok(match opcode {
            0x98 => Operation::Extend {
                destination: Register {
                    index: 0,
                    width,
                    shift: 0,
                },
                source: Operand::Register(Register {
                    index: 0,
                    width: match width {
                        Width::U64 => Width::U32,
                        Width::U32 => Width::U16,
                        _ => Width::U8,
                    },
                    shift: 0,
                }),
                signed: true,
            },
            0x99 => Operation::SignDividend { width },
            0x90 if self.rex & 1 == 0 => Operation::Nop,
            0x90 => Operation::Exchange {
                left: Operand::Register(self.register(0, width)),
                right: self.register(8, width),
            },
            0x91..=0x97 => Operation::Exchange {
                left: Operand::Register(self.register(0, width)),
                right: self.register((opcode & 7) | ((self.rex & 1) << 3), width),
            },
            0x50..=0x57 => {
                if self.operand16 {
                    return Err(self.error("16-bit push is unsupported"));
                }
                Operation::Push(Operand::Register(
                    self.register((opcode & 7) | ((self.rex & 1) << 3), Width::U64),
                ))
            }
            0x58..=0x5f => {
                if self.operand16 {
                    return Err(self.error("16-bit pop is unsupported"));
                }
                Operation::Pop(self.register((opcode & 7) | ((self.rex & 1) << 3), Width::U64))
            }
            0x68 | 0x6a => {
                if self.operand16 {
                    return Err(self.error("16-bit push is unsupported"));
                }
                Operation::Push(Operand::Immediate(self.signed(if opcode == 0x68 {
                    4
                } else {
                    1
                })? as u64))
            }
            0x69 | 0x6b => {
                let (destination, left, _) = self.modrm(width)?;
                let right = if opcode == 0x6b {
                    Operand::Immediate(self.signed(1)? as u64)
                } else {
                    self.immediate(width)?
                };
                Operation::Imul {
                    destination,
                    left,
                    right,
                }
            }
            0x70..=0x7f => Operation::Branch {
                condition: opcode & 15,
                target: self.relative(1)?,
            },
            0x80 | 0x81 | 0x83 => {
                let size = if opcode == 0x80 { Width::U8 } else { width };
                let (_, destination, group) = self.modrm(size)?;
                let source = if opcode == 0x83 {
                    Operand::Immediate(self.signed(1)? as u64)
                } else {
                    self.immediate(size)?
                };
                Operation::Alu {
                    kind: Self::alu(group),
                    destination,
                    source,
                }
            }
            0x84 | 0x85 => {
                let (reg, destination, _) =
                    self.modrm(if opcode == 0x84 { Width::U8 } else { width })?;
                Operation::Alu {
                    kind: Alu::Test,
                    destination,
                    source: Operand::Register(reg),
                }
            }
            0x86 | 0x87 => {
                let (right, left, _) =
                    self.modrm(if opcode == 0x86 { Width::U8 } else { width })?;
                Operation::Exchange { left, right }
            }
            0x88..=0x8b => {
                let (reg, rm, _) = self.modrm(if opcode & 1 == 0 { Width::U8 } else { width })?;
                if opcode & 2 == 0 {
                    Operation::Mov {
                        destination: rm,
                        source: Operand::Register(reg),
                    }
                } else {
                    Operation::Mov {
                        destination: Operand::Register(reg),
                        source: rm,
                    }
                }
            }
            0x8d => {
                let (destination, rm, _) = self.modrm(width)?;
                let Operand::Memory { address, .. } = rm else {
                    return Err(self.error("LEA requires a memory addressing form"));
                };
                Operation::Lea {
                    destination,
                    address,
                }
            }
            0x8f => {
                let (_, rm, group) = self.modrm(Width::U64)?;
                if group != 0 || self.operand16 {
                    return Err(self.error("unsupported POP form"));
                }
                let Operand::Register(reg) = rm else {
                    return Err(self.error("POP to memory is unsupported"));
                };
                Operation::Pop(reg)
            }
            0xa0..=0xa3 => {
                let size = if opcode & 1 == 0 { Width::U8 } else { width };
                let address = Addressing {
                    base: None,
                    index: None,
                    scale: 1,
                    displacement: self.unsigned(8)? as i64,
                    rip_relative: false,
                };
                let memory = Operand::Memory {
                    address,
                    width: size,
                };
                let reg = Operand::Register(self.register(0, size));
                if opcode & 2 == 0 {
                    Operation::Mov {
                        destination: reg,
                        source: memory,
                    }
                } else {
                    Operation::Mov {
                        destination: memory,
                        source: reg,
                    }
                }
            }
            0xa8 | 0xa9 => {
                let size = if opcode == 0xa8 { Width::U8 } else { width };
                Operation::Alu {
                    kind: Alu::Test,
                    destination: Operand::Register(self.register(0, size)),
                    source: self.immediate(size)?,
                }
            }
            0xb0..=0xbf => {
                let size = if opcode < 0xb8 { Width::U8 } else { width };
                let destination =
                    Operand::Register(self.register((opcode & 7) | ((self.rex & 1) << 3), size));
                Operation::Mov {
                    destination,
                    source: Operand::Immediate(self.unsigned(size.bytes())?),
                }
            }
            0xc0 | 0xc1 | 0xd0..=0xd3 => {
                let (_, destination, group) =
                    self.modrm(if opcode & 1 == 0 { Width::U8 } else { width })?;
                let count = match opcode {
                    0xc0 | 0xc1 => Operand::Immediate(self.unsigned(1)?),
                    0xd0 | 0xd1 => Operand::Immediate(1),
                    _ => Operand::Register(self.register(1, Width::U8)),
                };
                match group {
                    0 | 1 => Operation::Rotate {
                        kind: if group == 0 {
                            Rotate::Left
                        } else {
                            Rotate::Right
                        },
                        destination,
                        count,
                    },
                    4 | 5 | 7 => Operation::Shift {
                        kind: match group {
                            4 => Shift::Left,
                            5 => Shift::Right,
                            _ => Shift::ArithmeticRight,
                        },
                        destination,
                        count,
                    },
                    _ => return Err(self.error("RCL/RCR or unsupported shift group")),
                }
            }
            0xc2 | 0xc3 => {
                if self.operand16 {
                    return Err(self.error("16-bit RET is unsupported"));
                }
                Operation::Return {
                    extra_pop: if opcode == 0xc2 {
                        self.unsigned(2)? as u16
                    } else {
                        0
                    },
                }
            }
            0xc6 | 0xc7 => {
                let size = if opcode == 0xc6 { Width::U8 } else { width };
                let (_, destination, group) = self.modrm(size)?;
                if group != 0 {
                    return Err(self.error("unsupported MOV immediate group"));
                }
                Operation::Mov {
                    destination,
                    source: self.immediate(size)?,
                }
            }
            0xc9 => {
                if self.operand16 {
                    return Err(self.error("16-bit LEAVE is unsupported"));
                }
                Operation::Leave
            }
            0xe8 if self.policy == DecodePolicy::ReferenceInspection => {
                if !reference_prefixes_supported || notrack {
                    return Err(self.error("unsupported prefixes on reference control transfer"));
                }
                Operation::Call(self.relative(4)?)
            }
            0xe9 | 0xeb => Operation::Jump(self.relative(if opcode == 0xe9 { 4 } else { 1 })?),
            0xf6 | 0xf7 => {
                let size = if opcode == 0xf6 { Width::U8 } else { width };
                let (_, destination, group) = self.modrm(size)?;
                match group {
                    0 => Operation::Alu {
                        kind: Alu::Test,
                        destination,
                        source: self.immediate(size)?,
                    },
                    2 => Operation::Unary {
                        kind: Unary::Not,
                        destination,
                    },
                    3 => Operation::Unary {
                        kind: Unary::Neg,
                        destination,
                    },
                    4 => Operation::Mul {
                        source: destination,
                    },
                    6 | 7 if self.policy == DecodePolicy::ReferenceInspection => {
                        Operation::Divide {
                            source: destination,
                            signed: group == 7,
                        }
                    }
                    _ => return Err(self.error("implicit multiply/divide is unsupported")),
                }
            }
            0xfe | 0xff => {
                let group = (self
                    .bytes
                    .get(self.pos)
                    .ok_or_else(|| self.error("truncated ModR/M"))?
                    >> 3)
                    & 7;
                let reference_control = opcode == 0xff
                    && matches!(group, 2 | 4)
                    && self.policy == DecodePolicy::ReferenceInspection;
                if reference_control && !reference_prefixes_supported {
                    return Err(self.error("unsupported prefixes on reference control transfer"));
                }
                let size = if opcode == 0xfe {
                    Width::U8
                } else if group == 6 || reference_control {
                    Width::U64
                } else {
                    width
                };
                let (_, destination, group) = self.modrm(size)?;
                match group {
                    0 | 1 => Operation::Unary {
                        kind: if group == 0 { Unary::Inc } else { Unary::Dec },
                        destination,
                    },
                    2 if reference_control => Operation::IndirectCall(destination),
                    4 if reference_control => Operation::IndirectJump(destination),
                    6 if opcode == 0xff && !self.operand16 => Operation::Push(destination),
                    _ => return Err(self.error("indirect call/jump or unsupported FF group")),
                }
            }
            0x63 => {
                if self.operand16 {
                    return Err(self.error("16-bit MOVSXD form is unsupported"));
                }
                let (destination, source, _) = self.modrm(Width::U32)?;
                Operation::Extend {
                    destination: Register {
                        width,
                        ..destination
                    },
                    source,
                    signed: true,
                }
            }
            0x0f => {
                let second = self.byte()?;
                match second {
                    0xa4 | 0xac => {
                        let (source, destination, _) = self.modrm(width)?;
                        let count = self.byte()?;
                        let effective =
                            u64::from(count) & if width == Width::U64 { 63 } else { 31 };
                        if effective > u64::from(width.bits()) {
                            return Err(self.error("double shift count exceeds operand width"));
                        }
                        Operation::DoubleShift {
                            left: second == 0xa4,
                            destination,
                            source,
                            count,
                        }
                    }
                    0x1f => {
                        let (_, _, group) = self.modrm(width)?;
                        if group != 0 {
                            return Err(self.error("unsupported multi-byte NOP group"));
                        }
                        Operation::Nop
                    }
                    0x38 => {
                        let third = self.byte()?;
                        if !matches!(third, 0xf0 | 0xf1) {
                            return Err(self.error(format!("unsupported opcode 0f 38 {third:02x}")));
                        }
                        let (register, memory, _) = self.modrm(width)?;
                        if !matches!(memory, Operand::Memory { .. }) {
                            return Err(self.error("MOVBE requires one memory operand"));
                        }
                        let register = Operand::Register(register);
                        let (destination, source) = if third == 0xf0 {
                            (register, memory)
                        } else {
                            (memory, register)
                        };
                        Operation::Movbe {
                            destination,
                            source,
                        }
                    }
                    0x40..=0x4f => {
                        let (destination, source, _) = self.modrm(width)?;
                        Operation::Cmov {
                            condition: second & 15,
                            destination,
                            source,
                        }
                    }
                    0x80..=0x8f => Operation::Branch {
                        condition: second & 15,
                        target: self.relative(4)?,
                    },
                    0x90..=0x9f => {
                        let (_, destination, _) = self.modrm(Width::U8)?;
                        Operation::Set {
                            condition: second & 15,
                            destination,
                        }
                    }
                    0xa3 | 0xba => {
                        let (index, base, group) = self.modrm(width)?;
                        if second == 0xba && group != 4 {
                            return Err(
                                self.error("only BT /4 is supported; BTS/BTR/BTC are unsupported")
                            );
                        }
                        let Operand::Register(base) = base else {
                            return Err(self.error("memory BT is unsupported"));
                        };
                        let index = if second == 0xba {
                            Operand::Immediate(self.unsigned(1)?)
                        } else {
                            Operand::Register(index)
                        };
                        Operation::BitTest { base, index }
                    }
                    0xaf => {
                        let (destination, right, _) = self.modrm(width)?;
                        Operation::Imul {
                            destination,
                            left: Operand::Register(destination),
                            right,
                        }
                    }
                    0xc8..=0xcf => {
                        if width == Width::U16 {
                            return Err(self.error("16-bit BSWAP has undefined results"));
                        }
                        // The register is in opcode+rd. REX.B extends it;
                        // REX.R is ignored (Intel SDM documentation correction).
                        Operation::ByteSwap {
                            destination: self.register((second & 7) | ((self.rex & 1) << 3), width),
                        }
                    }
                    0xb6 | 0xb7 | 0xbe | 0xbf => {
                        let (reg, source, _) = self.modrm(if second & 1 == 0 {
                            Width::U8
                        } else {
                            Width::U16
                        })?;
                        Operation::Extend {
                            destination: Register {
                                index: ((reg.index + if reg.shift == 8 { 4 } else { 0 }) & 7)
                                    | ((self.rex & 4) << 1),
                                width,
                                shift: 0,
                            },
                            source,
                            signed: second & 8 != 0,
                        }
                    }
                    _ => return Err(self.error(format!("unsupported opcode 0f {second:02x}"))),
                }
            }
            _ => return Err(self.error(format!("unsupported opcode {opcode:02x}"))),
        })
    }
}

pub fn decode_at(bytes: &[u8], address: u64) -> Result<DecodedInstruction, DecodeError> {
    decode_with_policy(bytes, address, DecodePolicy::Executable)
}

/// Decode one instruction for reference inspection, including direct calls and
/// near 64-bit indirect calls/jumps. This does not enable their execution in
/// [`super::lift`] or change the policy of [`decode_at`] / [`decode_reachable`].
pub fn decode_reference_at(bytes: &[u8], address: u64) -> Result<DecodedInstruction, DecodeError> {
    decode_with_policy(bytes, address, DecodePolicy::ReferenceInspection)
}

fn decode_with_policy(
    bytes: &[u8],
    address: u64,
    policy: DecodePolicy,
) -> Result<DecodedInstruction, DecodeError> {
    let mut decoder = Decoder {
        bytes,
        address,
        pos: 0,
        rex: 0,
        rex_seen: false,
        operand16: false,
        policy,
    };
    let operation = decoder.operation()?;
    address
        .checked_add(decoder.pos as u64)
        .ok_or_else(|| decoder.error("address overflow"))?;
    Ok(DecodedInstruction {
        address,
        size: decoder.pos as u8,
        operation,
    })
}

pub fn decode_reachable(
    bytes: &[u8],
    base: u64,
    entry: u64,
) -> Result<Vec<DecodedInstruction>, DecodeError> {
    let end = base
        .checked_add(bytes.len() as u64)
        .ok_or_else(|| DecodeError {
            address: base,
            reason: "function range overflows".into(),
        })?;
    let mut decoded: BTreeMap<u64, DecodedInstruction> = BTreeMap::new();
    let mut pending = vec![entry];
    while let Some(address) = pending.pop() {
        if decoded.contains_key(&address) {
            continue;
        }
        if address < base || address >= end {
            return Err(DecodeError {
                address,
                reason: "control flow leaves the supplied function".into(),
            });
        }
        if let Some((_, previous)) = decoded.range(..address).next_back()
            && address < previous.address + u64::from(previous.size)
        {
            return Err(DecodeError {
                address,
                reason: "branch enters an instruction".into(),
            });
        }
        let instruction = decode_at(&bytes[(address - base) as usize..], address)?;
        let next = address + u64::from(instruction.size);
        if decoded.range(address..next).next().is_some() {
            return Err(DecodeError {
                address,
                reason: "overlapping instruction streams".into(),
            });
        }
        match instruction.operation {
            Operation::Return { .. } => {}
            Operation::Jump(target) => pending.push(target),
            Operation::Branch { target, .. } => {
                pending.push(next);
                pending.push(target);
            }
            _ => pending.push(next),
        }
        decoded.insert(address, instruction);
    }
    Ok(decoded.into_values().collect())
}
