//! Initial-image jump-table candidates for instruction discovery. Candidates
//! retain an open residual and never replace executable target expressions.

use crate::ir::Width;
use crate::x86::{Addressing, Alu, DecodedInstruction, Operand, Operation, Register, Shift};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

pub const MAX_WINDOW: usize = 24;
pub const MAX_ENTRIES: usize = 256;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entry {
    pub address: u64,
    pub target: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Candidate {
    pub branch: u64,
    pub table: u64,
    pub width: Width,
    pub signed: bool,
    pub bias: u64,
    pub entries: Vec<Entry>,
    pub reached_entry_limit: bool,
    /// Local unsigned-guard/mask hint for table extent, not CFG completeness.
    pub entry_limit_hint: Option<usize>,
}
impl Candidate {
    pub fn targets(&self) -> BTreeSet<u64> {
        self.entries.iter().map(|e| e.target).collect()
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Word {
    Linear {
        constant: u64,
        term: Option<(u32, u64)>,
    },
    Entry {
        table: u64,
        width: Width,
        signed: bool,
        bias: u64,
    },
}
impl Word {
    fn constant(n: u64) -> Self {
        Self::Linear {
            constant: n,
            term: None,
        }
    }
    fn number(self) -> Option<u64> {
        match self {
            Self::Linear {
                constant,
                term: None,
            } => Some(constant),
            _ => None,
        }
    }
    fn scale(self, n: u64) -> Option<Self> {
        match self {
            Self::Linear { constant, term } => Some(Self::Linear {
                constant: constant.wrapping_mul(n),
                term: term.and_then(|(id, c)| {
                    let c = c.wrapping_mul(n);
                    (c != 0).then_some((id, c))
                }),
            }),
            entry if n == 1 => Some(entry),
            _ => None,
        }
    }
    fn add(self, other: Self) -> Option<Self> {
        match (self, other) {
            (
                Self::Linear {
                    constant: a,
                    term: x,
                },
                Self::Linear {
                    constant: b,
                    term: y,
                },
            ) => {
                let term = match (x, y) {
                    (None, t) | (t, None) => t,
                    (Some((i, a)), Some((j, b))) if i == j => {
                        let n = a.wrapping_add(b);
                        (n != 0).then_some((i, n))
                    }
                    _ => return None,
                };
                Some(Self::Linear {
                    constant: a.wrapping_add(b),
                    term,
                })
            }
            (
                Self::Entry {
                    table,
                    width,
                    signed,
                    bias,
                },
                Self::Linear {
                    constant,
                    term: None,
                },
            )
            | (
                Self::Linear {
                    constant,
                    term: None,
                },
                Self::Entry {
                    table,
                    width,
                    signed,
                    bias,
                },
            ) => Some(Self::Entry {
                table,
                width,
                signed,
                bias: bias.wrapping_add(constant),
            }),
            _ => None,
        }
    }
}

struct Values {
    registers: [Word; 16],
    fresh: u32,
    bounds: BTreeMap<u32, u64>,
    entry_limits: BTreeMap<(u64, u32), usize>,
    comparison: Option<(Register, u64)>,
}
impl Values {
    fn new() -> Self {
        Self {
            registers: std::array::from_fn(|i| Word::Linear {
                constant: 0,
                term: Some((i as u32, 1)),
            }),
            fresh: 16,
            bounds: BTreeMap::new(),
            entry_limits: BTreeMap::new(),
            comparison: None,
        }
    }
    fn unknown(&mut self) -> Word {
        let id = self.fresh;
        self.fresh += 1;
        Word::Linear {
            constant: 0,
            term: Some((id, 1)),
        }
    }
    fn register(&mut self, r: Register) -> Word {
        let value = self.registers[r.index as usize];
        if r.width == Width::U64 && r.shift == 0 {
            return value;
        }
        if let Some(n) = value.number() {
            return Word::constant((n >> r.shift) & r.width.mask());
        }
        if r.width == Width::U32 && r.shift == 0 && self.fits_u32(value) {
            return value;
        }
        if r.shift == 0
            && let Word::Entry {
                table,
                width,
                signed: _,
                bias: 0,
            } = value
            && r.width == width
        {
            return Word::Entry {
                table,
                width,
                signed: false,
                bias: 0,
            };
        }
        self.unknown()
    }
    fn fits_u32(&self, value: Word) -> bool {
        matches!(value,Word::Linear {constant:0,term:Some((id,1))}
            if self.bounds.get(&id).is_some_and(|n|*n<=u64::from(u32::MAX)))
    }
    fn bounded_unknown(&mut self, maximum: u64) -> Word {
        let value = self.unknown();
        self.bounds.insert(self.fresh - 1, maximum);
        value
    }
    fn address(&mut self, a: Addressing, next: u64) -> Option<Word> {
        let mut value = Word::constant((a.displacement as u64).wrapping_add(if a.rip_relative {
            next
        } else {
            0
        }));
        if let Some(base) = a.base {
            value = value.add(self.registers[base as usize])?;
        }
        if let Some(index) = a.index {
            value = value.add(self.registers[index as usize].scale(u64::from(a.scale))?)?;
        }
        Some(value)
    }
    fn operand(&mut self, o: Operand, next: u64) -> Word {
        match o {
            Operand::Immediate(n) => Word::constant(n),
            Operand::Register(r) => self.register(r),
            Operand::Memory { address, width } => {
                if let Some(Word::Linear {
                    constant: table,
                    term: Some((id, stride)),
                }) = self.address(address, next)
                    && stride == width.bytes() as u64
                {
                    let key = (table, width.bits());
                    if let Some(limit) = self
                        .bounds
                        .get(&id)
                        .and_then(|n| n.checked_add(1))
                        .and_then(|n| usize::try_from(n).ok())
                    {
                        self.entry_limits.insert(key, limit);
                    } else {
                        self.entry_limits.remove(&key);
                    }
                    Word::Entry {
                        table,
                        width,
                        signed: false,
                        bias: 0,
                    }
                } else {
                    self.unknown()
                }
            }
        }
    }
    fn write(&mut self, r: Register, value: Word, raw_load: bool) {
        self.registers[r.index as usize] = if r.shift == 0 && r.width == Width::U64 {
            value
        } else if r.shift == 0 && r.width == Width::U32 {
            if let Some(n) = value.number() {
                Word::constant(n & Width::U32.mask())
            } else if self.fits_u32(value)
                || (raw_load
                    && matches!(
                        value,
                        Word::Entry {
                            width: Width::U32,
                            bias: 0,
                            ..
                        }
                    ))
            {
                value
            } else {
                self.unknown()
            }
        } else {
            self.unknown()
        };
    }
    fn observe(&mut self, i: DecodedInstruction) {
        let next = i.address + u64::from(i.size);
        let previous_comparison = self.comparison.take();
        match i.operation {
            Operation::Alu {
                kind: Alu::Cmp,
                destination: Operand::Register(r),
                source: Operand::Immediate(n),
            } => {
                self.comparison = Some((r, n & r.width.mask()));
            }
            Operation::Branch { condition, .. } => {
                if let Some((r, n)) = previous_comparison {
                    let bound = match condition {
                        7 => Some(n),
                        3 => n.checked_sub(1),
                        _ => None,
                    };
                    if let Some(bound) = bound {
                        let old = self.registers[r.index as usize];
                        let new = self.bounded_unknown(bound);
                        for value in &mut self.registers {
                            if *value == old {
                                *value = new;
                            }
                        }
                    }
                }
            }
            Operation::Nop
            | Operation::Alu {
                kind: Alu::Cmp | Alu::Test,
                ..
            } => {}
            Operation::Mov {
                destination: Operand::Register(r),
                source,
            } => {
                let value = self.operand(source, next);
                self.write(r, value, true);
            }
            Operation::Extend {
                destination,
                source,
                signed,
            } => {
                let mut value = self.operand(source, next);
                if let Word::Entry { signed: s, .. } = &mut value {
                    *s = signed;
                } else if signed
                    && let Some(n) = value.number()
                    && let Some(width) = source.width()
                {
                    let shift = 64 - width.bits();
                    value = Word::constant(((n << shift) as i64 >> shift) as u64);
                }
                self.write(destination, value, true);
            }
            Operation::Lea {
                destination,
                address,
            } => {
                let value = self
                    .address(address, next)
                    .unwrap_or_else(|| self.unknown());
                self.write(destination, value, false);
            }
            Operation::Alu {
                kind,
                destination: Operand::Register(r),
                source,
            } => {
                let a = self.register(r);
                let b = self.operand(source, next);
                let value = match kind {
                    Alu::And if a.number().is_none() && b.number().is_some() => {
                        Some(self.bounded_unknown(b.number().unwrap()))
                    }
                    Alu::Add => a.add(b),
                    Alu::Sub => b.scale(u64::MAX).and_then(|b| a.add(b)),
                    _ => match (a.number(), b.number()) {
                        (Some(a), Some(b)) => match kind {
                            Alu::And => Some(Word::constant(a & b)),
                            Alu::Or => Some(Word::constant(a | b)),
                            Alu::Xor => Some(Word::constant(a ^ b)),
                            _ => None,
                        },
                        _ => None,
                    },
                }
                .unwrap_or_else(|| self.unknown());
                self.write(r, value, false);
            }
            Operation::Shift {
                kind: Shift::Left,
                destination: Operand::Register(r),
                count: Operand::Immediate(count),
            } => {
                let value = self
                    .register(r)
                    .scale(1u64 << (count & 63))
                    .unwrap_or_else(|| self.unknown());
                self.write(r, value, false);
            }
            // Unmodeled writes invalidate the whole local interpretation.
            _ => {
                for r in 0..16 {
                    self.registers[r] = self.unknown();
                }
            }
        }
    }
}

/// Inspect a bounded contiguous window ending in an indirect jump. The caller
/// independently decodes targets and checks flags. Coverage stays open.
pub fn discover(
    window: &[DecodedInstruction],
    memory_base: u64,
    memory: &[u8],
    function: std::ops::Range<u64>,
) -> Option<Candidate> {
    if window.is_empty() || window.len() > MAX_WINDOW || function.start >= function.end {
        return None;
    }
    let register = |r: Register| r.index < 16 && r.shift < 64;
    let address = |a: Addressing| {
        a.base.is_none_or(|r| r < 16)
            && a.index.is_none_or(|r| r < 16)
            && matches!(a.scale, 1 | 2 | 4 | 8)
    };
    let operand = |o: Operand| match o {
        Operand::Register(r) => register(r),
        Operand::Memory { address: a, .. } => address(a),
        _ => true,
    };
    for i in window {
        if i.size == 0
            || i.size > 15
            || i.address < function.start
            || i.address
                .checked_add(u64::from(i.size))
                .is_none_or(|end| end > function.end)
        {
            return None;
        }
        let valid = match i.operation {
            Operation::Mov {
                destination,
                source,
            }
            | Operation::Alu {
                destination,
                source,
                ..
            } => operand(destination) && operand(source),
            Operation::Extend {
                destination,
                source,
                ..
            } => register(destination) && operand(source),
            Operation::Lea {
                destination,
                address: a,
            } => register(destination) && address(a),
            Operation::Shift {
                destination, count, ..
            } => operand(destination) && operand(count),
            Operation::IndirectJump(o) => operand(o),
            _ => true,
        };
        if !valid {
            return None;
        }
    }
    for pair in window.windows(2) {
        if pair[0].address.checked_add(u64::from(pair[0].size))? != pair[1].address {
            return None;
        }
    }
    let (branch, prefix) = window.split_last()?;
    let Operation::IndirectJump(operand) = branch.operation else {
        return None;
    };
    let mut values = Values::new();
    for &i in prefix {
        values.observe(i);
    }
    let next = branch.address.checked_add(u64::from(branch.size))?;
    let Word::Entry {
        table,
        width,
        signed,
        bias,
    } = values.operand(operand, next)
    else {
        return None;
    };
    let entry_limit_hint = values.entry_limits.get(&(table, width.bits())).copied();
    let limit = entry_limit_hint.unwrap_or(MAX_ENTRIES).min(MAX_ENTRIES);
    let mut entries = Vec::new();
    for index in 0..limit {
        let Some(address) = table.checked_add((index * width.bytes()) as u64) else {
            break;
        };
        let Some(offset) = address
            .checked_sub(memory_base)
            .and_then(|n| usize::try_from(n).ok())
        else {
            break;
        };
        let Some(bytes) = offset
            .checked_add(width.bytes())
            .and_then(|end| memory.get(offset..end))
        else {
            break;
        };
        let mut raw = [0u8; 8];
        raw[..width.bytes()].copy_from_slice(bytes);
        let raw = u64::from_le_bytes(raw);
        let value = if signed {
            let shift = 64 - width.bits();
            ((raw << shift) as i64 >> shift) as u64
        } else {
            raw
        };
        let target = bias.wrapping_add(value);
        if !function.contains(&target) {
            break;
        }
        entries.push(Entry { address, target });
    }
    (entries.len() >= 2).then_some(Candidate {
        branch: branch.address,
        table,
        width,
        signed,
        bias,
        reached_entry_limit: entries.len() == MAX_ENTRIES,
        entry_limit_hint,
        entries,
    })
}

pub fn to_json(tables: &[Candidate], diagnostics: &[(u64, String)]) -> Result<String, String> {
    if tables.len() > 8192
        || diagnostics.len() > 512
        || tables.iter().any(|t| t.entries.len() > MAX_ENTRIES)
    {
        return Err("jump table report collection limit".into());
    }
    let mut out = String::from(
        "{\"schema\":\"nirvana-jump-tables-v1\",\"coverage\":\"initial-image-candidates\",\"complete\":false,\"tables\":[",
    );
    for (i, t) in tables.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write!(out,"{{\"branch\":{},\"table\":{},\"width\":{},\"signed\":{},\"bias\":{},\"unknown_target\":true,\"reached_entry_limit\":{},\"entry_limit_hint\":{},\"entries\":[",t.branch,t.table,t.width.bytes(),t.signed,t.bias,t.reached_entry_limit,t.entry_limit_hint.map_or_else(||"null".into(),|n|n.to_string())).unwrap();
        for (j, e) in t.entries.iter().enumerate() {
            if j > 0 {
                out.push(',');
            }
            write!(out, "{{\"address\":{},\"target\":{}}}", e.address, e.target).unwrap();
            if out.len() > 16 * 1024 * 1024 {
                return Err("jump table report output limit".into());
            }
        }
        out.push_str("]}");
        if out.len() > 16 * 1024 * 1024 {
            return Err("jump table report output limit".into());
        }
    }
    out.push_str("],\"declined_functions\":[");
    for (i, (address, _)) in diagnostics.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write!(out, "{address}").unwrap();
    }
    out.push_str("]}\n");
    if out.len() > 16 * 1024 * 1024 {
        return Err("jump table report output limit".into());
    }
    Ok(out)
}
