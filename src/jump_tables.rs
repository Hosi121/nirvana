//! Initial-image jump-table candidates for instruction discovery. Candidates
//! retain an open residual and never replace executable target expressions.

use crate::ir::{BinaryOp, Expr, Place, Reg, Width};
use crate::x86::{self, Addressing, Alu, DecodedInstruction, Operand, Operation, Register, Shift};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

mod context;
pub(crate) use context::merge as merge_candidate;
pub use context::{
    ContextSearch, MAX_CONTEXT_INSTRUCTIONS, MAX_CONTEXT_PATHS, MAX_CONTEXT_WORK, discover_cfg,
};

pub const MAX_WINDOW: usize = 24;
pub const MAX_ENTRIES: usize = 256;
pub const MAX_READ_SITES: usize = 64;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReadSite {
    pub instruction: u64,
    pub next: u64,
    pub address: Addressing,
    pub width: Width,
}
impl ReadSite {
    /// Pure pre-instruction guest address. Rendering a snapshot adds no RAM read.
    pub fn address_expr(&self) -> Option<Expr> {
        let a = self.address;
        if a.base.is_some_and(|r| r >= 16)
            || a.index.is_some_and(|r| r >= 16)
            || !matches!(a.scale, 1 | 2 | 4 | 8)
        {
            return None;
        }
        let mut e = Expr::Const((a.displacement as u64).wrapping_add(if a.rip_relative {
            self.next
        } else {
            0
        }));
        if let Some(base) = a.base {
            e = Expr::binary(BinaryOp::Add, e, Expr::Register(Reg(base as usize)));
        }
        if let Some(index) = a.index {
            e = Expr::binary(
                BinaryOp::Add,
                e,
                Expr::binary(
                    BinaryOp::Mul,
                    Expr::Register(Reg(index as usize)),
                    Expr::Const(u64::from(a.scale)),
                ),
            );
        }
        Some(e)
    }
}

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
    /// Bounded provenance of the table value, retained across copies/spills.
    pub read_sites: Vec<ReadSite>,
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
        read: ReadSite,
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
                    read,
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
                    read,
                },
            ) => Some(Self::Entry {
                table,
                width,
                signed,
                bias: bias.wrapping_add(constant),
                read,
            }),
            _ => None,
        }
    }
}

struct Values {
    registers: [Word; 16],
    low32: [Word; 16],
    fresh: u32,
    bounds: BTreeMap<u32, u64>,
    entry_limits: BTreeMap<(u64, u32), usize>,
    comparison: Option<(Word, u64)>,
    spills: Vec<Spill>,
    current_pc: u64,
}

#[derive(Clone, Copy)]
struct Spill {
    address: Word,
    width: Width,
    value: Word,
}

const MAX_SPILLS: usize = 32;

// Equal affine terms cancel modulo 2^64. Both forward and reverse distances
// must leave room for the other byte interval. Different bases may alias.
fn disjoint(a: Word, a_width: Width, b: Word, b_width: Width) -> bool {
    match (a, b) {
        (
            Word::Linear {
                constant: a,
                term: x,
            },
            Word::Linear {
                constant: b,
                term: y,
            },
        ) if x == y => {
            b.wrapping_sub(a) >= a_width.bytes() as u64
                && a.wrapping_sub(b) >= b_width.bytes() as u64
        }
        _ => false,
    }
}

impl Values {
    fn new() -> Self {
        let mut values = Self {
            registers: std::array::from_fn(|i| Word::Linear {
                constant: 0,
                term: Some((i as u32, 1)),
            }),
            low32: [Word::constant(0); 16],
            fresh: 16,
            bounds: BTreeMap::new(),
            entry_limits: BTreeMap::new(),
            comparison: None,
            spills: Vec::new(),
            current_pc: 0,
        };
        for r in 0..16 {
            values.low32[r] = values.bounded_unknown(u64::from(u32::MAX));
        }
        values
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
                read,
            } = value
            && r.width == width
        {
            return Word::Entry {
                table,
                width,
                signed: false,
                bias: 0,
                read,
            };
        }
        if r.width == Width::U32 && r.shift == 0 {
            return self.low32[r.index as usize];
        }
        self.unknown()
    }
    fn fits_u32(&self, value: Word) -> bool {
        self.maximum(value).is_some_and(|n| n <= Width::U32.mask())
    }
    fn maximum(&self, value: Word) -> Option<u64> {
        match value {
            Word::Linear {
                constant,
                term: None,
            } => Some(constant),
            Word::Linear {
                constant: 0,
                term: Some((id, 1)),
            } => self.bounds.get(&id).copied(),
            _ => None,
        }
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
                let effective = self.address(address, next);
                if let Some(effective) = effective
                    && let Some(spill) = self
                        .spills
                        .iter()
                        .find(|s| s.address == effective && s.width == width)
                {
                    return spill.value;
                }
                if let Some(Word::Linear {
                    constant: table,
                    term: Some((id, stride)),
                }) = effective
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
                        read: ReadSite {
                            instruction: self.current_pc,
                            next,
                            address,
                            width,
                        },
                    }
                } else {
                    self.unknown()
                }
            }
        }
    }

    fn store(&mut self, address: Addressing, width: Width, value: Word, next: u64) {
        let Some(effective @ Word::Linear { .. }) = self.address(address, next) else {
            self.spills.clear();
            return;
        };
        self.spills
            .retain(|s| disjoint(s.address, s.width, effective, width));
        // Narrow stores share identity when the value fits. Otherwise record
        // a fresh value with the stored width's range.
        let value = if width == Width::U64 {
            value
        } else if let Some(n) = value.number() {
            Word::constant(n & width.mask())
        } else if self.maximum(value).is_some_and(|n| n <= width.mask()) {
            value
        } else {
            self.bounded_unknown(width.mask())
        };
        if self.spills.len() == MAX_SPILLS {
            self.spills.remove(0);
        }
        self.spills.push(Spill {
            address: effective,
            width,
            value,
        });
    }
    fn write(&mut self, r: Register, value: Word, raw_load: bool) {
        let value = if r.shift == 0 && r.width == Width::U64 {
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
                self.bounded_unknown(u64::from(u32::MAX))
            }
        } else {
            self.unknown()
        };
        self.registers[r.index as usize] = value;
        self.low32[r.index as usize] = if let Some(n) = value.number() {
            Word::constant(n & Width::U32.mask())
        } else if self.fits_u32(value) {
            value
        } else if let Word::Entry {
            table,
            width: Width::U32,
            bias: 0,
            read,
            ..
        } = value
        {
            Word::Entry {
                table,
                width: Width::U32,
                signed: false,
                bias: 0,
                read,
            }
        } else {
            self.bounded_unknown(u64::from(u32::MAX))
        };
    }
    fn forget(&mut self, index: u8) {
        let unknown = self.unknown();
        self.write(
            Register {
                index,
                width: Width::U64,
                shift: 0,
            },
            unknown,
            false,
        );
    }
    fn observe_effects(
        &mut self,
        instruction: DecodedInstruction,
        comparison: Option<(Word, u64)>,
    ) {
        let Ok(ir) = x86::lift_instruction(instruction) else {
            // Calls and effects outside scalar IR retain the opaque boundary.
            self.spills.clear();
            self.comparison = None;
            for r in 0..16 {
                self.forget(r);
            }
            return;
        };
        let mut clobbered = [false; 16];
        let mut flags_written = false;
        for assignment in ir.assignments {
            match assignment.destination {
                Place::Register(r) if r.0 < 16 => clobbered[r.0] = true,
                Place::Register(r) if (x86::CF..=x86::PF).contains(&r.0) => flags_written = true,
                Place::Memory { .. } => self.spills.clear(),
                _ => {}
            }
        }
        for (r, written) in clobbered.into_iter().enumerate() {
            if written {
                self.forget(r as u8);
            }
        }
        self.comparison = if flags_written { None } else { comparison };
    }
    fn observe(&mut self, i: DecodedInstruction, successor: u64) {
        self.current_pc = i.address;
        let next = i.address + u64::from(i.size);
        let previous_comparison = self.comparison.take();
        match i.operation {
            Operation::Alu {
                kind: Alu::Cmp,
                destination: Operand::Register(r),
                source: Operand::Immediate(n),
            } => {
                self.comparison = Some((self.register(r), n & r.width.mask()));
            }
            Operation::Branch { condition, target } => {
                if let Some((value, n)) = previous_comparison {
                    let bound = match (condition, successor == target, target != next) {
                        (7, false, true) | (6, true, true) => Some(n),
                        (3, false, true) | (2, true, true) => n.checked_sub(1),
                        _ => None,
                    };
                    if let (
                        Some(bound),
                        Word::Linear {
                            constant: 0,
                            term: Some((id, 1)),
                        },
                    ) = (bound, value)
                    {
                        self.bounds
                            .entry(id)
                            .and_modify(|n| *n = (*n).min(bound))
                            .or_insert(bound);
                    }
                    self.comparison = previous_comparison;
                }
            }
            Operation::Nop | Operation::Jump(_) => self.comparison = previous_comparison,
            Operation::Alu {
                kind: Alu::Cmp | Alu::Test,
                ..
            } => {}
            Operation::Mov {
                destination: Operand::Register(r),
                source,
            } => {
                let value = self.operand(source, next);
                self.write(r, value, true);
                self.comparison = previous_comparison;
            }
            Operation::Mov {
                destination: Operand::Memory { address, width },
                source,
            } => {
                let value = self.operand(source, next);
                self.store(address, width, value, next);
                self.comparison = previous_comparison;
            }
            Operation::Extend {
                destination,
                source,
                signed,
            } => {
                let mut value = self.operand(source, next);
                if let Word::Entry { signed: s, .. } = &mut value {
                    *s = signed;
                } else if signed && let Some(width) = source.width() {
                    if let Some(n) = value.number() {
                        let shift = 64 - width.bits();
                        value = Word::constant(((n << shift) as i64 >> shift) as u64);
                    } else if self
                        .maximum(value)
                        .is_none_or(|n| n >= (1u64 << (width.bits() - 1)))
                    {
                        // Sign extension may change a zero-extended pointer or
                        // index. Share its identity only when its sign bit is clear.
                        value = self.unknown();
                    }
                }
                self.write(destination, value, true);
                self.comparison = previous_comparison;
            }
            Operation::Lea {
                destination,
                address,
            } => {
                let value = self
                    .address(address, next)
                    .unwrap_or_else(|| self.unknown());
                self.write(destination, value, false);
                self.comparison = previous_comparison;
            }
            Operation::Alu {
                kind,
                destination: Operand::Register(r),
                source,
            } => {
                let a = self.register(r);
                let b = self.operand(source, next);
                // SUB defines the same comparison flags as CMP on its inputs.
                // A saved copy/reload of the pre-subtraction value can carry
                // the unsigned guard even though the destination is changed.
                if kind == Alu::Sub
                    && let Some(n) = b.number()
                {
                    self.comparison = Some((a, n & r.width.mask()));
                }
                let value = match kind {
                    Alu::And if a.number().is_none() && b.number().is_some() => {
                        Some(self.bounded_unknown(b.number().unwrap() & r.width.mask()))
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
                    .scale(1u64 << (count & if r.width == Width::U64 { 63 } else { 31 }))
                    .unwrap_or_else(|| self.unknown());
                self.write(r, value, false);
            }
            // Reuse executable IR's write set for operations whose result is
            // opaque here. Unchanged registers and memory keep their facts.
            _ => self.observe_effects(i, previous_comparison),
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
    for pair in window.windows(2) {
        if pair[0].address.checked_add(u64::from(pair[0].size))? != pair[1].address {
            return None;
        }
    }
    discover_path(window, memory_base, memory, function)
}

fn discover_path(
    path: &[DecodedInstruction],
    memory_base: u64,
    memory: &[u8],
    function: std::ops::Range<u64>,
) -> Option<Candidate> {
    let register = |r: Register| {
        r.index < 16 && (r.shift == 0 || (r.width == Width::U8 && r.shift == 8 && r.index < 4))
    };
    let address = |a: Addressing| {
        a.base.is_none_or(|r| r < 16)
            && a.index.is_none_or(|r| r < 16)
            && matches!(a.scale, 1 | 2 | 4 | 8)
    };
    let operand = |o: Operand| match o {
        Operand::Register(r) => register(r),
        Operand::Memory { address: a, .. } => address(a),
        Operand::Immediate(_) => true,
    };
    for i in path {
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
            }
            | Operation::Movbe {
                destination,
                source,
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
            }
            | Operation::Rotate {
                destination, count, ..
            } => operand(destination) && operand(count),
            Operation::Unary { destination, .. } => operand(destination),
            Operation::ByteSwap { destination } | Operation::Pop(destination) => {
                register(destination)
            }
            Operation::DoubleShift {
                destination,
                source,
                ..
            } => operand(destination) && register(source),
            Operation::Imul {
                destination,
                left,
                right,
            } => register(destination) && operand(left) && operand(right),
            Operation::BitTest { base, index } => register(base) && operand(index),
            Operation::Exchange { left, right } => operand(left) && register(right),
            Operation::Mul { source }
            | Operation::Push(source)
            | Operation::IndirectCall(source)
            | Operation::IndirectJump(source) => operand(source),
            Operation::Set {
                condition,
                destination,
            } => condition < 16 && operand(destination),
            Operation::Cmov {
                condition,
                destination,
                source,
            } => condition < 16 && register(destination) && operand(source),
            Operation::Branch { condition, .. } => condition < 16,
            Operation::Nop
            | Operation::Leave
            | Operation::Call(_)
            | Operation::Jump(_)
            | Operation::Return { .. } => true,
        };
        if !valid {
            return None;
        }
    }
    for pair in path.windows(2) {
        let next = pair[0].address.checked_add(u64::from(pair[0].size))?;
        let follows = match pair[0].operation {
            Operation::Jump(target) => pair[1].address == target,
            Operation::Branch { target, .. } => {
                pair[1].address == next || pair[1].address == target
            }
            Operation::Return { .. } | Operation::IndirectJump(_) => false,
            _ => pair[1].address == next,
        };
        if !follows {
            return None;
        }
    }
    let (branch, prefix) = path.split_last()?;
    let Operation::IndirectJump(operand) = branch.operation else {
        return None;
    };
    let mut values = Values::new();
    for (i, successor) in prefix.iter().zip(&path[1..]) {
        values.observe(*i, successor.address);
    }
    let next = branch.address.checked_add(u64::from(branch.size))?;
    values.current_pc = branch.address;
    let Word::Entry {
        table,
        width,
        signed,
        bias,
        read,
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
        read_sites: vec![read],
        entries,
    })
}

pub fn to_json(tables: &[Candidate], diagnostics: &[(u64, String)]) -> Result<String, String> {
    to_json_with_context_limits(tables, diagnostics, &[])
}

pub fn to_json_with_context_limits(
    tables: &[Candidate],
    diagnostics: &[(u64, String)],
    context_limits: &[u64],
) -> Result<String, String> {
    if tables.len() > 8192
        || diagnostics.len() > 512
        || context_limits.len() > 65_536
        || tables
            .iter()
            .any(|t| t.entries.len() > MAX_ENTRIES || t.read_sites.len() > MAX_READ_SITES)
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
        out.push_str("],\"read_sites\":[");
        for (j, site) in t.read_sites.iter().enumerate() {
            if j > 0 {
                out.push(',');
            }
            let a = site.address;
            write!(out,"{{\"instruction\":{},\"next\":{},\"width\":{},\"base\":{},\"index\":{},\"scale\":{},\"displacement\":{},\"rip_relative\":{}}}",site.instruction,site.next,site.width.bytes(),a.base.map_or_else(||"null".into(),|n|n.to_string()),a.index.map_or_else(||"null".into(),|n|n.to_string()),a.scale,a.displacement,a.rip_relative).unwrap();
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
    out.push_str("],\"context_limited_branches\":[");
    for (i, address) in context_limits.iter().enumerate() {
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
