//! Selected ELF64/x86-64 functions and their bounded initial guest image.
//!
//! PT_LOAD determines guest bytes (including zeroed BSS); PT_DYNAMIC determines
//! relocations. The modeled external function is puts. Dependency loading,
//! startup, TLS and IFUNC execution lie outside this selected-function model.

use crate::elf::FunctionImage;
use crate::loader::{LinkedImage, LoadedSection};
use std::collections::BTreeMap;
use std::fmt;

mod unwind;

const MAX_MEMORY: u64 = 16 * 1024 * 1024;
const MAX_FUNCTION: u64 = 1024 * 1024;
const MAX_TABLE: u64 = 262_144;
const MAX_WORK: usize = 8_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LinkedOptions {
    pub load_bias: u64,
    pub stack_size: usize,
}
impl Default for LinkedOptions {
    fn default() -> Self {
        Self {
            load_bias: 0x10000,
            stack_size: 65536,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportSlot {
    pub name: String,
    pub symbol_kind: u8,
    /// Runtime address of the relocated pointer field, not its contents.
    pub address: u64,
    pub width: u64,
    pub kind: u32,
    pub modeled: bool,
    pub addend: i64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FunctionOrigin {
    Symbol,
    /// File offset of an FDE; its contiguous region can be a function fragment.
    Unwind {
        record_offset: u64,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionSymbol {
    pub name: String,
    pub address: u64,
    pub size: u64,
    pub origin: FunctionOrigin,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryImage {
    pub image: LinkedImage,
    pub elf_type: u16,
    pub bias: u64,
    pub imports: Vec<ImportSlot>,
    pub functions: Vec<FunctionSymbol>,
    executable: Vec<(u64, u64)>,
}

impl BinaryImage {
    /// Recognize exactly an executable `jmp *disp32(%rip)`, optionally preceded
    /// by ENDBR64. The computed pointer must be an actual dynamic import field.
    /// No PLT section name, presumed stride or lazy-linker convention is trusted.
    pub fn plt_slot(&self, entry: u64) -> Option<&ImportSlot> {
        let read = |address: u64, size: u64| {
            if !self.executable.iter().any(|&(start, end)| {
                address >= start && address.checked_add(size).is_some_and(|a| a <= end)
            }) {
                return None;
            }
            let start = usize::try_from(address.checked_sub(self.image.memory_base)?).ok()?;
            self.image
                .memory
                .get(start..start.checked_add(size as usize)?)
        };
        let mut jump = entry;
        if read(entry, 4)? == [0xf3, 0x0f, 0x1e, 0xfa] {
            jump = entry.checked_add(4)?;
        }
        let bytes = read(jump, 6)?;
        if bytes[..2] != [0xff, 0x25] {
            return None;
        }
        let displacement = i32::from_le_bytes(bytes[2..6].try_into().ok()?);
        let slot =
            u64::try_from(i128::from(jump.checked_add(6)?) + i128::from(displacement)).ok()?;
        self.import_at(slot)
    }

    pub fn import_at(&self, address: u64) -> Option<&ImportSlot> {
        self.imports
            .iter()
            .find(|import| import.address == address && import.width == 8)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BinaryError {
    Invalid(&'static str),
    Unsupported(&'static str),
    Limit(&'static str),
    MissingFunction(String),
    AmbiguousFunction(String),
    ZeroSizedFunction(String),
    MissingFunctionAddress(u64),
    AmbiguousFunctionAddress(u64),
    Unwind(crate::eh_frame::Error),
    Relocation {
        address: u64,
        kind: u32,
        reason: &'static str,
    },
}
impl fmt::Display for BinaryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(s) => write!(f, "invalid linked ELF: {s}"),
            Self::Unsupported(s) => write!(f, "unsupported linked ELF: {s}"),
            Self::Limit(s) => write!(f, "linked ELF resource limit: {s}"),
            Self::MissingFunction(s) => write!(f, "no defined STT_FUNC symbol named {s:?}"),
            Self::AmbiguousFunction(s) => write!(f, "ambiguous STT_FUNC symbol named {s:?}"),
            Self::ZeroSizedFunction(s) => write!(f, "function {s:?} has no declared size"),
            Self::MissingFunctionAddress(a) => write!(f, "no bounded code region starts at {a:#x}"),
            Self::AmbiguousFunctionAddress(a) => write!(f, "conflicting code regions at {a:#x}"),
            Self::Unwind(e) => write!(f, "linked ELF {e}"),
            Self::Relocation {
                address,
                kind,
                reason,
            } => write!(f, "linked ELF relocation {kind} at {address:#x}: {reason}"),
        }
    }
}
impl std::error::Error for BinaryError {}
type Result<T> = std::result::Result<T, BinaryError>;
fn invalid(reason: &'static str) -> BinaryError {
    BinaryError::Invalid(reason)
}
fn unsupported(reason: &'static str) -> BinaryError {
    BinaryError::Unsupported(reason)
}
fn end(start: u64, size: u64) -> Result<u64> {
    start
        .checked_add(size)
        .ok_or_else(|| invalid("address or range overflow"))
}
fn range(data: &[u8], start: u64, size: u64) -> Result<&[u8]> {
    let stop = end(start, size)?;
    let start = usize::try_from(start).map_err(|_| invalid("offset does not fit host"))?;
    let stop = usize::try_from(stop).map_err(|_| invalid("range does not fit host"))?;
    data.get(start..stop)
        .ok_or_else(|| invalid("range extends beyond file"))
}
fn array<const N: usize>(data: &[u8], start: u64) -> Result<[u8; N]> {
    Ok(range(data, start, N as u64)?
        .try_into()
        .expect("checked range"))
}
fn u16_at(data: &[u8], start: u64) -> Result<u16> {
    Ok(u16::from_le_bytes(array(data, start)?))
}
fn u32_at(data: &[u8], start: u64) -> Result<u32> {
    Ok(u32::from_le_bytes(array(data, start)?))
}
fn u64_at(data: &[u8], start: u64) -> Result<u64> {
    Ok(u64::from_le_bytes(array(data, start)?))
}
fn aligned(address: u64) -> Result<u64> {
    Ok(end(address, 15)? & !15)
}
fn table_count(size: u64, stride: u64) -> Result<u64> {
    if !size.is_multiple_of(stride) {
        return Err(invalid("incomplete table entry"));
    }
    let count = size / stride;
    if count > MAX_TABLE {
        return Err(BinaryError::Limit("too many table entries"));
    }
    Ok(count)
}
struct Work(usize);
impl Work {
    fn use_bytes(&mut self, amount: usize) -> Result<()> {
        self.0 = self
            .0
            .checked_sub(amount)
            .ok_or(BinaryError::Limit("metadata work exceeds bound"))?;
        Ok(())
    }
    fn name<'a>(&mut self, data: &'a [u8], offset: u32) -> Result<&'a str> {
        let tail = data
            .get(offset as usize..)
            .ok_or_else(|| invalid("string offset outside table"))?;
        let scan = tail.len().min(self.0);
        let length = tail[..scan].iter().position(|&x| x == 0).ok_or_else(|| {
            if scan < tail.len() {
                BinaryError::Limit("metadata work exceeds bound")
            } else {
                invalid("unterminated symbol name")
            }
        })?;
        self.use_bytes(length + 1)?;
        std::str::from_utf8(&tail[..length]).map_err(|_| invalid("symbol name is not UTF-8"))
    }
}

#[derive(Clone, Copy)]
struct Segment {
    index: usize,
    kind: u32,
    flags: u32,
    offset: u64,
    address: u64,
    files: u64,
    memory: u64,
}
struct Mapping<'a> {
    data: &'a [u8],
    loads: Vec<Segment>,
}
impl<'a> Mapping<'a> {
    fn contains(&self, address: u64, size: u64, executable: bool) -> bool {
        address.checked_add(size).is_some_and(|stop| {
            self.loads.iter().any(|s| {
                (!executable || s.flags & 1 != 0)
                    && address >= s.address
                    && stop <= s.address + s.memory
            })
        })
    }
    fn offset(&self, address: u64, size: u64) -> Result<u64> {
        let stop = end(address, size)?;
        let segment = self
            .loads
            .iter()
            .find(|s| address >= s.address && stop <= s.address + s.files)
            .ok_or_else(|| invalid("metadata or function is not file-backed PT_LOAD bytes"))?;
        end(segment.offset, address - segment.address)
    }
    fn bytes(&self, address: u64, size: u64) -> Result<&'a [u8]> {
        range(self.data, self.offset(address, size)?, size)
    }
}
#[derive(Clone, Copy)]
struct Section {
    name: u32,
    kind: u32,
    flags: u64,
    address: u64,
    offset: u64,
    size: u64,
    link: u32,
    stride: u64,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Symbol {
    name: u32,
    info: u8,
    section: u16,
    value: u64,
    size: u64,
}
impl Symbol {
    fn parse(data: &[u8]) -> Result<Self> {
        Ok(Self {
            name: u32_at(data, 0)?,
            info: data[4],
            section: u16_at(data, 6)?,
            value: u64_at(data, 8)?,
            size: u64_at(data, 16)?,
        })
    }
    fn kind(self) -> u8 {
        self.info & 15
    }
}

fn sections(data: &[u8]) -> Result<Vec<Section>> {
    let offset = u64_at(data, 40)?;
    let count = u16_at(data, 60)? as u64;
    if offset == 0 && count == 0 {
        if u16_at(data, 62)? != 0 {
            return Err(invalid("section name index without section table"));
        }
        return Ok(Vec::new());
    }
    if offset == 0 || count == 0 {
        return Err(unsupported("extended or missing section table"));
    }
    if count > 4096 {
        return Err(BinaryError::Limit("too many section headers"));
    }
    if u16_at(data, 58)? != 64 {
        return Err(invalid("section header stride is not 64"));
    }
    range(data, offset, count * 64)?;
    let names = u16_at(data, 62)? as u64;
    if names >= count {
        return Err(invalid("invalid section name table index"));
    }
    let mut sections = Vec::new();
    for index in 0..count {
        let header = range(data, offset + index * 64, 64)?;
        let section = Section {
            name: u32_at(header, 0)?,
            kind: u32_at(header, 4)?,
            flags: u64_at(header, 8)?,
            address: u64_at(header, 16)?,
            offset: u64_at(header, 24)?,
            size: u64_at(header, 32)?,
            link: u32_at(header, 40)?,
            stride: u64_at(header, 56)?,
        };
        if section.kind != 8 && section.kind != 0 {
            range(data, section.offset, section.size)?;
        }
        sections.push(section);
    }
    Ok(sections)
}

struct Dynamic {
    tags: BTreeMap<u64, u64>,
    count: Option<u64>,
}
impl Dynamic {
    fn tag(&self, tag: u64) -> Option<u64> {
        self.tags.get(&tag).copied()
    }
    fn required(&self, tag: u64) -> Result<u64> {
        self.tag(tag)
            .ok_or_else(|| invalid("missing required dynamic tag"))
    }
    fn symbol<'a>(&self, mapping: &Mapping<'a>, index: u64) -> Result<Symbol> {
        let count = self
            .count
            .ok_or_else(|| unsupported("dynamic symbol table has no proven bound"))?;
        if index >= MAX_TABLE || index >= count {
            return Err(invalid("dynamic symbol index outside table"));
        }
        if self.required(11)? != 24 {
            return Err(invalid("DT_SYMENT is not 24"));
        }
        Symbol::parse(mapping.bytes(end(self.required(6)?, index * 24)?, 24)?)
    }
    fn names<'a>(&self, mapping: &Mapping<'a>) -> Result<&'a [u8]> {
        let size = self.required(10)?;
        if size > MAX_MEMORY {
            return Err(BinaryError::Limit("dynamic strings exceed 16 MiB"));
        }
        let names = mapping.bytes(self.required(5)?, size)?;
        if names.first() != Some(&0) || names.last() != Some(&0) {
            return Err(invalid("dynamic string table lacks boundary NUL"));
        }
        Ok(names)
    }
}

fn dynamic(
    mapping: &Mapping<'_>,
    sections: &[Section],
    segment: Option<Segment>,
    work: &mut Work,
) -> Result<Dynamic> {
    let mut dynamic = Dynamic {
        tags: BTreeMap::new(),
        count: None,
    };
    let Some(segment) = segment else {
        return Ok(dynamic);
    };
    if segment.files > MAX_FUNCTION || segment.files % 16 != 0 {
        return Err(invalid("invalid PT_DYNAMIC size"));
    }
    if mapping.offset(segment.address, segment.files)? != segment.offset {
        return Err(invalid("PT_DYNAMIC disagrees with PT_LOAD file mapping"));
    }
    let bytes = mapping.bytes(segment.address, segment.files)?;
    let mut terminated = false;
    for entry in bytes.chunks_exact(16) {
        work.use_bytes(16)?;
        let tag = u64_at(entry, 0)?;
        if tag == 0 {
            terminated = true;
            break;
        }
        let value = u64_at(entry, 8)?;
        // Repeated DT_NEEDED/DT_AUXILIARY/DT_FILTER describe dependencies, which
        // are never opened here. All actual relocation tables remain checked.
        if matches!(tag, 1 | 0x7fff_fffd | 0x7fff_ffff) {
            continue;
        }
        if dynamic.tags.insert(tag, value).is_some() {
            return Err(invalid("duplicate dynamic tag"));
        }
        if matches!(tag, 17..=19 | 35..=37 | 0x6000_000f..=0x6000_0012) {
            return Err(unsupported("REL, RELR or packed dynamic relocations"));
        }
    }
    if !terminated {
        return Err(invalid("PT_DYNAMIC lacks DT_NULL"));
    }
    if dynamic.tag(6).is_some() {
        if dynamic.required(11)? != 24 {
            return Err(invalid("DT_SYMENT is not 24"));
        }
        dynamic.names(mapping)?;
    }
    if let Some(address) = dynamic.tag(4) {
        let header = mapping.bytes(address, 8)?;
        let buckets = u32_at(header, 0)? as u64;
        let count = u32_at(header, 4)? as u64;
        if buckets == 0 || count == 0 || buckets > MAX_TABLE || count > MAX_TABLE {
            return Err(invalid("invalid DT_HASH dimensions"));
        }
        let bytes = mapping.bytes(address, 8 + (buckets + count) * 4)?;
        work.use_bytes(bytes.len())?;
        for entry in bytes[8..].chunks_exact(4) {
            if u32_at(entry, 0)? as u64 >= count {
                return Err(invalid("DT_HASH index outside symbol table"));
            }
        }
        dynamic.count = Some(count);
    }
    if let Some(address) = dynamic.tag(0x6fff_fef5) {
        let header = mapping.bytes(address, 16)?;
        let buckets = u32_at(header, 0)? as u64;
        let first = u32_at(header, 4)? as u64;
        let bloom = u32_at(header, 8)? as u64;
        if buckets == 0
            || buckets > MAX_TABLE
            || first > MAX_TABLE
            || bloom == 0
            || bloom > MAX_TABLE
            || !bloom.is_power_of_two()
        {
            return Err(invalid("invalid DT_GNU_HASH dimensions"));
        }
        let bucket_address = end(address, 16 + bloom * 8)?;
        let bucket_bytes = mapping.bytes(bucket_address, buckets * 4)?;
        work.use_bytes(bucket_bytes.len())?;
        let mut last = 0;
        for entry in bucket_bytes.chunks_exact(4) {
            let index = u32_at(entry, 0)? as u64;
            if index != 0 && (index < first || index >= MAX_TABLE) {
                return Err(invalid("invalid GNU hash bucket"));
            }
            last = last.max(index);
        }
        let count = if last == 0 {
            // With no hashed exports GNU ld may leave undefined symbols after
            // symoffset. An empty GNU hash does not establish their count.
            None
        } else {
            let chains = end(bucket_address, buckets * 4)?;
            let mut index = last;
            loop {
                if index >= MAX_TABLE {
                    return Err(BinaryError::Limit("GNU hash chain exceeds symbol bound"));
                }
                work.use_bytes(4)?;
                let value = u32_at(mapping.bytes(end(chains, (index - first) * 4)?, 4)?, 0)?;
                index += 1;
                if value & 1 != 0 {
                    break Some(index);
                }
            }
        };
        if let Some(count) = count {
            if dynamic.count.is_some_and(|old| old != count) {
                return Err(invalid("dynamic hash tables disagree on symbol count"));
            }
            dynamic.count = Some(count);
        }
    }
    // An empty GNU hash does not count trailing undefined symbols. A section
    // extent can establish that bound only when its virtual and file addresses
    // agree exactly with DT_SYMTAB; section names never identify dynamic tables.
    if let Some(address) = dynamic.tag(6) {
        for section in sections
            .iter()
            .filter(|s| s.kind == 11 && s.address == address)
        {
            if section.stride != 24 || mapping.offset(address, section.size)? != section.offset {
                return Err(invalid("dynamic symbol section disagrees with DT_SYMTAB"));
            }
            let count = table_count(section.size, 24)?;
            if count == 0 || dynamic.count.is_some_and(|old| old != count) {
                return Err(invalid("dynamic symbol table bounds disagree"));
            }
            dynamic.count = Some(count);
        }
    }
    if let Some(count) = dynamic.count {
        mapping.bytes(dynamic.required(6)?, count * 24)?;
    }
    Ok(dynamic)
}

fn select_function(
    mapping: &Mapping<'_>,
    sections: &[Section],
    dynamic: &Dynamic,
    name: Option<&str>,
    work: &mut Work,
) -> Result<(Option<Symbol>, Vec<FunctionSymbol>)> {
    let mut selected: Option<Symbol> = None;
    let mut functions = BTreeMap::<u64, FunctionSymbol>::new();
    let mut accept =
        |symbol: Symbol, names: &[u8], section_check: bool, work: &mut Work| -> Result<()> {
            if symbol.section == 0 {
                return Ok(());
            }
            let symbol_name = work.name(names, symbol.name)?;
            let wanted = name == Some(symbol_name);
            if !wanted
                && (symbol.kind() != 2
                    || symbol.size == 0
                    || symbol.size > MAX_FUNCTION
                    || symbol.section >= 0xff00
                    || !mapping.contains(symbol.value, symbol.size, true))
            {
                return Ok(());
            }
            if symbol.kind() == 10 {
                return Err(unsupported("selected IFUNC function"));
            }
            if symbol.kind() != 2 {
                return Ok(());
            }
            if symbol.size == 0 {
                return Err(BinaryError::ZeroSizedFunction(symbol_name.to_owned()));
            }
            if symbol.size > MAX_FUNCTION {
                return Err(BinaryError::Limit("selected function exceeds 1 MiB"));
            }
            if symbol.section >= 0xff00 {
                return Err(unsupported("reserved selected symbol section"));
            }
            if !mapping.contains(symbol.value, symbol.size, true) {
                return Err(invalid(
                    "selected function is not contained in executable PT_LOAD",
                ));
            }
            mapping.bytes(symbol.value, symbol.size)?;
            if section_check {
                let section = sections
                    .get(symbol.section as usize)
                    .ok_or_else(|| invalid("selected symbol section index outside table"))?;
                if section.flags & 6 != 6
                    || section.kind != 1
                    || symbol.value < section.address
                    || end(symbol.value, symbol.size)? > end(section.address, section.size)?
                {
                    return Err(invalid(
                        "selected function is not contained in allocated executable section",
                    ));
                }
                if end(section.offset, symbol.value - section.address)?
                    != mapping.offset(symbol.value, symbol.size)?
                {
                    return Err(invalid(
                        "selected section disagrees with PT_LOAD file mapping",
                    ));
                }
            }
            if wanted
                && selected.is_some_and(|old| {
                    old.value != symbol.value
                        || old.size != symbol.size
                        || old.section != symbol.section
                })
            {
                return Err(BinaryError::AmbiguousFunction(symbol_name.to_owned()));
            }
            if let Some(old) = functions.get(&symbol.value)
                && old.size != symbol.size
            {
                return Err(BinaryError::AmbiguousFunction(symbol_name.to_owned()));
            }
            functions
                .entry(symbol.value)
                .or_insert_with(|| FunctionSymbol {
                    name: symbol_name.to_owned(),
                    address: symbol.value,
                    size: symbol.size,
                    origin: FunctionOrigin::Symbol,
                });
            if functions.len() > 4096 {
                return Err(BinaryError::Limit("function catalog exceeds 4096 entries"));
            }
            if wanted {
                selected = Some(symbol);
            }
            Ok(())
        };
    for table in sections.iter().filter(|s| matches!(s.kind, 2 | 11)) {
        if table.stride != 24 {
            return Err(invalid("symbol table stride is not 24"));
        }
        let count = table_count(table.size, 24)?;
        let names = sections
            .get(table.link as usize)
            .filter(|s| s.kind == 3)
            .ok_or_else(|| invalid("symbol table does not link to a string table"))?;
        if names.size > MAX_MEMORY {
            return Err(BinaryError::Limit("symbol strings exceed 16 MiB"));
        }
        let names = range(mapping.data, names.offset, names.size)?;
        if names.first() != Some(&0) || names.last() != Some(&0) {
            return Err(invalid("symbol string table lacks boundary NUL"));
        }
        for index in 0..count {
            work.use_bytes(24)?;
            let symbol = Symbol::parse(range(mapping.data, table.offset + index * 24, 24)?)?;
            accept(symbol, names, true, work)?;
        }
    }
    if let Some(count) = dynamic.count {
        let names = dynamic.names(mapping)?;
        for index in 0..count {
            work.use_bytes(24)?;
            let symbol = dynamic.symbol(mapping, index)?;
            if matches!(symbol.kind(), 6 | 10) {
                return Err(unsupported("TLS or IFUNC dynamic symbols"));
            }
            accept(symbol, names, !sections.is_empty(), work)?;
        }
    }
    Ok((selected, functions.into_values().collect()))
}

#[derive(Clone, Copy)]
struct Relocation {
    address: u64,
    kind: u32,
    symbol: u64,
    addend: i64,
}
fn relocations(
    mapping: &Mapping<'_>,
    dynamic: &Dynamic,
    work: &mut Work,
) -> Result<Vec<Relocation>> {
    let mut tables = Vec::new();
    if dynamic.tag(7).is_some() || dynamic.tag(8).is_some() {
        let address = dynamic.required(7)?;
        let size = dynamic.required(8)?;
        if dynamic.required(9)? != 24 {
            return Err(invalid("DT_RELAENT is not 24"));
        }
        tables.push((address, size));
    }
    if dynamic.tag(23).is_some() || dynamic.tag(2).is_some() {
        let address = dynamic.required(23)?;
        let size = dynamic.required(2)?;
        if dynamic.required(20)? != 7 {
            return Err(unsupported("PLT relocations are not RELA"));
        }
        tables.push((address, size));
    }
    let mut records = Vec::new();
    for (address, size) in tables {
        let count = table_count(size, 24)?;
        if records.len() as u64 + count > MAX_TABLE {
            return Err(BinaryError::Limit("too many dynamic relocations"));
        }
        let bytes = if size == 0 {
            &[]
        } else {
            mapping.bytes(address, size)?
        };
        work.use_bytes(bytes.len())?;
        for entry in bytes.chunks_exact(24) {
            let info = u64_at(entry, 8)?;
            let record = Relocation {
                address: u64_at(entry, 0)?,
                kind: info as u32,
                symbol: info >> 32,
                addend: i64::from_le_bytes(array(entry, 16)?),
            };
            if record.kind == 0 {
                continue;
            }
            if !matches!(record.kind, 1 | 6 | 7 | 8) {
                return Err(BinaryError::Relocation {
                    address: record.address,
                    kind: record.kind,
                    reason: "unsupported relocation (COPY, TLS, IFUNC and unknown types are rejected)",
                });
            }
            if !mapping.contains(record.address, 8, false) {
                return Err(invalid("relocation field is not contained in PT_LOAD"));
            }
            records.push(record);
        }
    }
    records.sort_by_key(|r| r.address);
    if records.windows(2).any(|p| p[0].address + 8 > p[1].address) {
        return Err(invalid(
            "overlapping or duplicate dynamic relocation fields",
        ));
    }
    Ok(records)
}

/// Load deterministic guest RAM, never host executable pages. Sparse spans,
/// BSS, padding and stack together are limited to 16 MiB; function bytes to
/// 1 MiB and symbol/relocation tables to 262144 records. ET_EXEC requires bias
/// zero; ET_DYN uses the explicitly supplied bias. Holes are ordinary zero RAM,
/// not an OS page-permission model. The stack includes a root return slot.
///
/// Unmodeled function imports receive distinct non-RAM sentinel addresses;
/// these are metadata for conservative call rejection, never host addresses.
/// Undefined STT_NOTYPE is permitted only for puts or weak CRT imports. Data
/// imports, COPY, TLS, IFUNC, REL/RELR and unknown relocation types are rejected.
pub fn load(object: &[u8], symbol: &str, options: LinkedOptions) -> Result<BinaryImage> {
    load_selected(object, Selection::Name(symbol), options)
}

/// Select an exact link-time virtual address. Positive-size function symbols
/// supply preferred bounds; mapped `.eh_frame` FDEs add contiguous code regions
/// and synthetic names. PIE load bias is added after metadata interpretation.
/// An interior PC requires a known region entry rather than a guessed boundary.
pub fn load_at(object: &[u8], entry: u64, options: LinkedOptions) -> Result<BinaryImage> {
    load_selected(object, Selection::Address(entry), options)
}

#[derive(Clone, Copy)]
enum Selection<'a> {
    Name(&'a str),
    Address(u64),
}

fn load_selected(
    object: &[u8],
    selection: Selection<'_>,
    options: LinkedOptions,
) -> Result<BinaryImage> {
    if object.len() > 64 * 1024 * 1024 {
        return Err(BinaryError::Limit("input file exceeds 64 MiB"));
    }
    range(object, 0, 64)?;
    if &object[..7] != b"\x7fELF\x02\x01\x01" {
        return Err(unsupported("expected ELF64 little-endian version 1"));
    }
    if u16_at(object, 18)? != 62 || u32_at(object, 20)? != 1 {
        return Err(unsupported("expected x86-64 ELF version 1"));
    }
    if u16_at(object, 52)? != 64 {
        return Err(invalid("ELF header size is not 64"));
    }
    let elf_type = u16_at(object, 16)?;
    if !matches!(elf_type, 2 | 3) {
        return Err(unsupported("expected ET_EXEC or ET_DYN"));
    }
    if elf_type == 2 && options.load_bias != 0 {
        return Err(invalid("ET_EXEC requires load_bias=0"));
    }
    if options.stack_size < 16 {
        return Err(invalid("stack must contain at least 16 bytes"));
    }
    let stack_size = u64::try_from(options.stack_size)
        .map_err(|_| BinaryError::Limit("stack size does not fit u64"))?;
    if stack_size > MAX_MEMORY {
        return Err(BinaryError::Limit("stack exceeds 16 MiB"));
    }
    let phoff = u64_at(object, 32)?;
    let phnum = u16_at(object, 56)? as u64;
    if phnum == 0 || phnum > 4096 {
        return Err(BinaryError::Limit("missing or excessive program headers"));
    }
    if u16_at(object, 54)? != 56 {
        return Err(invalid("program header stride is not 56"));
    }
    range(object, phoff, phnum * 56)?;
    let mut loads = Vec::new();
    let mut dyn_segment = None;
    for index in 0..phnum {
        let bytes = range(object, phoff + index * 56, 56)?;
        let segment = Segment {
            index: index as usize,
            kind: u32_at(bytes, 0)?,
            flags: u32_at(bytes, 4)?,
            offset: u64_at(bytes, 8)?,
            address: u64_at(bytes, 16)?,
            files: u64_at(bytes, 32)?,
            memory: u64_at(bytes, 40)?,
        };
        if segment.kind == 7 {
            return Err(unsupported("PT_TLS"));
        }
        if !matches!(segment.kind, 1 | 2) {
            continue;
        }
        range(object, segment.offset, segment.files)?;
        if segment.files > segment.memory {
            return Err(invalid("segment filesz exceeds memsz"));
        }
        end(segment.address, segment.memory)?;
        end(end(segment.address, options.load_bias)?, segment.memory)?;
        if segment.kind == 1 {
            let alignment = u64_at(bytes, 48)?;
            if alignment > 1
                && (!alignment.is_power_of_two()
                    || alignment > MAX_MEMORY
                    || segment.address % alignment != segment.offset % alignment)
            {
                return Err(invalid("invalid PT_LOAD alignment or congruence"));
            }
            if segment.memory != 0 {
                loads.push(segment);
            }
        } else if dyn_segment.replace(segment).is_some() {
            return Err(invalid("multiple PT_DYNAMIC segments"));
        }
    }
    loads.sort_by_key(|s| s.address);
    if loads.is_empty() {
        return Err(invalid("no nonempty PT_LOAD segments"));
    }
    if loads
        .windows(2)
        .any(|p| p[0].address + p[0].memory > p[1].address)
    {
        return Err(invalid("overlapping PT_LOAD segments"));
    }
    let original_base = loads[0].address;
    let original_end = loads
        .last()
        .map(|s| s.address + s.memory)
        .expect("nonempty");
    let memory_base = end(original_base, options.load_bias)?;
    let stack_start = aligned(end(original_end, options.load_bias)?)?;
    let memory_end = aligned(end(stack_start, stack_size)?)?;
    let memory_size = memory_end - memory_base;
    if memory_size > MAX_MEMORY {
        return Err(BinaryError::Limit(
            "guest image including stack exceeds 16 MiB",
        ));
    }
    let mapping = Mapping {
        data: object,
        loads,
    };
    let sections = sections(object)?;
    let mut work = Work(MAX_WORK);
    let dynamic = dynamic(&mapping, &sections, dyn_segment, &mut work)?;
    let name = match selection {
        Selection::Name(name) => Some(name),
        _ => None,
    };
    let (selected_symbol, mut functions) =
        select_function(&mapping, &sections, &dynamic, name, &mut work)?;
    let relocations = relocations(&mapping, &dynamic, &mut work)?;
    let selected = match selection {
        Selection::Name(name) => {
            let symbol =
                selected_symbol.ok_or_else(|| BinaryError::MissingFunction(name.to_owned()))?;
            FunctionSymbol {
                name: name.to_owned(),
                address: symbol.value,
                size: symbol.size,
                origin: FunctionOrigin::Symbol,
            }
        }
        Selection::Address(address) => {
            functions = unwind::catalog(&mapping, &sections, &relocations, functions, &mut work)?;
            functions
                .iter()
                .find(|f| f.address == address)
                .cloned()
                .ok_or(BinaryError::MissingFunctionAddress(address))?
        }
    };
    for function in &mut functions {
        function.address = end(function.address, options.load_bias)?;
    }
    let mut imports = Vec::new();
    let mut patches = Vec::new();
    let mut unmodeled = BTreeMap::new();
    for record in relocations {
        let error = |reason| BinaryError::Relocation {
            address: record.address,
            kind: record.kind,
            reason,
        };
        let value = if record.kind == 8 {
            if record.symbol != 0 {
                return Err(error("RELATIVE must use symbol zero"));
            }
            u64::try_from(i128::from(options.load_bias) + i128::from(record.addend))
                .map_err(|_| error("RELATIVE result overflows u64"))?
        } else {
            if record.symbol == 0 {
                return Err(error("symbolic relocation requires a symbol"));
            }
            let sym = dynamic.symbol(&mapping, record.symbol)?;
            if !matches!(sym.kind(), 0..=3) {
                return Err(error("TLS, IFUNC or unsupported symbol kind"));
            }
            let base = if sym.section == 0 {
                if sym.value != 0 {
                    return Err(error("undefined symbol has a nonzero value"));
                }
                let name = work.name(dynamic.names(&mapping)?, sym.name)?;
                if name.is_empty() {
                    return Err(error("unnamed import"));
                }
                if sym.kind() != 2 && !(sym.kind() == 0 && (name == "puts" || sym.info >> 4 == 2)) {
                    return Err(error("unsupported data or untyped nonweak import"));
                }
                let modeled = name == "puts";
                let target = if modeled {
                    memory_end
                } else {
                    let next = unmodeled.len() as u64 + 1;
                    *unmodeled
                        .entry(record.symbol)
                        .or_insert(end(memory_end, next * 8)?)
                };
                imports.push(ImportSlot {
                    name: name.to_owned(),
                    symbol_kind: sym.kind(),
                    address: end(record.address, options.load_bias)?,
                    width: 8,
                    kind: record.kind,
                    modeled,
                    addend: record.addend,
                });
                target
            } else if sym.section == 0xfff1 {
                sym.value
            } else {
                if sym.section >= 0xff00 {
                    return Err(error("reserved or COMMON symbol section"));
                }
                if !mapping.contains(sym.value, sym.size.max(1), false) {
                    return Err(error("defined symbol is outside PT_LOAD"));
                }
                end(sym.value, options.load_bias)?
            };
            if matches!(record.kind, 6 | 7) {
                if record.addend != 0 {
                    return Err(error("GLOB_DAT/JUMP_SLOT requires a zero addend"));
                }
                base
            } else {
                u64::try_from(i128::from(base) + i128::from(record.addend))
                    .map_err(|_| error("absolute relocation result overflows u64"))?
            }
        };
        patches.push((record.address - original_base, value));
    }
    let mut loaded_sections = Vec::new();
    for (index, section) in sections
        .iter()
        .enumerate()
        .filter(|(_, s)| s.flags & 2 != 0 && s.size != 0)
    {
        if !mapping.contains(section.address, section.size, false) {
            return Err(invalid("allocated section is outside PT_LOAD"));
        }
        loaded_sections.push(LoadedSection {
            index,
            address: end(section.address, options.load_bias)?,
            size: section.size,
        });
    }
    // Sectionless binaries still expose their loaded ranges to image consumers.
    if sections.is_empty() {
        loaded_sections.extend(mapping.loads.iter().map(|s| LoadedSection {
            index: s.index,
            address: s.address + options.load_bias,
            size: s.memory,
        }));
    }
    let mut memory = vec![0; memory_size as usize];
    for segment in &mapping.loads {
        let start = (segment.address - original_base) as usize;
        memory[start..start + segment.files as usize].copy_from_slice(range(
            object,
            segment.offset,
            segment.files,
        )?);
    }
    for (offset, value) in patches {
        memory[offset as usize..offset as usize + 8].copy_from_slice(&value.to_le_bytes());
    }
    let function_start = (selected.address - original_base) as usize;
    let function = FunctionImage {
        name: selected.name,
        address: end(selected.address, options.load_bias)?,
        bytes: memory[function_start..function_start + selected.size as usize].to_vec(),
        relocations: Vec::new(),
    };
    let executable = mapping
        .loads
        .iter()
        .filter(|s| s.flags & 1 != 0)
        .map(|s| {
            (
                s.address + options.load_bias,
                s.address + options.load_bias + s.files,
            )
        })
        .collect();
    Ok(BinaryImage {
        image: LinkedImage {
            memory_base,
            memory,
            function,
            sections: loaded_sections,
            puts_address: memory_end,
            stack_pointer: memory_end - 8,
        },
        elf_type,
        bias: options.load_bias,
        imports,
        functions,
        executable,
    })
}
