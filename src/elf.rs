//! Checked extraction of sized functions from ELF64 x86-64 relocatable objects.
//!
//! Section, symbol, string and relocation layouts follow the System V gABI:
//! <https://gabi.xinuos.com/elf/>. Relocations are reported, never applied.

use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionImage {
    pub name: String,
    /// Section address plus the symbol's section-relative value.
    pub address: u64,
    pub bytes: Vec<u8>,
    pub relocations: Vec<Relocation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Relocation {
    /// Byte offset from the beginning of the selected function.
    pub offset: u64,
    pub kind: u32,
    pub symbol: Option<String>,
}

/// Original section contents. SHT_NOBITS has a size but no file bytes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SectionImage<'a> {
    pub index: usize,
    pub name: Option<&'a str>,
    pub kind: u32,
    pub flags: u64,
    pub address: u64,
    pub size: u64,
    pub bytes: Option<&'a [u8]>,
}

/// A symbol's identity within the relocatable object, without link placement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RelocationTarget {
    Undefined,
    Section { index: usize, offset: u64 },
    Absolute(u64),
    Reserved(u16),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectRelocation {
    /// Byte offset from the beginning of the selected function.
    pub offset: u64,
    pub kind: u32,
    pub width: Option<u64>,
    /// Explicit SHT_RELA addend only. Implicit SHT_REL addends stay unknown.
    pub addend: Option<i64>,
    pub symbol: Option<String>,
    pub symbol_table: usize,
    pub symbol_index: usize,
    pub symbol_kind: u8,
    pub target: RelocationTarget,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionContext<'a> {
    pub image: FunctionImage,
    pub section: usize,
    /// Symbol value within `section`; no sections have been placed or linked.
    pub offset: u64,
    pub sections: Vec<SectionImage<'a>>,
    pub references: Vec<ObjectRelocation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ElfError {
    InvalidFormat(&'static str),
    Unsupported(&'static str),
    MissingFunction(String),
    AmbiguousFunction(String),
    ZeroSizedFunction(String),
}

impl fmt::Display for ElfError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidFormat(reason) => write!(f, "invalid ELF object: {reason}"),
            Self::Unsupported(reason) => write!(f, "unsupported ELF object: {reason}"),
            Self::MissingFunction(name) => write!(f, "no defined STT_FUNC symbol named {name:?}"),
            Self::AmbiguousFunction(name) => write!(f, "ambiguous STT_FUNC symbol named {name:?}"),
            Self::ZeroSizedFunction(name) => write!(f, "function {name:?} has no declared size"),
        }
    }
}

impl std::error::Error for ElfError {}

const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;
const SHT_RELA: u32 = 4;
const SHT_NOBITS: u32 = 8;
const SHT_REL: u32 = 9;
const SHN_LORESERVE: u16 = 0xff00;
const SHN_ABS: u16 = 0xfff1;
const SHN_XINDEX: u16 = 0xffff;

// Bound the opt-in inspection path independently of input file size. In
// particular, overlapping table sections cannot multiply work or allocation.
const CONTEXT_FUNCTION_BYTES: u64 = 1_048_576;
const CONTEXT_REFERENCES: usize = 16_384;
const CONTEXT_WORK: usize = 8_000_000;
const CONTEXT_NAME_BYTES: usize = 16_777_216;

struct Limits {
    work: Option<usize>,
    name_bytes: Option<usize>,
    context: bool,
}

impl Limits {
    fn new(context: bool) -> Self {
        Self {
            work: context.then_some(CONTEXT_WORK),
            name_bytes: context.then_some(CONTEXT_NAME_BYTES),
            context,
        }
    }

    fn work(&mut self, amount: usize) -> Result<(), ElfError> {
        if let Some(remaining) = &mut self.work {
            *remaining = remaining.checked_sub(amount).ok_or(ElfError::Unsupported(
                "ELF context inspection work limit exceeded",
            ))?;
        }
        Ok(())
    }

    fn owned_name(&mut self, name: Option<&str>) -> Result<Option<String>, ElfError> {
        if let Some(name) = name {
            if let Some(remaining) = &mut self.name_bytes {
                *remaining = remaining
                    .checked_sub(name.len())
                    .ok_or(ElfError::Unsupported(
                        "ELF context symbol name storage limit exceeded",
                    ))?;
            }
            Ok(Some(name.to_owned()))
        } else {
            Ok(None)
        }
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
    info: u32,
    entry_size: u64,
}

#[derive(Clone, Copy)]
struct Symbol<'a> {
    name: Option<&'a str>,
    kind: u8,
    section: u16,
    value: u64,
    size: u64,
}

#[derive(Clone, Copy)]
struct SymbolTable<'a> {
    data: &'a [u8],
    names: &'a [u8],
}

struct ParsedObject<'a> {
    object: &'a [u8],
    sections: Vec<Section>,
    names: Option<&'a [u8]>,
    tables: Vec<Option<SymbolTable<'a>>>,
}

fn invalid(reason: &'static str) -> ElfError {
    ElfError::InvalidFormat(reason)
}

fn range(data: &[u8], start: u64, size: u64) -> Result<&[u8], ElfError> {
    let end = start
        .checked_add(size)
        .ok_or_else(|| invalid("range overflow"))?;
    let start = usize::try_from(start).map_err(|_| invalid("offset does not fit this host"))?;
    let end = usize::try_from(end).map_err(|_| invalid("size does not fit this host"))?;
    data.get(start..end)
        .ok_or_else(|| invalid("range extends beyond the file or section"))
}

fn array<const N: usize>(data: &[u8], offset: u64) -> Result<[u8; N], ElfError> {
    range(data, offset, N as u64)?
        .try_into()
        .map_err(|_| invalid("truncated field"))
}

fn u16_at(data: &[u8], offset: u64) -> Result<u16, ElfError> {
    Ok(u16::from_le_bytes(array(data, offset)?))
}

fn u32_at(data: &[u8], offset: u64) -> Result<u32, ElfError> {
    Ok(u32::from_le_bytes(array(data, offset)?))
}

fn u64_at(data: &[u8], offset: u64) -> Result<u64, ElfError> {
    Ok(u64::from_le_bytes(array(data, offset)?))
}

fn string_table(data: &[u8]) -> Result<(), ElfError> {
    if !data.is_empty() && (data.first() != Some(&0) || data.last() != Some(&0)) {
        return Err(invalid("string table must begin and end with NUL"));
    }
    Ok(())
}

fn string_at<'a>(
    data: &'a [u8],
    offset: u32,
    limits: &mut Limits,
) -> Result<Option<&'a str>, ElfError> {
    if offset == 0 {
        return Ok(None);
    }
    let offset =
        usize::try_from(offset).map_err(|_| invalid("string offset does not fit this host"))?;
    let tail = data
        .get(offset..)
        .ok_or_else(|| invalid("invalid string offset"))?;
    let scan_size = tail.len().min(limits.work.unwrap_or(usize::MAX));
    let length = tail[..scan_size]
        .iter()
        .position(|&byte| byte == 0)
        .ok_or_else(|| {
            if scan_size < tail.len() {
                ElfError::Unsupported("ELF context inspection work limit exceeded")
            } else {
                invalid("unterminated string")
            }
        })?;
    limits.work(length + 1)?;
    let name = std::str::from_utf8(&tail[..length])
        .map_err(|_| ElfError::Unsupported("non-UTF-8 symbol or section name"))?;
    Ok(Some(name))
}

fn entries<'a>(object: &'a [u8], section: &Section, size: u64) -> Result<&'a [u8], ElfError> {
    if section.entry_size != size || !section.size.is_multiple_of(size) {
        return Err(invalid("invalid table entry size or incomplete entry"));
    }
    range(object, section.offset, section.size)
}

fn section_index(index: u32, count: usize) -> Result<usize, ElfError> {
    let index =
        usize::try_from(index).map_err(|_| invalid("section index does not fit this host"))?;
    if index == 0 || index >= count {
        return Err(invalid("invalid section index"));
    }
    Ok(index)
}

/// Read a single, explicitly sized STT_FUNC definition. No relocation is resolved.
///
/// Only ELF64, little-endian, EM_X86_64, ET_REL and ordinary section numbering
/// are supported. Ambiguous definitions and unknown function sizes are errors.
pub fn read_function(object: &[u8], symbol: &str) -> Result<FunctionImage, ElfError> {
    let mut limits = Limits::new(false);
    let parsed = ParsedObject::parse(object, &mut limits)?;
    Ok(parsed.function(symbol, &mut limits)?.image)
}

/// Inspect an ET_REL function together with original sections and symbol targets.
///
/// No relocation is applied and no link address is invented. Section byte slices
/// borrow `object`, including writable and compressed sections; flags describe
/// their original representation. NOBITS sections have `bytes: None`.
///
/// Inspection is bounded to 1 MiB of selected function bytes, 16,384 references,
/// 8,000,000 metadata/name work units and 16 MiB of copied symbol names. Limits
/// return `ElfError::Unsupported`. The legacy `read_function` has no new limits.
pub fn read_function_context<'a>(
    object: &'a [u8],
    symbol: &str,
) -> Result<FunctionContext<'a>, ElfError> {
    let mut limits = Limits::new(true);
    let parsed = ParsedObject::parse(object, &mut limits)?;
    let mut result = parsed.function(symbol, &mut limits)?;
    result.sections = parsed
        .sections
        .iter()
        .enumerate()
        .map(|(index, section)| {
            limits.work(1)?;
            Ok(SectionImage {
                index,
                name: parsed
                    .names
                    .map(|names| string_at(names, section.name, &mut limits))
                    .transpose()?
                    .flatten(),
                kind: section.kind,
                flags: section.flags,
                address: section.address,
                size: section.size,
                bytes: if section.kind == SHT_NOBITS {
                    None
                } else {
                    Some(range(object, section.offset, section.size)?)
                },
            })
        })
        .collect::<Result<_, ElfError>>()?;
    Ok(result)
}

impl<'a> SymbolTable<'a> {
    fn symbol(&self, index: usize, limits: &mut Limits) -> Result<Symbol<'a>, ElfError> {
        limits.work(1)?;
        let offset = index
            .checked_mul(24)
            .and_then(|offset| u64::try_from(offset).ok())
            .ok_or_else(|| invalid("symbol offset overflow"))?;
        let data = range(self.data, offset, 24)?;
        Ok(Symbol {
            name: string_at(self.names, u32_at(data, 0)?, limits)?,
            kind: data[4] & 15,
            section: u16_at(data, 6)?,
            value: u64_at(data, 8)?,
            size: u64_at(data, 16)?,
        })
    }
}

impl<'a> ParsedObject<'a> {
    fn parse(object: &'a [u8], limits: &mut Limits) -> Result<Self, ElfError> {
        let ident = range(object, 0, 16)?;
        if ident.get(..4) != Some(b"\x7fELF") {
            return Err(invalid("missing ELF magic"));
        }
        if ident[4] != 2 {
            return Err(ElfError::Unsupported("requires ELF64"));
        }
        if ident[5] != 1 {
            return Err(ElfError::Unsupported("requires little-endian ELF"));
        }
        if ident[6] != 1 || u32_at(object, 20)? != 1 {
            return Err(ElfError::Unsupported("requires ELF version 1"));
        }
        range(object, 0, 64)?;
        if u16_at(object, 16)? != 1 {
            return Err(ElfError::Unsupported(
                "requires an ET_REL relocatable object",
            ));
        }
        if u16_at(object, 18)? != 62 {
            return Err(ElfError::Unsupported("requires EM_X86_64"));
        }
        if u16_at(object, 52)? != 64 || u16_at(object, 58)? != 64 {
            return Err(invalid("invalid ELF64 header or section header size"));
        }
        let section_offset = u64_at(object, 40)?;
        let section_count = u16_at(object, 60)?;
        let names_index = u16_at(object, 62)?;
        let program_count = u16_at(object, 56)?;
        if section_count == 0
            || section_count >= SHN_LORESERVE
            || names_index == SHN_XINDEX
            || program_count == 0xffff
        {
            return Err(ElfError::Unsupported(
                "extended ELF numbering or absent section table",
            ));
        }
        if section_offset == 0 {
            return Err(invalid("missing section header table"));
        }
        if program_count != 0 {
            if u16_at(object, 54)? != 56 {
                return Err(invalid("invalid ELF64 program header size"));
            }
            range(object, u64_at(object, 32)?, u64::from(program_count) * 56)?;
        }
        let table = range(object, section_offset, u64::from(section_count) * 64)?;
        let mut sections = Vec::with_capacity(usize::from(section_count));
        for data in table.chunks_exact(64) {
            limits.work(1)?;
            let section = Section {
                name: u32_at(data, 0)?,
                kind: u32_at(data, 4)?,
                flags: u64_at(data, 8)?,
                address: u64_at(data, 16)?,
                offset: u64_at(data, 24)?,
                size: u64_at(data, 32)?,
                link: u32_at(data, 40)?,
                info: u32_at(data, 44)?,
                entry_size: u64_at(data, 56)?,
            };
            if section.kind == 18 {
                return Err(ElfError::Unsupported(
                    "SHT_SYMTAB_SHNDX extended symbol indices",
                ));
            }
            if section.kind != SHT_NOBITS {
                range(object, section.offset, section.size)?;
            }
            sections.push(section);
        }
        if sections[0].kind != 0 || sections[0].size != 0 {
            return Err(invalid("invalid null section"));
        }
        let names = if names_index == 0 {
            None
        } else {
            let section = sections
                .get(usize::from(names_index))
                .ok_or_else(|| invalid("invalid section name table index"))?;
            if section.kind != SHT_STRTAB {
                return Err(invalid("section name table is not SHT_STRTAB"));
            }
            let names = range(object, section.offset, section.size)?;
            string_table(names)?;
            for section in &sections {
                string_at(names, section.name, limits)?;
            }
            Some(names)
        };
        let mut tables = vec![None; sections.len()];
        for (index, section) in sections
            .iter()
            .enumerate()
            .filter(|(_, section)| section.kind == SHT_SYMTAB)
        {
            let names_index = section_index(section.link, sections.len())?;
            let names_section = &sections[names_index];
            if names_section.kind != SHT_STRTAB {
                return Err(invalid("symbol names do not link to SHT_STRTAB"));
            }
            let names = range(object, names_section.offset, names_section.size)?;
            string_table(names)?;
            let data = entries(object, section, 24)?;
            if data.is_empty()
                || data
                    .get(..24)
                    .is_none_or(|first| first.iter().any(|&byte| byte != 0))
            {
                return Err(invalid("missing or invalid null symbol"));
            }
            if u64::from(section.info) > section.size / 24 {
                return Err(invalid("symbol table sh_info exceeds symbol count"));
            }
            tables[index] = Some(SymbolTable { data, names });
        }
        Ok(Self {
            object,
            sections,
            names,
            tables,
        })
    }

    fn select(&self, name: &str, limits: &mut Limits) -> Result<Symbol<'a>, ElfError> {
        let mut selected = None;
        for table in self.tables.iter().flatten() {
            for index in 0..table.data.len() / 24 {
                let record = table.symbol(index, limits)?;
                if record.section == SHN_XINDEX {
                    return Err(ElfError::Unsupported("SHN_XINDEX extended symbol index"));
                }
                if record.section < SHN_LORESERVE
                    && usize::from(record.section) >= self.sections.len()
                {
                    return Err(invalid("symbol section index exceeds section count"));
                }
                if record.kind == 2
                    && record.name == Some(name)
                    && record.section != 0
                    && selected.replace(record).is_some()
                {
                    return Err(ElfError::AmbiguousFunction(name.to_owned()));
                }
            }
        }
        selected.ok_or_else(|| ElfError::MissingFunction(name.to_owned()))
    }

    fn function(&self, name: &str, limits: &mut Limits) -> Result<FunctionContext<'a>, ElfError> {
        let selected = self.select(name, limits)?;
        if selected.size == 0 {
            return Err(ElfError::ZeroSizedFunction(name.to_owned()));
        }
        if selected.section >= SHN_LORESERVE {
            return Err(ElfError::Unsupported(
                "function has a reserved section index",
            ));
        }
        let selected_section = usize::from(selected.section);
        let section = &self.sections[selected_section];
        if section.kind != 1 || section.flags & 4 == 0 {
            return Err(invalid(
                "function is not in an executable SHT_PROGBITS section",
            ));
        }
        if section.flags & 0x800 != 0 {
            return Err(ElfError::Unsupported("compressed function section"));
        }
        if limits.context && selected.size > CONTEXT_FUNCTION_BYTES {
            return Err(ElfError::Unsupported(
                "ELF context function byte limit exceeded",
            ));
        }
        let section_bytes = range(self.object, section.offset, section.size)?;
        let bytes = range(section_bytes, selected.value, selected.size)?.to_vec();
        let end = selected
            .value
            .checked_add(selected.size)
            .ok_or_else(|| invalid("function size overflow"))?;
        let address = section
            .address
            .checked_add(selected.value)
            .ok_or_else(|| invalid("function address overflow"))?;
        let mut relocations = Vec::new();
        let mut references = Vec::new();
        for relocation_section in self
            .sections
            .iter()
            .filter(|section| matches!(section.kind, SHT_RELA | SHT_REL))
        {
            let target = section_index(relocation_section.info, self.sections.len())?;
            let linked = section_index(relocation_section.link, self.sections.len())?;
            let table = self.tables[linked]
                .ok_or_else(|| invalid("relocations do not link to SHT_SYMTAB"))?;
            let entry_size = if relocation_section.kind == SHT_RELA {
                24
            } else {
                16
            };
            let data = entries(self.object, relocation_section, entry_size)?;
            for data in data.chunks_exact(entry_size as usize) {
                limits.work(1)?;
                let offset = u64_at(data, 0)?;
                let info = u64_at(data, 8)?;
                let kind = info as u32;
                let width = relocation_width(kind);
                let symbol_index = usize::try_from(info >> 32)
                    .map_err(|_| invalid("relocation symbol index does not fit this host"))?;
                if symbol_index >= table.data.len() / 24 {
                    return Err(invalid("invalid relocation symbol index"));
                }
                let referenced = table.symbol(symbol_index, limits)?;
                if offset >= self.sections[target].size {
                    return Err(invalid("relocation site is outside its target section"));
                }
                if let Some(width) = width
                    && offset
                        .checked_add(width)
                        .is_none_or(|site_end| site_end > self.sections[target].size)
                {
                    return Err(invalid("relocation field exceeds its target section"));
                }
                if target != selected_section {
                    continue;
                }
                if offset < selected.value {
                    // Unknown widths cannot prove that the function is untouched.
                    match width {
                        Some(width)
                            if offset
                                .checked_add(width)
                                .is_some_and(|end| end <= selected.value) =>
                        {
                            continue;
                        }
                        _ => {
                            return Err(ElfError::Unsupported(
                                "relocation may cross the function start",
                            ));
                        }
                    }
                }
                if offset >= end {
                    continue;
                }
                if let Some(width) = width
                    && offset
                        .checked_add(width)
                        .is_none_or(|site_end| site_end > end)
                {
                    return Err(invalid("relocation field crosses the function end"));
                }
                if limits.context && references.len() == CONTEXT_REFERENCES {
                    return Err(ElfError::Unsupported(
                        "ELF context reference limit exceeded",
                    ));
                }
                relocations.push(Relocation {
                    offset: offset - selected.value,
                    kind,
                    symbol: limits.owned_name(referenced.name)?,
                });
                if limits.context {
                    let target = match referenced.section {
                        0 => RelocationTarget::Undefined,
                        SHN_ABS => RelocationTarget::Absolute(referenced.value),
                        index if index >= SHN_LORESERVE => RelocationTarget::Reserved(index),
                        index => RelocationTarget::Section {
                            index: usize::from(index),
                            offset: referenced.value,
                        },
                    };
                    references.push(ObjectRelocation {
                        offset: offset - selected.value,
                        kind,
                        width,
                        addend: if relocation_section.kind == SHT_RELA {
                            Some(i64::from_le_bytes(array(data, 16)?))
                        } else {
                            None
                        },
                        symbol: limits.owned_name(referenced.name)?,
                        symbol_table: linked,
                        symbol_index,
                        symbol_kind: referenced.kind,
                        target,
                    });
                }
            }
        }
        Ok(FunctionContext {
            image: FunctionImage {
                name: limits.owned_name(Some(name))?.expect("name is present"),
                address,
                bytes,
                relocations,
            },
            section: selected_section,
            offset: selected.value,
            sections: Vec::new(),
            references,
        })
    }
}

// x86-64 psABI relocation field widths. Unknown types are still reported when
// their site is in the selected function; they are never interpreted/resolved.
fn relocation_width(kind: u32) -> Option<u64> {
    match kind {
        0 | 35 => Some(0),
        14 | 15 => Some(1),
        12 | 13 => Some(2),
        2..=4 | 9..=11 | 19..=23 | 26 | 32 | 34 | 41 | 42 => Some(4),
        1 | 6..=8 | 16..=18 | 24 | 25 | 27..=31 | 33 | 37 | 38 => Some(8),
        36 => Some(16),
        _ => None,
    }
}
