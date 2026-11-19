//! A bounded synthetic linker for ELF64 x86-64 ET_REL objects.
//!
//! This creates guest bytes only: it never maps executable host pages, invokes
//! constructors, or resolves a host function address. The sole external symbol,
//! `puts`, is an abstract address immediately beyond the guest RAM image.

use crate::elf::{self, ElfError, FunctionImage, ObjectRelocation, RelocationTarget};
use std::collections::BTreeMap;
use std::fmt;

const MAX_MEMORY: u64 = 16 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LoadOptions {
    pub base: u64,
    pub stack_size: usize,
}

impl Default for LoadOptions {
    fn default() -> Self {
        Self {
            base: 0x10000,
            stack_size: 65536,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoadedSection {
    pub index: usize,
    pub address: u64,
    pub size: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LinkedImage {
    pub memory_base: u64,
    pub memory: Vec<u8>,
    pub function: FunctionImage,
    pub sections: Vec<LoadedSection>,
    pub puts_address: u64,
    /// SysV entry alignment (RSP % 16 == 8), with a reserved root return slot.
    pub stack_pointer: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoadError {
    Elf(ElfError),
    Invalid(&'static str),
    Unsupported(&'static str),
    Limit(&'static str),
    Relocation {
        section: usize,
        offset: u64,
        reason: &'static str,
    },
}

impl fmt::Display for LoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Elf(error) => error.fmt(f),
            Self::Invalid(reason) => write!(f, "invalid ELF link input: {reason}"),
            Self::Unsupported(reason) => write!(f, "unsupported ELF link input: {reason}"),
            Self::Limit(reason) => write!(f, "ELF link resource limit: {reason}"),
            Self::Relocation {
                section,
                offset,
                reason,
            } => write!(
                f,
                "ELF relocation at section {section}+{offset:#x}: {reason}"
            ),
        }
    }
}

impl std::error::Error for LoadError {}

impl From<ElfError> for LoadError {
    fn from(error: ElfError) -> Self {
        Self::Elf(error)
    }
}

fn aligned(address: u64, alignment: u64) -> Result<u64, LoadError> {
    let alignment = alignment.max(1);
    address
        .checked_add(alignment - 1)
        .map(|value| value & !(alignment - 1))
        .ok_or(LoadError::Invalid("address alignment overflow"))
}

fn bounded_end(base: u64, start: u64, size: u64) -> Result<u64, LoadError> {
    let end = start
        .checked_add(size)
        .ok_or(LoadError::Invalid("guest address range overflow"))?;
    if end
        .checked_sub(base)
        .is_none_or(|length| length > MAX_MEMORY)
    {
        return Err(LoadError::Limit("guest image exceeds 16 MiB"));
    }
    Ok(end)
}

fn target_address(
    relocation: &ObjectRelocation,
    placements: &[Option<LoadedSection>],
    puts_address: u64,
) -> Result<u64, &'static str> {
    if !matches!(relocation.symbol_kind, 0..=3) {
        return Err("unsupported relocation symbol kind");
    }
    match relocation.target {
        RelocationTarget::Undefined
            if relocation.symbol.as_deref() == Some("puts")
                && matches!(relocation.symbol_kind, 0 | 2) =>
        {
            Ok(puts_address)
        }
        RelocationTarget::Undefined => Err("unresolved import (only puts is supported)"),
        RelocationTarget::Absolute(address) => Ok(address),
        RelocationTarget::Section { index, offset } => {
            let section = placements
                .get(index)
                .and_then(Option::as_ref)
                .ok_or("symbol is not in an allocated section")?;
            if offset > section.size {
                return Err("symbol lies beyond its allocated section");
            }
            section
                .address
                .checked_add(offset)
                .ok_or("symbol address overflow")
        }
        RelocationTarget::Reserved(_) => Err("reserved or COMMON symbol section"),
    }
}

/// Place all allocated sections, resolve supported explicit-addend relocations,
/// append deterministic GOT slots, then append a zeroed 16-byte-aligned stack.
///
/// Section alignment is capped at 1 MiB; guest RAM (including padding, GOT and
/// stack) is capped at 16 MiB. Stack sizes below 16 bytes are rejected; other
/// sizes are rounded up to 16 bytes. Metadata, fields, overlaps and arithmetic
/// are checked before allocating guest RAM. Input bytes remain unchanged.
pub fn link(object: &[u8], symbol: &str, options: LoadOptions) -> Result<LinkedImage, LoadError> {
    if options.stack_size < 16 {
        return Err(LoadError::Invalid("stack must contain at least 16 bytes"));
    }
    let stack_size = u64::try_from(options.stack_size)
        .map_err(|_| LoadError::Limit("stack size does not fit u64"))?;
    if stack_size > MAX_MEMORY {
        return Err(LoadError::Limit("stack exceeds 16 MiB"));
    }
    let (context, relocations) = elf::read_link_context(object, symbol)?;
    let mut placements = vec![None; context.sections.len()];
    let mut cursor = options.base;
    for section in context
        .sections
        .iter()
        .filter(|section| section.flags & 2 != 0)
    {
        cursor = aligned(cursor, section.alignment)?;
        let end = bounded_end(options.base, cursor, section.size)?;
        placements[section.index] = Some(LoadedSection {
            index: section.index,
            address: cursor,
            size: section.size,
        });
        cursor = end;
    }
    let selected = placements[context.section]
        .as_ref()
        .ok_or(LoadError::Invalid("selected function is not allocated"))?;
    let function_address = selected
        .address
        .checked_add(context.offset)
        .ok_or(LoadError::Invalid("function address overflow"))?;

    // Preflight all sites and targets. Sorting catches overlap across separate
    // relocation sections too, including duplicate or differently sized fields.
    let mut sites = Vec::with_capacity(relocations.len());
    let mut got = BTreeMap::new();
    for record in &relocations {
        let relocation = &record.relocation;
        let error = |reason| LoadError::Relocation {
            section: record.section,
            offset: relocation.offset,
            reason,
        };
        let width = match relocation.kind {
            1 => 8,
            2 | 4 | 9 | 10 | 11 | 41 | 42 => 4,
            _ => return Err(error("unsupported relocation type")),
        };
        if relocation.addend.is_none() {
            return Err(error("implicit REL addend"));
        }
        let section = placements[record.section]
            .as_ref()
            .ok_or_else(|| error("relocation site is not allocated"))?;
        let end = relocation
            .offset
            .checked_add(width)
            .ok_or_else(|| error("field offset overflow"))?;
        if end > section.size {
            return Err(error("field exceeds target section"));
        }
        sites.push((record.section, relocation.offset, end));
        // An arbitrary temporary external address is sufficient to validate
        // identity here. The final stub address depends on GOT and stack size.
        target_address(relocation, &placements, 0).map_err(error)?;
        if matches!(relocation.kind, 9 | 41 | 42) {
            got.insert(
                (relocation.symbol_table, relocation.symbol_index),
                (0, relocation),
            );
        }
    }
    sites.sort_unstable();
    if sites
        .windows(2)
        .any(|pair| pair[0].0 == pair[1].0 && pair[0].2 > pair[1].1)
    {
        return Err(LoadError::Invalid(
            "overlapping or duplicate relocation fields",
        ));
    }
    if !got.is_empty() {
        cursor = aligned(cursor, 8)?;
    }
    for (address, _) in got.values_mut() {
        *address = cursor;
        cursor = bounded_end(options.base, cursor, 8)?;
    }
    let stack_start = aligned(cursor, 16)?;
    let stack_end = aligned(bounded_end(options.base, stack_start, stack_size)?, 16)?;
    let memory_end = bounded_end(options.base, stack_end, 0)?;
    let puts_address = memory_end;

    // Resolve and range-check every field before any RAM is created or patched.
    let mut patches = Vec::with_capacity(relocations.len());
    for record in &relocations {
        let relocation = &record.relocation;
        let error = |reason| LoadError::Relocation {
            section: record.section,
            offset: relocation.offset,
            reason,
        };
        let target = target_address(relocation, &placements, puts_address).map_err(error)?;
        let section = placements[record.section]
            .as_ref()
            .expect("validated allocation");
        let place = section
            .address
            .checked_add(relocation.offset)
            .ok_or_else(|| error("site address overflow"))?;
        let addend = i128::from(relocation.addend.expect("validated RELA"));
        let symbol_address = if matches!(relocation.kind, 9 | 41 | 42) {
            got[&(relocation.symbol_table, relocation.symbol_index)].0
        } else {
            target
        };
        let mut value = i128::from(symbol_address) + addend;
        if matches!(relocation.kind, 2 | 4 | 9 | 41 | 42) {
            value -= i128::from(place);
        }
        let (width, bits) = match relocation.kind {
            1 => (
                8,
                u64::try_from(value).map_err(|_| error("unsigned 64-bit relocation overflow"))?,
            ),
            10 => (
                4,
                u64::from(
                    u32::try_from(value)
                        .map_err(|_| error("unsigned 32-bit relocation overflow"))?,
                ),
            ),
            _ => (
                4,
                u64::from(
                    i32::try_from(value).map_err(|_| error("signed 32-bit relocation overflow"))?
                        as u32,
                ),
            ),
        };
        patches.push(((place - options.base) as usize, width, bits));
    }
    let mut memory = vec![0; (memory_end - options.base) as usize];
    for section in &context.sections {
        if let Some(placed) = &placements[section.index]
            && let Some(bytes) = section.bytes
        {
            let start = (placed.address - options.base) as usize;
            memory[start..start + bytes.len()].copy_from_slice(bytes);
        }
    }
    for (address, relocation) in got.values() {
        let target =
            target_address(relocation, &placements, puts_address).expect("preflighted symbol");
        let start = (address - options.base) as usize;
        memory[start..start + 8].copy_from_slice(&target.to_le_bytes());
    }
    for (start, width, bits) in patches {
        memory[start..start + width].copy_from_slice(&bits.to_le_bytes()[..width]);
    }
    let function_start = (function_address - options.base) as usize;
    let function_size = context.image.bytes.len();
    let function = FunctionImage {
        name: context.image.name,
        address: function_address,
        bytes: memory[function_start..function_start + function_size].to_vec(),
        relocations: Vec::new(),
    };
    Ok(LinkedImage {
        memory_base: options.base,
        memory,
        function,
        sections: placements.into_iter().flatten().collect(),
        puts_address,
        stack_pointer: stack_end - 8,
    })
}
