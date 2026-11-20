//! Bounded x86-64 `.eh_frame` region reader, independent of CFI execution.
//!
//! An FDE describes a contiguous code region, which can be one part of a
//! function. Callers must check executable file mapping and ownership separately.
//! Layout: LSB Core 4.1 §10.6; AMD64 ABI 0.99 §4.2.4.
//! https://refspecs.linuxfoundation.org/elf/x86_64-abi-0.99.pdf

use std::collections::BTreeMap;
use std::fmt;

const MAX_BYTES: usize = 4 * 1024 * 1024;
const MAX_RECORDS: usize = 65_536;
const MAX_CIES: usize = 4096;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Region {
    pub address: u64,
    pub size: u64,
    /// Byte offset of the original FDE in the supplied section.
    pub record: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Error {
    pub offset: usize,
    pub reason: &'static str,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ".eh_frame at {:#x}: {}", self.offset, self.reason)
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;

struct Cursor<'a> {
    data: &'a [u8],
    at: usize,
    end: usize,
}
impl Cursor<'_> {
    fn error(&self, reason: &'static str) -> Error {
        Error {
            offset: self.at,
            reason,
        }
    }
    fn bytes(&mut self, size: usize) -> Result<&[u8]> {
        let next = self
            .at
            .checked_add(size)
            .ok_or_else(|| self.error("offset overflow"))?;
        if next > self.end {
            return Err(self.error("truncated record"));
        }
        let bytes = &self.data[self.at..next];
        self.at = next;
        Ok(bytes)
    }
    fn byte(&mut self) -> Result<u8> {
        Ok(self.bytes(1)?[0])
    }
    fn u32(&mut self) -> Result<u32> {
        Ok(u32::from_le_bytes(self.bytes(4)?.try_into().unwrap()))
    }
    fn leb(&mut self, signed: bool) -> Result<i128> {
        let mut value = 0u128;
        for i in 0..10 {
            let byte = self.byte()?;
            value |= u128::from(byte & 127) << (i * 7);
            if byte & 128 == 0 {
                let value = if signed && byte & 64 != 0 {
                    value as i128 - (1i128 << ((i + 1) * 7))
                } else {
                    value as i128
                };
                if (signed && i64::try_from(value).is_err())
                    || (!signed && u64::try_from(value).is_err())
                {
                    return Err(self.error("LEB128 exceeds 64 bits"));
                }
                return Ok(value);
            }
        }
        Err(self.error("unterminated LEB128"))
    }
    fn unsigned_leb(&mut self) -> Result<u64> {
        Ok(self.leb(false)? as u64)
    }
    fn raw_pointer(&mut self, format: u8) -> Result<i128> {
        Ok(match format {
            0 | 4 => u64::from_le_bytes(self.bytes(8)?.try_into().unwrap()) as i128,
            1 => self.leb(false)?,
            2 => u16::from_le_bytes(self.bytes(2)?.try_into().unwrap()) as i128,
            3 => self.u32()? as i128,
            9 => self.leb(true)?,
            10 => i16::from_le_bytes(self.bytes(2)?.try_into().unwrap()) as i128,
            11 => i32::from_le_bytes(self.bytes(4)?.try_into().unwrap()) as i128,
            12 => i64::from_le_bytes(self.bytes(8)?.try_into().unwrap()) as i128,
            _ => return Err(self.error("unsupported pointer representation")),
        })
    }
    fn augmentation_end(&mut self) -> Result<usize> {
        let size = usize::try_from(self.unsigned_leb()?)
            .map_err(|_| self.error("augmentation size exceeds host"))?;
        let end = self
            .at
            .checked_add(size)
            .ok_or_else(|| self.error("augmentation overflow"))?;
        if end > self.end {
            return Err(self.error("augmentation exceeds record"));
        }
        Ok(end)
    }
}

#[derive(Clone, Copy)]
struct Cie {
    encoding: u8,
    augmented: bool,
}

fn encoding_supported(encoding: u8) -> bool {
    matches!(encoding & 0x0f, 0..=4 | 9..=12) && matches!(encoding & 0xf0, 0 | 0x10)
}

fn cie(cursor: &mut Cursor<'_>) -> Result<Cie> {
    let version = cursor.byte()?;
    if !matches!(version, 1 | 3) {
        return Err(cursor.error("unsupported CIE version"));
    }
    let mut augmentation = Vec::new();
    loop {
        let byte = cursor.byte()?;
        if byte == 0 {
            break;
        }
        if augmentation.len() == 64 {
            return Err(cursor.error("augmentation name exceeds 64 bytes"));
        }
        augmentation.push(byte);
    }
    if cursor.unsigned_leb()? == 0 {
        return Err(cursor.error("zero code alignment"));
    }
    cursor.leb(true)?;
    if version == 1 {
        cursor.byte()?;
    } else {
        cursor.unsigned_leb()?;
    }
    if augmentation.is_empty() {
        return Ok(Cie {
            encoding: 0,
            augmented: false,
        });
    }
    if augmentation[0] != b'z' {
        return Err(cursor.error("unsupported CIE augmentation"));
    }
    let end = cursor.augmentation_end()?;
    let mut aug = Cursor {
        data: cursor.data,
        at: cursor.at,
        end,
    };
    let mut encoding = 0;
    let mut seen = 0u8;
    for byte in &augmentation[1..] {
        let bit = match byte {
            b'L' => 1,
            b'P' => 2,
            b'R' => 4,
            b'S' => 8,
            _ => return Err(aug.error("unsupported CIE augmentation field")),
        };
        if seen & bit != 0 {
            return Err(aug.error("duplicate CIE augmentation field"));
        }
        seen |= bit;
        match byte {
            b'L' => {
                aug.byte()?;
            }
            b'P' => {
                // Personality is opaque metadata. Consume its representation;
                // never dereference its possibly indirect encoded pointer.
                let personality = aug.byte()?;
                if personality == 0xff
                    || !matches!(personality & 0x70, 0 | 0x10 | 0x20 | 0x30 | 0x40)
                {
                    return Err(aug.error("unsupported personality encoding"));
                }
                aug.raw_pointer(personality & 15)?;
            }
            b'R' => {
                encoding = aug.byte()?;
            }
            b'S' => {}
            _ => unreachable!(),
        }
    }
    if !encoding_supported(encoding) {
        return Err(aug.error("unsupported FDE pointer encoding"));
    }
    cursor.at = end;
    Ok(Cie {
        encoding,
        augmented: true,
    })
}

/// Read CIE v1/v3 and ordinary 32-bit record lengths. Absolute and PC-relative
/// FDE pointers use the supported unsigned/signed fixed-width or LEB formats.
/// Unsupported encodings and malformed records return an offset diagnostic.
/// CFI instructions and language-specific payloads remain opaque bytes.
pub fn read(data: &[u8], section_address: u64) -> Result<Vec<Region>> {
    let fail = |offset, reason| Error { offset, reason };
    if data.len() > MAX_BYTES {
        return Err(fail(0, "section exceeds 4 MiB"));
    }
    section_address
        .checked_add(data.len() as u64)
        .ok_or_else(|| fail(0, "section address overflow"))?;
    let mut cursor = Cursor {
        data,
        at: 0,
        end: data.len(),
    };
    let mut cies = BTreeMap::new();
    let mut regions = Vec::new();
    let mut records = 0;
    while cursor.at < cursor.end {
        let record = cursor.at;
        let length = cursor.u32()?;
        if length == 0 {
            if data[cursor.at..].iter().any(|b| *b != 0) {
                return Err(fail(cursor.at, "nonzero bytes after terminator"));
            }
            break;
        }
        records += 1;
        if records > MAX_RECORDS {
            return Err(fail(record, "record count exceeds 65536"));
        }
        if length == u32::MAX {
            return Err(fail(record, "extended record length unsupported"));
        }
        let stop = cursor
            .at
            .checked_add(length as usize)
            .ok_or_else(|| fail(record, "record length overflow"))?;
        if stop > cursor.end {
            return Err(fail(record, "record exceeds section"));
        }
        let mut entry = Cursor {
            data,
            at: cursor.at,
            end: stop,
        };
        let pointer_field = entry.at;
        let id = entry.u32()?;
        if id == 0 {
            if cies.len() == MAX_CIES {
                return Err(fail(record, "CIE count exceeds 4096"));
            }
            cies.insert(record, cie(&mut entry)?);
        } else {
            let referenced = pointer_field
                .checked_sub(id as usize)
                .ok_or_else(|| fail(pointer_field, "CIE reference underflow"))?;
            let common = cies
                .get(&referenced)
                .ok_or_else(|| fail(pointer_field, "FDE lacks a preceding CIE record"))?;
            let field_address = section_address + entry.at as u64;
            let raw = entry.raw_pointer(common.encoding & 15)?;
            let absolute = raw
                + if common.encoding & 0x70 == 0x10 {
                    field_address as i128
                } else {
                    0
                };
            let address =
                u64::try_from(absolute).map_err(|_| entry.error("FDE address overflow"))?;
            // PC range uses representation bits only, never the PC-relative bias.
            let size = u64::try_from(entry.raw_pointer(common.encoding & 15)?)
                .map_err(|_| entry.error("negative FDE range"))?;
            address
                .checked_add(size)
                .ok_or_else(|| entry.error("FDE range overflow"))?;
            if common.augmented {
                entry.augmentation_end()?;
            }
            if size != 0 {
                regions.push(Region {
                    address,
                    size,
                    record,
                });
            }
        }
        cursor.at = stop;
    }
    Ok(regions)
}
