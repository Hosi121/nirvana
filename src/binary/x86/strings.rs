//! Canonical long-mode string transfers and direction-flag forms for module IR.
use super::DecodeError;
use crate::model::ir::Width;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StringOperation {
    Direction(bool),
    Store { width: Width, repeat: bool },
    Move { width: Width, repeat: bool },
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StringInstruction {
    pub address: u64,
    pub size: u8,
    pub operation: StringOperation,
}
pub fn decode_string_at(bytes: &[u8], address: u64) -> Result<StringInstruction, DecodeError> {
    let error = || DecodeError {
        address,
        reason: "unsupported string instruction or prefix sequence".into(),
    };
    let direction = match bytes.first() {
        Some(0xfc) => Some(false),
        Some(0xfd) => Some(true),
        _ => None,
    };
    let (size, operation) = if let Some(backwards) = direction {
        (1, StringOperation::Direction(backwards))
    } else {
        let mut at = 0;
        let mut repeat = false;
        let mut short = false;
        // Legacy prefixes precede the optional REX; duplicates and address-size
        // overrides are outside this explicit 64-bit-address profile.
        for _ in 0..2 {
            match bytes.get(at) {
                Some(0xf3) if !repeat => {
                    repeat = true;
                    at += 1;
                }
                Some(0x66) if !short => {
                    short = true;
                    at += 1;
                }
                _ => break,
            }
        }
        let mut wide = false;
        if let Some(&rex @ 0x40..=0x4f) = bytes.get(at) {
            wide = rex & 8 != 0;
            at += 1;
        }
        let opcode = bytes.get(at).copied().ok_or_else(error)?;
        let width = match opcode {
            0xa4 | 0xaa => Width::U8,
            0xa5 | 0xab if wide => Width::U64,
            0xa5 | 0xab if short => Width::U16,
            0xa5 | 0xab => Width::U32,
            _ => return Err(error()),
        };
        let operation = if opcode == 0xa4 || opcode == 0xa5 {
            StringOperation::Move { width, repeat }
        } else {
            StringOperation::Store { width, repeat }
        };
        (at + 1, operation)
    };
    address.checked_add(size as u64).ok_or_else(error)?;
    Ok(StringInstruction {
        address,
        size: size as u8,
        operation,
    })
}
