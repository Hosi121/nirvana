//! Linux x86-64 FS stack-guard reads resolved against an explicit guest slot.
use super::{DecodeError, DecodedInstruction, Operand, Operation, decode_reference_at};
use crate::ir::Width;

pub const FS_GUARD_OFFSET: u64 = 0x28;

/// Decode the absolute eight-byte FS:0x28 source used by stack protection.
/// The supplied address is guest RAM. Ordinary instruction decoding keeps its
/// segment-free contract; general FS/GS addressing requires another profile.
pub fn decode_fs_guard_at(
    bytes: &[u8],
    address: u64,
    guard_address: u64,
) -> Result<DecodedInstruction, DecodeError> {
    let error = |reason: &str| DecodeError {
        address,
        reason: reason.into(),
    };
    if bytes.first() != Some(&0x64) {
        return Err(error("expected FS prefix"));
    }
    let next = address
        .checked_add(1)
        .ok_or_else(|| error("FS instruction address overflow"))?;
    let mut instruction = decode_reference_at(&bytes[1..], next)?;
    if instruction.size >= 15 {
        return Err(error("FS instruction exceeds 15 bytes"));
    }
    let (destination, source, alu) = match instruction.operation {
        Operation::Mov {
            destination: Operand::Register(destination),
            source,
        } => (destination, source, None),
        Operation::Alu {
            kind,
            destination: Operand::Register(destination),
            source,
        } => (destination, source, Some(kind)),
        _ => {
            return Err(error(
                "FS guard profile requires a register move or ALU source",
            ));
        }
    };
    let Operand::Memory {
        mut address,
        width: Width::U64,
    } = source
    else {
        return Err(error(
            "FS guard profile requires an eight-byte memory source",
        ));
    };
    if destination.width != Width::U64
        || address.base.is_some()
        || address.index.is_some()
        || address.rip_relative
        || address.displacement as u64 != FS_GUARD_OFFSET
    {
        return Err(error("FS guard profile requires absolute FS:0x28"));
    }
    // The caller supplies the selected guest TLS slot. i64 stores its address
    // bit pattern; ordinary addressing is modulo 2^64.
    address.displacement = guard_address as i64;
    let source = Operand::Memory {
        address,
        width: Width::U64,
    };
    instruction.operation = match alu {
        Some(kind) => Operation::Alu {
            kind,
            destination: Operand::Register(destination),
            source,
        },
        None => Operation::Mov {
            destination: Operand::Register(destination),
            source,
        },
    };
    instruction.address = next - 1;
    instruction.size += 1;
    Ok(instruction)
}
