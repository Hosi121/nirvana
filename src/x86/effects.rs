//! Opt-in lifting of calls to the explicitly modeled external `puts` effect.
//! Reference decoding here does not relax the legacy executable decoder.

use std::collections::BTreeMap;
use std::fmt;

use super::REGISTER_COUNT;
use super::decode::{DecodeError, DecodedInstruction, Operand, Operation, decode_reference_at};
use super::lift::{LiftError, check_effect_flags, lift_instruction};
use crate::cfg::{BuildError, Cfg, Flow, Instruction as Location};
use crate::effects::{self, CallInstruction, CallTarget, Instruction, Program};
use crate::ir::{Reg, Width};

const MAX_FUNCTION_BYTES: usize = 1_048_576;
const MAX_INSTRUCTIONS: usize = 16_384;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EffectLiftError {
    Decode(DecodeError),
    Layout(BuildError),
    Core(LiftError),
    Program(effects::BuildError),
    Limit(&'static str),
    UnsupportedTarget { address: u64, reason: &'static str },
}

impl fmt::Display for EffectLiftError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Decode(error) => error.fmt(f),
            Self::Layout(error) => error.fmt(f),
            Self::Core(error) => error.fmt(f),
            Self::Program(error) => error.fmt(f),
            Self::Limit(reason) => write!(f, "x86 effect lift limit: {reason}"),
            Self::UnsupportedTarget { address, reason } => {
                write!(f, "x86 effect lift at {address:#x}: {reason}")
            }
        }
    }
}
impl std::error::Error for EffectLiftError {}

fn decode_error(address: u64, reason: &'static str) -> EffectLiftError {
    EffectLiftError::Decode(DecodeError {
        address,
        reason: reason.into(),
    })
}

fn indirect_target(
    instruction: DecodedInstruction,
    operand: Operand,
) -> Result<CallTarget, EffectLiftError> {
    match operand {
        Operand::Register(reg) if reg.width == Width::U64 && reg.shift == 0 => {
            Ok(CallTarget::Register(Reg(usize::from(reg.index))))
        }
        Operand::Memory {
            address,
            width: Width::U64,
        } if address.rip_relative && address.base.is_none() && address.index.is_none() => {
            // Match the core lifter's modular guest-address arithmetic. The
            // actual target remains an explicit checked U64 read at runtime.
            Ok(CallTarget::Memory(
                (instruction.address + u64::from(instruction.size))
                    .wrapping_add(address.displacement as u64),
            ))
        }
        _ => Err(EffectLiftError::UnsupportedTarget {
            address: instruction.address,
            reason: "indirect effects require an r64 or RIP-relative m64 target",
        }),
    }
}

fn call(
    instruction: DecodedInstruction,
    base: u64,
    end: u64,
    puts_address: u64,
    resolve: &mut impl FnMut(DecodedInstruction) -> Result<Option<CallTarget>, EffectLiftError>,
) -> Result<Option<CallInstruction>, EffectLiftError> {
    let is_call = matches!(
        instruction.operation,
        Operation::Call(_) | Operation::IndirectCall(_) | Operation::IndirectJump(_)
    ) || matches!(instruction.operation, Operation::Jump(target) if !(base..end).contains(&target));
    if is_call && let Some(target) = resolve(instruction)? {
        return Ok(Some(CallInstruction {
            address: instruction.address,
            size: u32::from(instruction.size),
            target,
            tail: matches!(
                instruction.operation,
                Operation::Jump(_) | Operation::IndirectJump(_)
            ),
        }));
    }
    let (target, tail) = match instruction.operation {
        Operation::Call(target) => {
            if (base..end).contains(&target) || target != puts_address {
                return Err(EffectLiftError::UnsupportedTarget {
                    address: instruction.address,
                    reason: "direct call must target the external puts address",
                });
            }
            (CallTarget::Direct(target), false)
        }
        Operation::Jump(target) if !(base..end).contains(&target) => {
            if target != puts_address {
                return Err(EffectLiftError::UnsupportedTarget {
                    address: instruction.address,
                    reason: "external tail jump must target puts",
                });
            }
            (CallTarget::Direct(target), true)
        }
        Operation::IndirectCall(operand) => (indirect_target(instruction, operand)?, false),
        Operation::IndirectJump(operand) => (indirect_target(instruction, operand)?, true),
        _ => return Ok(None),
    };
    Ok(Some(CallInstruction {
        address: instruction.address,
        size: u32::from(instruction.size),
        target,
        tail,
    }))
}

/// Lift reachable x86-64 instructions using the external `puts` effect model.
///
/// This low-level entry point trusts the supplied `puts_address` annotation;
/// object clients should use `frontend::lift_elf_effects`, which first proves
/// the original symbol identity independently of relocation/link placement.
/// Indirect target values are always validated again by the effect runtime.
pub fn lift_effects(
    bytes: &[u8],
    base: u64,
    entry: u64,
    puts_address: u64,
) -> Result<Program, EffectLiftError> {
    lift_effects_with_resolver(bytes, base, entry, puts_address, |_| Ok(None))
}

/// Internal boundary for a frontend with independent import identity evidence.
pub(crate) fn lift_effects_with_resolver(
    bytes: &[u8],
    base: u64,
    entry: u64,
    puts_address: u64,
    mut resolve: impl FnMut(DecodedInstruction) -> Result<Option<CallTarget>, EffectLiftError>,
) -> Result<Program, EffectLiftError> {
    if bytes.len() > MAX_FUNCTION_BYTES {
        return Err(EffectLiftError::Limit("function bytes"));
    }
    let end = base
        .checked_add(bytes.len() as u64)
        .ok_or_else(|| decode_error(base, "function range overflows"))?;
    let mut decoded = BTreeMap::<u64, (DecodedInstruction, Option<CallInstruction>)>::new();
    let mut pending = vec![entry];
    while let Some(address) = pending.pop() {
        if decoded.contains_key(&address) {
            continue;
        }
        if !(base..end).contains(&address) {
            return Err(decode_error(
                address,
                "control flow leaves the supplied function",
            ));
        }
        if decoded.len() >= MAX_INSTRUCTIONS {
            return Err(EffectLiftError::Limit("instruction count"));
        }
        if let Some((_, (previous, _))) = decoded.range(..address).next_back()
            && address < previous.address + u64::from(previous.size)
        {
            return Err(decode_error(address, "branch enters an instruction"));
        }
        let instruction = decode_reference_at(&bytes[(address - base) as usize..], address)
            .map_err(EffectLiftError::Decode)?;
        let next = address + u64::from(instruction.size);
        if decoded.range(address..next).next().is_some() {
            return Err(decode_error(address, "overlapping instruction streams"));
        }
        let effect = call(instruction, base, end, puts_address, &mut resolve)?;
        if let Some(effect) = &effect {
            if !effect.tail {
                pending.push(next);
            }
        } else {
            match instruction.operation {
                Operation::Return { .. } => {}
                Operation::Jump(target) => pending.push(target),
                Operation::Branch { target, .. } => {
                    pending.push(next);
                    pending.push(target);
                }
                _ => pending.push(next),
            }
        }
        decoded.insert(address, (instruction, effect));
    }
    let mut source = Vec::with_capacity(decoded.len());
    let mut instructions = Vec::with_capacity(decoded.len());
    let mut locations = Vec::with_capacity(decoded.len());
    for (instruction, effect) in decoded.into_values() {
        locations.push(if let Some(effect) = &effect {
            Location::new(
                effect.address,
                effect.size,
                if effect.tail {
                    Flow::Return
                } else {
                    Flow::Next
                },
            )
        } else {
            instruction.layout()
        });
        source.push(instruction);
        instructions.push(if let Some(effect) = effect {
            Instruction::Call(effect)
        } else {
            Instruction::Core(lift_instruction(instruction).map_err(EffectLiftError::Core)?)
        });
    }
    // The effect CFG supplies call fallthrough/tail-return semantics to the
    // same definite-flag analysis used by the legacy frontend.
    let cfg = Cfg::build(entry, locations).map_err(EffectLiftError::Layout)?;
    check_effect_flags(&cfg, &source).map_err(EffectLiftError::Core)?;
    Program::new(entry, REGISTER_COUNT, instructions, puts_address)
        .map_err(EffectLiftError::Program)
}
