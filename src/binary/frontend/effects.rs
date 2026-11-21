//! Source-identity proof followed by linking and effect-aware executable lift.

use std::fmt;

use crate::binary::elf;
use crate::binary::loader::{self, LinkedImage, LoadError, LoadOptions};
use crate::binary::object_refs::{ObjectReferences, ReferenceError, Target};
use crate::binary::x86::{self, EffectLiftError, Operand, Operation};
use crate::model::effects::{self, CallTarget, Instruction};

#[derive(Clone, Debug)]
pub struct EffectFunction {
    pub image: LinkedImage,
    pub program: effects::Program,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EffectFrontendError {
    References(ReferenceError),
    UnprovenCall {
        instruction: u64,
        target: Option<Target>,
    },
    Load(LoadError),
    Lift(EffectLiftError),
    Linked(String),
    ProofMismatch {
        instruction: u64,
        reason: &'static str,
    },
}

impl fmt::Display for EffectFrontendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::References(error) => error.fmt(f),
            Self::UnprovenCall {
                instruction,
                target,
            } => write!(
                f,
                "effect frontend at function+{instruction:#x}: call target {target:?} is not proven external puts+0"
            ),
            Self::Load(error) => error.fmt(f),
            Self::Lift(error) => error.fmt(f),
            Self::Linked(error) => f.write_str(error),
            Self::ProofMismatch {
                instruction,
                reason,
            } => {
                write!(
                    f,
                    "effect frontend at function+{instruction:#x}: original call proof mismatch: {reason}"
                )
            }
        }
    }
}
impl std::error::Error for EffectFrontendError {}

/// Prove every reachable source call is exactly external `puts+0` before
/// applying any relocations, then build an explicit effect program.
pub fn lift_elf_effects(
    object: &[u8],
    symbol: &str,
    options: LoadOptions,
) -> Result<EffectFunction, EffectFrontendError> {
    let proof =
        ObjectReferences::analyze(object, symbol).map_err(EffectFrontendError::References)?;
    for call in &proof.calls {
        if !matches!(&call.target, Some(Target::External { name, addend: 0 }) if name == "puts") {
            return Err(EffectFrontendError::UnprovenCall {
                instruction: call.instruction,
                target: call.target.clone(),
            });
        }
    }
    // Retain the original opcode/operand form and length, not merely the
    // patched destination value. The source proof is independent of linking.
    let original = elf::read_function(object, symbol)
        .map_err(|error| EffectFrontendError::References(ReferenceError::Elf(error)))?;
    let image = loader::link(object, symbol, options).map_err(EffectFrontendError::Load)?;
    if image.function.bytes.len() != proof.function_size {
        return Err(EffectFrontendError::ProofMismatch {
            instruction: 0,
            reason: "function size changed during linking",
        });
    }
    let program = x86::lift_effects(
        &image.function.bytes,
        image.function.address,
        image.function.address,
        image.puts_address,
    )
    .map_err(EffectFrontendError::Lift)?;
    let mut calls = program
        .instructions()
        .iter()
        .filter_map(|instruction| match instruction {
            Instruction::Call(call) => Some(call),
            Instruction::Core(_) => None,
        });
    for source in &proof.calls {
        let mismatch = |reason| EffectFrontendError::ProofMismatch {
            instruction: source.instruction,
            reason,
        };
        let lifted = calls
            .next()
            .ok_or_else(|| mismatch("source call is absent after linking"))?;
        if lifted.address.checked_sub(image.function.address) != Some(source.instruction)
            || lifted.tail != source.tail
        {
            return Err(mismatch(
                "call site or tail behavior changed during linking",
            ));
        }
        let offset =
            usize::try_from(source.instruction).map_err(|_| mismatch("source offset overflows"))?;
        let original_bytes = original
            .bytes
            .get(offset..)
            .ok_or_else(|| mismatch("source call lies outside function"))?;
        let instruction = x86::decode_reference_at(
            original_bytes,
            original
                .address
                .checked_add(source.instruction)
                .ok_or_else(|| mismatch("source address overflows"))?,
        )
        .map_err(|error| EffectFrontendError::References(ReferenceError::Decode(error)))?;
        if u32::from(instruction.size) != lifted.size {
            return Err(mismatch("call instruction length changed during linking"));
        }
        let same_form = match (instruction.operation, lifted.target) {
            (Operation::Call(_) | Operation::Jump(_), CallTarget::Direct(target)) => {
                target == image.puts_address
            }
            (
                Operation::IndirectCall(Operand::Register(reg))
                | Operation::IndirectJump(Operand::Register(reg)),
                CallTarget::Register(target),
            ) => usize::from(reg.index) == target.0,
            (
                Operation::IndirectCall(Operand::Memory { address, .. })
                | Operation::IndirectJump(Operand::Memory { address, .. }),
                CallTarget::Memory(_),
            ) => address.rip_relative && address.base.is_none() && address.index.is_none(),
            _ => false,
        };
        if !same_form {
            return Err(mismatch("call target operand form changed during linking"));
        }
    }
    if let Some(extra) = calls.next() {
        return Err(EffectFrontendError::ProofMismatch {
            instruction: extra.address - image.function.address,
            reason: "linked code contains an additional unproven call",
        });
    }
    Ok(EffectFunction { image, program })
}
