//! Fuse single-use loaded values into strict computations at the load site.
//!
//! T=load(A); ...; D=f(T) becomes T=f(load(A)); ...; D=T. Only the
//! uniquely private temporary changes contents. The contract is
//! return, all RAM and first fault, with original load evaluation order.
//! The stable-input API also admits register leaves with no intervening
//! definitions. The constant-only API retains its original v1 contract.
use crate::model::ir::{Expr, Program, Reg};
use std::sync::Arc;

pub use super::load_order::{
    Error, MAX_ASSIGNMENTS, MAX_BLOCKS, MAX_DEPTH, MAX_FOLDS, MAX_INSTRUCTIONS, MAX_NODES,
    MAX_REGISTERS, MAX_WORK,
};
mod propose;
mod verify;
pub use propose::{propose, propose_with_stable_inputs};
pub use verify::{validate, validate_with_stable_inputs};

pub const MODEL_ID: &str = "checked-strict-load-consumer-v1";
pub const STABLE_MODEL_ID: &str = "checked-stable-load-consumer-v2";
pub const MAX_CONTEXT_INPUTS: usize = 64;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ContextKind {
    Constants,
    StableInputs,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Fold {
    pub load_instruction: u64,
    pub load_assignment: usize,
    pub consumer_instruction: u64,
    pub consumer_assignment: usize,
    pub temporary: Reg,
    pub destination: Reg,
    pub expression: Expr,
    pub inputs: Vec<Reg>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Evidence {
    pub folds: Vec<Fold>,
}

/// Retain the source before presentation changes and the checked paired IR.
/// Control recovery can consume the source while C consumes the lowering.
#[derive(Clone, Debug)]
pub struct Lowering {
    source: Arc<Program>,
    program: Arc<Program>,
    parameters: Vec<Reg>,
    evidence: Evidence,
    context: ContextKind,
}
impl Lowering {
    pub fn source(&self) -> &Program {
        &self.source
    }
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn parameters(&self) -> &[Reg] {
        &self.parameters
    }
    pub fn evidence(&self) -> &Evidence {
        &self.evidence
    }
    pub fn model_id(&self) -> &'static str {
        match self.context {
            ContextKind::Constants => MODEL_ID,
            ContextKind::StableInputs => STABLE_MODEL_ID,
        }
    }
    pub(crate) fn shared_source(&self) -> Arc<Program> {
        Arc::clone(&self.source)
    }
    pub fn validate(&self) -> Result<(), Error> {
        let actual = match self.context {
            ContextKind::Constants => validate(&self.source, &self.program, &self.parameters)?,
            ContextKind::StableInputs => {
                validate_with_stable_inputs(&self.source, &self.program, &self.parameters)?
            }
        };
        if actual != self.evidence {
            return Err(Error::UnsupportedChange);
        }
        Ok(())
    }
}
pub fn lower(source: &Program, parameters: &[Reg]) -> Option<Lowering> {
    lower_kind(source, parameters, ContextKind::Constants)
}
pub fn lower_with_stable_inputs(source: &Program, parameters: &[Reg]) -> Option<Lowering> {
    lower_kind(source, parameters, ContextKind::StableInputs)
}
fn lower_kind(source: &Program, parameters: &[Reg], context: ContextKind) -> Option<Lowering> {
    let candidate = propose::with_kind(source, parameters, context)?;
    let evidence = verify::with_kind(source, &candidate, parameters, context).ok()?;
    let context = if evidence.folds.iter().all(|f| f.inputs.is_empty()) {
        ContextKind::Constants
    } else {
        context
    };
    Some(Lowering {
        source: Arc::new(source.clone()),
        program: Arc::new(candidate),
        parameters: parameters.to_vec(),
        evidence,
        context,
    })
}
