//! Tentative record types from SSA value flow and observed field accesses.
//!
//! Compatibility classes describe possible common layouts, independently of
//! exact value aliases. They are inspection metadata; checked guest execution
//! keeps its original memory operations and register values.

use crate::dataflow::ssa::{Site, ValueId};
use crate::model::ir::{Program, Reg, Width};

mod infer;
mod report;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstraintKind {
    Copy,
    Phi,
    Select,
    Stack,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Constraint {
    pub from: ValueId,
    pub to: ValueId,
    pub kind: ConstraintKind,
    pub site: Option<Site>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Field {
    pub offset: u64,
    pub width: Width,
    pub reads: bool,
    pub writes: bool,
    pub loaded_values: Vec<ValueId>,
    pub pointer_targets: Vec<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Record {
    pub id: usize,
    /// Actual affine address bases observed in this compatibility class.
    pub bases: Vec<ValueId>,
    pub values: Vec<ValueId>,
    pub fields: Vec<Field>,
    /// Member values with a proven/syntactic zero alternative in their flow.
    pub null_alternatives: Vec<ValueId>,
    /// Source comparisons with zero, without a reachability claim for null.
    pub null_tests: Vec<Site>,
    pub overlaps: Vec<(usize, usize)>,
    /// Negative or greater-than-4096 field offsets retained as omissions.
    pub excluded_offsets: usize,
}

#[derive(Clone, Debug)]
pub struct Analysis {
    pub records: Vec<Record>,
    pub constraints: Vec<Constraint>,
    pub skipped_stack_flows: usize,
}

/// Analyze the supplied source afresh, avoiding stale type/address evidence.
/// Stack transfers are optional and require the caller's explicit stack ABI.
pub fn analyze(source: &Program, stack_register: Option<Reg>) -> Result<Analysis, String> {
    let types = crate::dataflow::type_infer::TypeAnalysis::analyze(source)
        .ok_or("record source type analysis unavailable")?;
    infer::analyze(source, &types, stack_register)
}

impl Analysis {
    pub fn to_json(&self) -> Result<String, String> {
        report::json(self)
    }
    /// Candidate x86-64 declarations for inspection, separate from executing C.
    pub fn to_c(&self) -> Result<String, String> {
        report::declarations(self)
    }
}

pub(crate) fn report_result(value: &Result<Analysis, String>) -> Result<String, String> {
    match value {
        Ok(analysis) => analysis.to_json(),
        Err(reason) => report::unavailable(reason),
    }
}
