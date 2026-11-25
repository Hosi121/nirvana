//! Optional retention of the selected render's actual storage-analysis input.
//! Capture never participates in rendering or candidate ranking. Bounds and
//! their source phase travel together until the final source can be retained.

use std::mem::size_of;
use std::sync::Arc;

use crate::control_flow::cfg::{BasicBlock, BlockId, Edge, Instruction};
use crate::dataflow::value_width::{ValidationError, ValueWidths};
use crate::model::ir::{Assignment, Control, Expr, IrInstruction, Place, Program, Reg, Width};

#[cfg(test)]
mod tests;

/// Resource limits for optional storage provenance, separate from inference.
/// `retained_bytes` bounds conservative source/certificate storage accounting;
/// it is not a measurement of allocator overhead or the whole emission process.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StorageCaptureLimits {
    pub points: usize,
    pub expressions: usize,
    pub depth: usize,
    pub retained_bytes: usize,
}

pub const STORAGE_CAPTURE_LIMITS: StorageCaptureLimits = StorageCaptureLimits {
    points: 100_000,
    expressions: 100_000,
    depth: 128,
    retained_bytes: 16 * 1024 * 1024,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StorageSourcePhase {
    /// Web/load-mask selection, before width-dependent presentation rewrites.
    BeforePresentation,
    /// The accepted display-DCE result on which storage bounds were rebuilt.
    DisplayAfterDce,
}

/// The actual analysis consumed by allocation of the selected C locals.
/// This is not the raw machine-IR analysis, a recovered source type, or proof
/// of emitted C. `widths.verification()` reports the retained check outcome.
#[derive(Clone, Debug)]
pub struct StorageSnapshot {
    pub source: Arc<Program>,
    pub widths: ValueWidths,
    pub source_phase: StorageSourcePhase,
}

#[derive(Clone, Debug, Default)]
pub enum StorageProvenance {
    #[default]
    NotCaptured,
    /// Capture limits do not change C generation or candidate selection.
    Unavailable(&'static str),
    /// A known-invalid consumed proposal must not become merely unavailable
    /// when optional source retention is omitted. Rendering uses U64 fallback.
    Rejected(&'static str),
    Captured(Arc<StorageSnapshot>),
}

#[derive(Clone, Copy)]
pub(super) enum CapturePolicy {
    Off,
    On(StorageCaptureLimits),
}

/// Every accepted width replacement carries its binding phase with it. The
/// initial input remains borrowed by preparation, so no source clone is needed
/// until preparation finishes and only if that input still supplies the bounds.
pub(super) struct WidthAnalysis {
    widths: ValueWidths,
    phase: StorageSourcePhase,
}

impl WidthAnalysis {
    pub fn before_presentation(source: &Program) -> Self {
        Self {
            widths: ValueWidths::analyze(source),
            phase: StorageSourcePhase::BeforePresentation,
        }
    }

    pub fn after_dce(source: &Program) -> Self {
        Self {
            widths: ValueWidths::analyze(source),
            phase: StorageSourcePhase::DisplayAfterDce,
        }
    }

    pub fn width(&self, register: Reg) -> Width {
        self.widths.width(register)
    }

    pub fn finish(
        self,
        policy: CapturePolicy,
        before_presentation: &Program,
        display: &Arc<Program>,
    ) -> (ValueWidths, StorageProvenance) {
        let CapturePolicy::On(limits) = policy else {
            return (self.widths, StorageProvenance::NotCaptured);
        };
        if let Err(ValidationError::Invalid(reason)) = self.widths.verification() {
            let reason = *reason;
            return (self.widths, StorageProvenance::Rejected(reason));
        }
        let source = match self.phase {
            StorageSourcePhase::BeforePresentation => before_presentation,
            StorageSourcePhase::DisplayAfterDce => display.as_ref(),
        };
        if let Err(reason) = preflight(source, &self.widths, limits) {
            return (self.widths, StorageProvenance::Unavailable(reason));
        }
        let source = match self.phase {
            StorageSourcePhase::BeforePresentation => Arc::new(before_presentation.clone()),
            StorageSourcePhase::DisplayAfterDce => Arc::clone(display),
        };
        let snapshot = StorageSnapshot {
            source,
            widths: self.widths.clone(),
            source_phase: self.phase,
        };
        (self.widths, StorageProvenance::Captured(Arc::new(snapshot)))
    }
}

struct Budget {
    limits: StorageCaptureLimits,
    points: usize,
    expressions: usize,
    bytes: usize,
}

impl Budget {
    fn bytes(&mut self, count: usize, size: usize) -> Result<(), &'static str> {
        self.bytes = count
            .checked_mul(size)
            .and_then(|n| self.bytes.checked_add(n))
            .filter(|&n| n <= self.limits.retained_bytes)
            .ok_or("storage capture retained-byte limit")?;
        Ok(())
    }

    fn points(&mut self, count: usize) -> Result<(), &'static str> {
        self.points = self
            .points
            .checked_add(count)
            .filter(|&n| n <= self.limits.points)
            .ok_or("storage capture point limit")?;
        Ok(())
    }

    fn expression(&mut self, root: &Expr) -> Result<(), &'static str> {
        let mut pending = vec![(root, 0usize)];
        while let Some((expression, depth)) = pending.pop() {
            if depth > self.limits.depth {
                return Err("storage capture expression-depth limit");
            }
            self.expressions = self
                .expressions
                .checked_add(1)
                .filter(|&n| n <= self.limits.expressions)
                .ok_or("storage capture expression-node limit")?;
            // Include inline roots as well as boxed children, and allow for
            // allocation bookkeeping. This deliberately overcounts Expr slots.
            self.bytes(1, size_of::<Expr>() + 16)?;
            match expression {
                Expr::Const(_) | Expr::Register(_) => {}
                Expr::Unary(_, value) | Expr::Load { address: value, .. } => {
                    pending.push((value, depth + 1));
                }
                Expr::Binary(_, left, right) => {
                    pending.extend([(&**right, depth + 1), (&**left, depth + 1)]);
                }
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([
                    (&**not_taken, depth + 1),
                    (&**taken, depth + 1),
                    (&**condition, depth + 1),
                ]),
            }
        }
        Ok(())
    }
}

/// Scan before retaining an Arc or cloning the earlier input. In particular a
/// failed/limited inference must not authorize retaining an unbounded Program.
fn preflight(
    source: &Program,
    widths: &ValueWidths,
    limits: StorageCaptureLimits,
) -> Result<(), &'static str> {
    let mut budget = Budget {
        limits,
        points: 0,
        expressions: 0,
        bytes: 0,
    };
    budget.bytes(1, size_of::<Program>() + size_of::<StorageSnapshot>() + 256)?;
    budget.points(source.instructions().len())?;
    budget.bytes(
        source.instructions().len(),
        size_of::<IrInstruction>() + size_of::<Instruction>(),
    )?;
    // Cfg's per-block map uses a B-tree. Charging 256 bytes per entry also
    // covers its nodes and the cloned successor/predecessor Vec headers.
    budget.bytes(source.cfg().blocks().len(), size_of::<BasicBlock>() + 256)?;
    budget.bytes(source.register_count(), size_of::<Width>())?;
    for block in source.cfg().blocks() {
        budget.bytes(block.successors.len(), size_of::<Edge>())?;
        budget.bytes(block.predecessors.len(), size_of::<BlockId>())?;
    }
    for instruction in source.instructions() {
        budget.points(instruction.assignments.len())?;
        budget.bytes(instruction.assignments.len(), size_of::<Assignment>())?;
        for assignment in &instruction.assignments {
            if let Place::Memory { address, .. } = &assignment.destination {
                budget.expression(address)?;
            }
            budget.expression(&assignment.value)?;
        }
        if let Control::Branch { condition, .. } | Control::Return(condition) = &instruction.control
        {
            budget.expression(condition)?;
        }
    }
    if let Some(rows) = widths.incoming() {
        budget.bytes(rows.len(), size_of::<Option<Vec<u8>>>() + size_of::<u64>())?;
        for row in rows.iter().flatten() {
            budget.bytes(row.len(), size_of::<u8>())?;
        }
    }
    Ok(())
}
