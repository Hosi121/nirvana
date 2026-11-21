use super::{Analysis, BoundaryKind, CallContract, FunctionValues, MAX_FUNCTIONS, PointRole};
use crate::ir::Reg;
use crate::ssa::{Definition, RegisterValue, Site, ValueId};
use crate::value_liveness::Use;

const MAX_REPORT_BYTES: usize = 64 * 1024 * 1024;

struct Json(String);
impl Json {
    fn raw(&mut self, s: &str) -> Option<()> {
        if self.0.len().checked_add(s.len())? > MAX_REPORT_BYTES {
            return None;
        }
        self.0.push_str(s);
        Some(())
    }
    fn number(&mut self, n: impl std::fmt::Display) -> Option<()> {
        self.raw(&n.to_string())
    }
    fn string(&mut self, s: &str) -> Option<()> {
        self.raw("\"")?;
        for c in s.chars() {
            match c {
                '"' => self.raw("\\\"")?,
                '\\' => self.raw("\\\\")?,
                '\n' => self.raw("\\n")?,
                '\r' => self.raw("\\r")?,
                '\t' => self.raw("\\t")?,
                c if c < ' ' => self.raw(&format!("\\u{:04x}", u32::from(c)))?,
                c => self.raw(c.encode_utf8(&mut [0; 4]))?,
            }
        }
        self.raw("\"")
    }
    fn optional_number(&mut self, n: Option<u64>) -> Option<()> {
        match n {
            Some(n) => self.number(n),
            None => self.raw("null"),
        }
    }
    fn site(&mut self, site: Site) -> Option<()> {
        self.raw("{\"instruction\":")?;
        self.number(site.instruction)?;
        self.raw(",\"assignment\":")?;
        match site.assignment {
            Some(n) => self.number(n)?,
            None => self.raw("null")?,
        }
        self.raw("}")
    }
    fn ids(&mut self, ids: &[ValueId]) -> Option<()> {
        self.raw("[")?;
        for (i, id) in ids.iter().enumerate() {
            if i > 0 {
                self.raw(",")?;
            }
            self.number(id.0)?;
        }
        self.raw("]")
    }
    fn registers(&mut self, reads: &[RegisterValue]) -> Option<()> {
        self.raw("[")?;
        for (i, rv) in reads.iter().enumerate() {
            if i > 0 {
                self.raw(",")?;
            }
            self.raw("{\"register\":")?;
            self.number(rv.register.0)?;
            self.raw(",\"value\":")?;
            self.number(rv.value.0)?;
            self.raw("}")?;
        }
        self.raw("]")
    }
    fn raw_registers(&mut self, registers: &[Reg]) -> Option<()> {
        self.raw("[")?;
        for (i, register) in registers.iter().enumerate() {
            if i > 0 {
                self.raw(",")?;
            }
            self.number(register.0)?;
        }
        self.raw("]")
    }
    fn summary(&mut self, summary: &crate::call_footprint::FunctionSummary) -> Option<()> {
        self.raw("{\"closed\":")?;
        self.raw(if summary.closed { "true" } else { "false" })?;
        self.raw(",\"reason\":")?;
        match &summary.reason {
            Some(reason) => self.string(reason)?,
            None => self.raw("null")?,
        }
        self.raw(",\"reads\":")?;
        self.raw_registers(&summary.reads)?;
        self.raw(",\"clobbers\":")?;
        self.raw_registers(&summary.clobbers)?;
        self.raw(",\"preserved\":")?;
        self.raw_registers(&summary.preserved)?;
        self.raw(",\"callees\":[")?;
        for (i, callee) in summary.callees.iter().enumerate() {
            if i > 0 {
                self.raw(",")?;
            }
            self.number(callee)?;
        }
        self.raw("]}")
    }
    fn role(&mut self, role: Option<&PointRole>) -> Option<()> {
        let (name, original, register) = match role {
            Some(PointRole::Assignment { original }) => ("assignment", Some(*original), None),
            Some(PointRole::VectorAssignment { original }) => {
                ("vector-assignment", Some(*original), None)
            }
            Some(PointRole::VectorGuard) => ("vector-guard", None, None),
            Some(PointRole::DivideSource) => ("divide-source", None, None),
            Some(PointRole::Target) => ("transfer-target", None, None),
            Some(PointRole::Input { register }) => ("boundary-input", None, Some(register.0)),
            Some(PointRole::OpaqueOutput { register }) => ("opaque-output", None, Some(register.0)),
            None => ("control", None, None),
        };
        self.raw("{\"kind\":")?;
        self.string(name)?;
        if let Some(original) = original {
            self.raw(",\"source_assignment\":")?;
            self.number(original)?;
        }
        if let Some(register) = register {
            self.raw(",\"guest_register\":")?;
            self.number(register)?;
        }
        self.raw("}")
    }
    fn definition(&mut self, definition: &Definition, values: &FunctionValues) -> Option<()> {
        match definition {
            Definition::Initial { register } => {
                self.raw("{\"kind\":")?;
                self.string(if register.0 == values.guest_registers {
                    "analysis-scratch"
                } else {
                    "initial"
                })?;
                self.raw(",\"register\":")?;
                self.number(register.0)?;
            }
            Definition::Assignment { site, register } => {
                let role = values.roles.get(site);
                self.raw("{\"kind\":")?;
                self.string(match role {
                    Some(PointRole::OpaqueOutput { .. }) => "opaque-output",
                    Some(
                        PointRole::Input { .. }
                        | PointRole::Target
                        | PointRole::VectorGuard
                        | PointRole::DivideSource,
                    ) => "observation",
                    _ => "assignment",
                })?;
                self.raw(",\"register\":")?;
                self.number(register.0)?;
                self.raw(",\"site\":")?;
                self.site(*site)?;
                self.raw(",\"role\":")?;
                self.role(role)?;
            }
            Definition::Phi {
                block,
                register,
                inputs,
            } => {
                self.raw("{\"kind\":\"phi\",\"block\":")?;
                self.number(block)?;
                self.raw(",\"register\":")?;
                self.number(register.0)?;
                self.raw(",\"inputs\":[")?;
                for (i, input) in inputs.iter().enumerate() {
                    if i > 0 {
                        self.raw(",")?;
                    }
                    self.raw("{\"predecessor\":")?;
                    self.optional_number(input.predecessor)?;
                    self.raw(",\"value\":")?;
                    self.number(input.value.0)?;
                    self.raw("}")?;
                }
                self.raw("]")?;
            }
        }
        self.raw("}")
    }
    fn function(&mut self, values: &FunctionValues) -> Option<()> {
        self.raw(",\"local_recovery\":{")?;
        match &values.locals {
            Err(reason) => {
                self.raw("\"status\":\"unavailable\",\"reason\":")?;
                self.string(reason)?;
            }
            Ok(recovery) => {
                self.raw("\"status\":\"available\",\"locals\":")?;
                self.number(recovery.plan.local_count)?;
                self.raw(",\"ssa_values\":")?;
                self.number(recovery.stats.ssa_values)?;
                self.raw(",\"phi_inputs\":")?;
                self.number(recovery.stats.phi_inputs)?;
                self.raw(",\"edge_copies\":")?;
                self.number(recovery.stats.edge_copies)?;
                self.raw(",\"temporary_edges\":")?;
                self.number(recovery.stats.temporary_edges)?;
                self.raw(",\"by_value\":[")?;
                for (i, local) in recovery.plan.by_value.iter().enumerate() {
                    if i > 0 {
                        self.raw(",")?;
                    }
                    self.number(local)?;
                }
                self.raw("],\"edges\":[")?;
                for (i, edge) in recovery.edges.iter().enumerate() {
                    if i > 0 {
                        self.raw(",")?;
                    }
                    self.raw("{\"from\":")?;
                    self.optional_number(edge.from)?;
                    self.raw(",\"to\":")?;
                    self.number(edge.to)?;
                    self.raw(",\"parallel\":[")?;
                    for (i, copy) in edge.parallel.iter().enumerate() {
                        if i > 0 {
                            self.raw(",")?;
                        }
                        self.raw("[")?;
                        self.number(copy.destination)?;
                        self.raw(",")?;
                        self.number(copy.source)?;
                        self.raw("]")?;
                    }
                    self.raw("],\"sequential\":[")?;
                    for (i, copy) in edge.schedule.copies.iter().enumerate() {
                        if i > 0 {
                            self.raw(",")?;
                        }
                        self.raw("[")?;
                        self.number(copy.destination)?;
                        self.raw(",")?;
                        self.number(copy.source)?;
                        self.raw("]")?;
                    }
                    self.raw("]}")?;
                }
                self.raw("]")?;
            }
        }
        self.raw("}")?;
        self.raw(",\"guest_registers\":")?;
        self.number(values.guest_registers)?;
        self.raw(",\"analysis_scratch_register\":")?;
        self.number(values.guest_registers)?;
        self.raw(",\"source_instructions\":")?;
        self.number(values.source_instructions)?;
        self.raw(",\"peak_live\":")?;
        self.number(values.lifetimes.peak_live)?;
        self.raw(",\"values\":[")?;
        for (id, (definition, lifetime)) in values
            .graph
            .values
            .iter()
            .zip(&values.lifetimes.values)
            .enumerate()
        {
            if id > 0 {
                self.raw(",")?;
            }
            self.raw("{\"id\":")?;
            self.number(id)?;
            self.raw(",\"definition\":")?;
            self.definition(definition, values)?;
            self.raw(",\"uses\":[")?;
            for (i, usage) in lifetime.uses.iter().enumerate() {
                if i > 0 {
                    self.raw(",")?;
                }
                match usage {
                    Use::Point { site, read } => {
                        self.raw("{\"kind\":\"point\",\"site\":")?;
                        self.site(*site)?;
                        self.raw(",\"read\":")?;
                        self.number(read)?;
                    }
                    Use::Phi { value, predecessor } => {
                        self.raw("{\"kind\":\"phi\",\"value\":")?;
                        self.number(value.0)?;
                        self.raw(",\"predecessor\":")?;
                        self.optional_number(*predecessor)?;
                    }
                }
                self.raw("}")?;
            }
            self.raw("],\"live_blocks\":[")?;
            for (i, block) in lifetime.live_blocks.iter().enumerate() {
                if i > 0 {
                    self.raw(",")?;
                }
                self.number(block)?;
            }
            self.raw("]}")?;
        }
        self.raw("],\"blocks\":[")?;
        for (i, (block, live)) in values
            .graph
            .blocks
            .iter()
            .zip(&values.lifetimes.blocks)
            .enumerate()
        {
            if i > 0 {
                self.raw(",")?;
            }
            self.raw("{\"start\":")?;
            self.number(block.start)?;
            self.raw(",\"live_in\":")?;
            self.ids(&live.live_in)?;
            self.raw(",\"live_out\":")?;
            self.ids(&live.live_out)?;
            self.raw(",\"points\":[")?;
            for (i, (point, lifetime)) in block.points.iter().zip(&live.points).enumerate() {
                if i > 0 {
                    self.raw(",")?;
                }
                self.raw("{\"site\":")?;
                self.site(point.site)?;
                self.raw(",\"role\":")?;
                self.role(values.roles.get(&point.site))?;
                self.raw(",\"definition\":")?;
                match point.definition {
                    Some(id) => self.number(id.0)?,
                    None => self.raw("null")?,
                }
                self.raw(",\"reads\":")?;
                self.registers(&point.reads)?;
                self.raw(",\"before\":")?;
                self.ids(&lifetime.before)?;
                self.raw(",\"after\":")?;
                self.ids(&lifetime.after)?;
                self.raw("}")?;
            }
            self.raw("]}")?;
        }
        self.raw("],\"edges\":[")?;
        for (i, edge) in values.lifetimes.edges.iter().enumerate() {
            if i > 0 {
                self.raw(",")?;
            }
            self.raw("{\"from\":")?;
            self.optional_number(edge.from)?;
            self.raw(",\"to\":")?;
            self.number(edge.to)?;
            self.raw(",\"live\":")?;
            self.ids(&edge.live)?;
            self.raw("}")?;
        }
        self.raw("],\"boundaries\":[")?;
        for (i, boundary) in values.boundaries.iter().enumerate() {
            if i > 0 {
                self.raw(",")?;
            }
            self.raw("{\"address\":")?;
            self.number(boundary.address)?;
            self.raw(",\"kind\":")?;
            self.string(match boundary.kind {
                BoundaryKind::Call { .. } => "call",
                BoundaryKind::Divide { .. } => "divide",
                BoundaryKind::Tail => "tail",
                BoundaryKind::Return => "return",
            })?;
            if let BoundaryKind::Call { continuation } | BoundaryKind::Divide { continuation, .. } =
                boundary.kind
            {
                self.raw(",\"continuation\":")?;
                self.number(continuation)?;
            }
            if let BoundaryKind::Divide { width, signed, .. } = boundary.kind {
                self.raw(",\"width\":")?;
                self.number(width.bits())?;
                self.raw(",\"signed\":")?;
                self.raw(if signed { "true" } else { "false" })?;
            }
            self.raw(",\"target_reads\":")?;
            self.registers(&boundary.target_reads)?;
            self.raw(",\"operand_reads\":")?;
            self.registers(&boundary.operand_reads)?;
            self.raw(",\"inputs\":")?;
            self.registers(&boundary.inputs)?;
            self.raw(",\"outputs\":")?;
            self.registers(&boundary.outputs)?;
            self.raw(",\"preserved\":")?;
            self.registers(&boundary.preserved)?;
            self.raw(",\"call_contract\":")?;
            match &boundary.call_contract {
                Some(CallContract::Closed { callee }) => {
                    self.raw("{\"kind\":\"closed\",\"callee\":")?;
                    self.number(callee)?;
                    self.raw("}")?;
                }
                Some(CallContract::Opaque { reason }) => {
                    self.raw("{\"kind\":\"opaque\",\"reason\":")?;
                    self.string(reason)?;
                    self.raw("}")?;
                }
                None => self.raw("null")?,
            }
            self.raw("}")?;
        }
        self.raw("]")
    }
}

pub(super) fn render(analysis: &Analysis) -> Option<String> {
    if analysis.functions.len() > MAX_FUNCTIONS {
        return None;
    }
    let mut out = Json(String::new());
    out.raw("{\"schema\":\"nirvana-module-values-v3\",\"identity\":\"per-function-ssa\",\"scope\":\"function-entry-and-normal-effect-continuations\",\"liveness\":\"syntactic-possible-uses\",\"calls\":\"closed-internal-footprints-with-opaque-fallback\",\"memory\":\"ordered-accesses-and-opaque-call-effects\",\"sites\":\"analysis-event-indices\",\"functions\":[")?;
    for (i, function) in analysis.functions.iter().enumerate() {
        if i > 0 {
            out.raw(",")?;
        }
        out.raw("{\"name\":")?;
        out.string(&function.function.name)?;
        out.raw(",\"address\":")?;
        out.number(function.function.address)?;
        out.raw(",\"size\":")?;
        out.number(function.function.size)?;
        out.raw(",\"call_summary\":")?;
        out.summary(analysis.call_summaries.at(function.function.address)?)?;
        match &function.result {
            Ok(values) => {
                out.raw(",\"status\":\"analyzed\"")?;
                out.function(values)?;
            }
            Err(reason) => {
                out.raw(",\"status\":\"unavailable\",\"reason\":")?;
                out.string(reason)?;
            }
        }
        out.raw("}")?;
    }
    out.raw("]}\n")?;
    Some(out.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn quotes_control_characters_and_unicode() {
        let mut json = Json(String::new());
        json.string("a\"\\\n\r\t\0日本語").unwrap();
        assert_eq!(json.0, "\"a\\\"\\\\\\n\\r\\t\\u0000日本語\"");
    }
}
