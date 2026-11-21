use super::{
    MAX_INSTRUCTIONS, MAX_REFERENCES, MAX_REPORT_BYTES, MAX_STRING_BYTES, ObjectReferences,
    ReferenceUse, Target,
};
use crate::binary::elf::RelocationTarget;

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
    fn optional_string(&mut self, s: Option<&str>) -> Option<()> {
        match s {
            Some(s) => self.string(s),
            None => self.raw("null"),
        }
    }
    fn optional_number(&mut self, n: Option<impl std::fmt::Display>) -> Option<()> {
        match n {
            Some(n) => self.number(n),
            None => self.raw("null"),
        }
    }
    fn target(&mut self, t: Option<&Target>) -> Option<()> {
        match t {
            None => self.raw("null"),
            Some(Target::Section { index, offset }) => {
                self.raw("{\"kind\":\"section\",\"section\":")?;
                self.number(index)?;
                self.raw(",\"offset\":")?;
                self.number(offset)?;
                self.raw("}")
            }
            Some(Target::External { name, addend }) => {
                self.raw("{\"kind\":\"external\",\"name\":")?;
                self.string(name)?;
                self.raw(",\"addend\":")?;
                self.number(addend)?;
                self.raw("}")
            }
            Some(Target::Absolute(value)) => {
                self.raw("{\"kind\":\"absolute\",\"value\":")?;
                self.number(value)?;
                self.raw("}")
            }
        }
    }
}

pub(super) fn render(report: &ObjectReferences) -> Option<String> {
    if report.references.len() > MAX_REFERENCES
        || report.calls.len() > MAX_INSTRUCTIONS
        || report.literals.len() > MAX_REFERENCES
        || report
            .literals
            .iter()
            .any(|l| l.bytes.len() > MAX_STRING_BYTES)
        || report
            .calls
            .iter()
            .any(|c| c.integer_argument_registers.len() > 6)
    {
        return None;
    }
    let mut out = Json(String::new());
    out.raw("{\"schema\":\"nirvana-object-references-v1\",\"analysis\":\"static-file-references\",\"abi\":\"sysv-x86-64-integer-registers\",\"call_effects\":\"opaque\",\"function\":{\"name\":")?;
    out.string(&report.function)?;
    out.raw(",\"section\":")?;
    out.number(report.section)?;
    out.raw(",\"section_offset\":")?;
    out.number(report.section_offset)?;
    out.raw(",\"size\":")?;
    out.number(report.function_size)?;
    out.raw("},\"references\":[")?;
    for (id, r) in report.references.iter().enumerate() {
        if id > 0 {
            out.raw(",")?;
        }
        let raw = &r.relocation;
        out.raw("{\"id\":")?;
        out.number(id)?;
        out.raw(",\"offset\":")?;
        out.number(raw.offset)?;
        out.raw(",\"relocation_type\":")?;
        out.number(raw.kind)?;
        out.raw(",\"field_width\":")?;
        out.optional_number(raw.width)?;
        out.raw(",\"addend\":")?;
        out.optional_number(raw.addend)?;
        out.raw(",\"symbol_table\":")?;
        out.number(raw.symbol_table)?;
        out.raw(",\"symbol_index\":")?;
        out.number(raw.symbol_index)?;
        out.raw(",\"symbol_kind\":")?;
        out.number(raw.symbol_kind)?;
        out.raw(",\"symbol\":")?;
        out.optional_string(raw.symbol.as_deref())?;
        out.raw(",\"symbol_target\":")?;
        match raw.target {
            RelocationTarget::Undefined => out.raw("{\"kind\":\"undefined\"}")?,
            RelocationTarget::Section { index, offset } => {
                out.target(Some(&Target::Section { index, offset }))?
            }
            RelocationTarget::Absolute(value) => out.target(Some(&Target::Absolute(value)))?,
            RelocationTarget::Reserved(index) => {
                out.raw("{\"kind\":\"reserved\",\"index\":")?;
                out.number(index)?;
                out.raw("}")?;
            }
        }
        out.raw(",\"instruction\":")?;
        out.optional_number(r.instruction)?;
        out.raw(",\"use\":")?;
        out.optional_string(r.usage.map(|u| match u {
            ReferenceUse::Address => "address",
            ReferenceUse::Branch => "branch",
            ReferenceUse::Call => "call",
            ReferenceUse::TailCall => "tail-call",
            ReferenceUse::GotCall => "got-call",
        }))?;
        out.raw(",\"target\":")?;
        out.target(r.target.as_ref())?;
        out.raw(",\"literal\":")?;
        out.optional_number(r.literal)?;
        out.raw("}")?;
    }
    out.raw("],\"literals\":[")?;
    for (id, l) in report.literals.iter().enumerate() {
        if id > 0 {
            out.raw(",")?;
        }
        out.raw("{\"id\":")?;
        out.number(id)?;
        out.raw(",\"kind\":\"nul-terminated-file-bytes\",\"section\":")?;
        out.number(l.section)?;
        out.raw(",\"section_name\":")?;
        out.optional_string(l.section_name.as_deref())?;
        out.raw(",\"offset\":")?;
        out.number(l.offset)?;
        out.raw(",\"bytes\":[")?;
        for (i, b) in l.bytes.iter().enumerate() {
            if i > 0 {
                out.raw(",")?;
            }
            out.number(b)?;
        }
        out.raw("],\"c_literal\":")?;
        out.string(&l.c_literal())?;
        out.raw("}")?;
    }
    out.raw("],\"calls\":[")?;
    for (i, c) in report.calls.iter().enumerate() {
        if i > 0 {
            out.raw(",")?;
        }
        out.raw("{\"instruction\":")?;
        out.number(c.instruction)?;
        out.raw(",\"tail\":")?;
        out.raw(if c.tail { "true" } else { "false" })?;
        out.raw(",\"target\":")?;
        out.target(c.target.as_ref())?;
        out.raw(",\"symbol\":")?;
        out.optional_string(c.symbol.as_deref())?;
        out.raw(",\"integer_argument_registers\":[")?;
        for (i, arg) in c.integer_argument_registers.iter().enumerate() {
            if i > 0 {
                out.raw(",")?;
            }
            out.raw("{\"register\":")?;
            out.number(arg.register)?;
            out.raw(",\"target\":")?;
            out.target(arg.target.as_ref())?;
            out.raw(",\"literal\":")?;
            out.optional_number(arg.literal)?;
            out.raw("}")?;
        }
        out.raw("],\"source_hint\":")?;
        out.optional_string(report.call_hint(c).as_deref())?;
        out.raw("}")?;
    }
    out.raw("]}\n")?;
    Some(out.0)
}
