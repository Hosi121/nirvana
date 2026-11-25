//! Retained source-entry storage observations and their complete candidate.
//! This record is neither source-language typing nor an emitted-C proof.

use super::{ValidationError, ValueWidths};
use std::fmt::Display;

const MAX_REPORT_BYTES: usize = 16 * 1024 * 1024;

struct Json {
    text: String,
    limit: usize,
}
impl Json {
    fn raw(&mut self, text: &str) -> Result<(), String> {
        if self
            .text
            .len()
            .checked_add(text.len())
            .is_none_or(|n| n > self.limit)
        {
            return Err("storage width report size limit".into());
        }
        self.text.push_str(text);
        Ok(())
    }

    fn number(&mut self, value: impl Display) -> Result<(), String> {
        self.raw(&value.to_string())
    }

    fn string(&mut self, text: &str) -> Result<(), String> {
        self.raw("\"")?;
        for c in text.chars() {
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
}

pub(super) fn render(value: &ValueWidths) -> Result<String, String> {
    render_bounded(value, MAX_REPORT_BYTES)
}

fn render_bounded(value: &ValueWidths, limit: usize) -> Result<String, String> {
    let mut out = Json {
        text: String::new(),
        limit,
    };
    out.raw("{\"schema\":\"nirvana-storage-widths-v1\",\"scope\":\"source-entry-storage-observations\",\"status\":")?;
    match value.verification() {
        Err(error) => {
            out.string(match error {
                ValidationError::Unavailable(_) => "unavailable",
                ValidationError::Invalid(_) => "rejected",
            })?;
            out.raw(",\"evidence\":null,\"widths\":null,\"incoming\":null,\"entry_block\":null,\"block_starts\":null,\"reason\":")?;
            out.string(&error.to_string())?;
        }
        Ok(evidence) => {
            out.raw("\"checked\",\"evidence\":{\"registers\":")?;
            out.number(evidence.registers)?;
            for (name, count) in [
                ("narrow_registers", evidence.narrow_registers),
                ("blocks", evidence.blocks),
                ("edges", evidence.edges),
                ("assignments", evidence.assignments),
                ("reads", evidence.reads),
                ("expressions", evidence.expressions),
            ] {
                out.raw(",")?;
                out.string(name)?;
                out.raw(":")?;
                out.number(count)?;
            }
            out.raw("},\"widths\":[")?;
            for (index, width) in value
                .widths()
                .ok_or("storage width report missing widths")?
                .iter()
                .enumerate()
            {
                if index != 0 {
                    out.raw(",")?;
                }
                out.number(width.bits())?;
            }
            out.raw("],\"incoming\":[")?;
            for (index, row) in value
                .incoming()
                .ok_or("storage width report missing incoming")?
                .iter()
                .enumerate()
            {
                if index != 0 {
                    out.raw(",")?;
                }
                match row {
                    None => out.raw("null")?,
                    Some(row) => {
                        out.raw("[")?;
                        for (register, bits) in row.iter().enumerate() {
                            if register != 0 {
                                out.raw(",")?;
                            }
                            out.number(bits)?;
                        }
                        out.raw("]")?;
                    }
                }
            }
            out.raw("],\"entry_block\":")?;
            out.number(
                value
                    .entry_block
                    .ok_or("storage width report missing entry")?,
            )?;
            out.raw(",\"block_starts\":[")?;
            for (index, start) in value
                .block_starts
                .as_ref()
                .ok_or("storage width report missing blocks")?
                .iter()
                .enumerate()
            {
                if index != 0 {
                    out.raw(",")?;
                }
                out.number(start)?;
            }
            out.raw("],\"reason\":null")?;
        }
    }
    out.raw("}")?;
    Ok(out.text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::ir::{Assignment, Control, Expr, IrInstruction, Program, Reg, Width};
    use std::sync::Arc;

    fn source() -> Program {
        Program::new(
            16,
            2,
            vec![
                IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(Expr::Const(0)),
                },
                IrInstruction {
                    address: 16,
                    size: 1,
                    assignments: vec![Assignment {
                        destination: Reg(1).into(),
                        value: Expr::Const(255),
                    }],
                    control: Control::Return(Expr::Register(Reg(1))),
                },
            ],
        )
        .unwrap()
    }

    #[test]
    fn successful_report_retains_replayable_dense_rows_and_clones_share_them() {
        let source = source();
        let widths = ValueWidths::analyze(&source);
        assert_eq!(widths.widths(), Some([Width::U64, Width::U8].as_slice()));
        let incoming = widths.incoming().unwrap();
        assert!(incoming[0].is_none());
        assert_eq!(incoming[1], Some(vec![64, 64]));
        assert_eq!(
            super::super::validate(&source, widths.widths().unwrap(), incoming).as_ref(),
            widths.verification()
        );
        let cloned = widths.clone();
        assert!(Arc::ptr_eq(
            widths.incoming.as_ref().unwrap(),
            cloned.incoming.as_ref().unwrap()
        ));
        let report = widths.to_json().unwrap();
        assert!(report.contains("\"status\":\"checked\""));
        assert!(report.contains("\"widths\":[64,8],\"incoming\":[null,[64,64]],\"entry_block\":1,\"block_starts\":[0,16]"));
        assert!(report.contains("\"assignments\":1,\"reads\":1,\"expressions\":2"));
        assert!(report.ends_with("\"reason\":null}"));
        assert_eq!(cloned.to_json().unwrap(), report);
        assert!(render_bounded(&widths, report.len() - 1).is_err());
        assert_eq!(render_bounded(&widths, report.len()).unwrap(), report);
    }

    #[test]
    fn rejected_and_unavailable_reports_publish_no_partial_certificate() {
        let source = source();
        let rejected = ValueWidths::checked(&source, vec![Width::U64; 2], vec![]);
        for (value, expected) in [
            (ValueWidths::default(), "unavailable"),
            (rejected, "rejected"),
        ] {
            assert!(value.widths().is_none());
            assert!(value.incoming().is_none());
            assert_eq!(value.width(Reg(1)), Width::U64);
            let report = value.to_json().unwrap();
            assert!(report.contains(&format!("\"status\":\"{expected}\"")));
            assert!(report.contains("\"evidence\":null,\"widths\":null,\"incoming\":null,\"entry_block\":null,\"block_starts\":null"));
            assert!(!report.contains("\"reason\":null"));
        }
    }
}
