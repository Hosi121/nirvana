use super::*;
use std::fmt::Write;

const MAX_BYTES: usize = 16 * 1024 * 1024;
const MAX_MEMBERS: usize = 1_000_000;

fn validate(analysis: &Analysis) -> Result<(), String> {
    if analysis.records.len() > 2048 || analysis.constraints.len() > 262_144 {
        return Err("record report collection limit".into());
    }
    let mut members = analysis.constraints.len();
    for (id, record) in analysis.records.iter().enumerate() {
        if id != record.id {
            return Err("record report identity mismatch".into());
        }
        members = members
            .checked_add(
                record.values.len()
                    + record.bases.len()
                    + record.fields.len()
                    + record.null_tests.len()
                    + record.null_alternatives.len()
                    + record.overlaps.len() * 2,
            )
            .ok_or("record report size overflow")?;
        for field in &record.fields {
            members = members
                .checked_add(field.loaded_values.len() + field.pointer_targets.len())
                .ok_or("record report size overflow")?;
            if field
                .offset
                .checked_add(field.width.bytes() as u64)
                .is_none_or(|end| end > 4096)
                || field
                    .pointer_targets
                    .iter()
                    .any(|&n| n >= analysis.records.len())
            {
                return Err("record report field bounds".into());
            }
        }
        if members > MAX_MEMBERS {
            return Err("record report membership limit".into());
        }
    }
    Ok(())
}

fn check(out: &str) -> Result<(), String> {
    if out.len() > MAX_BYTES {
        Err("record report output limit".into())
    } else {
        Ok(())
    }
}

fn ids(out: &mut String, values: impl IntoIterator<Item = usize>) -> Result<(), String> {
    out.push('[');
    for (i, id) in values.into_iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write!(out, "{id}").unwrap();
        check(out)?;
    }
    out.push(']');
    Ok(())
}

fn site(out: &mut String, value: Option<Site>) {
    if let Some(value) = value {
        write!(
            out,
            "{{\"instruction\":{},\"assignment\":{}}}",
            value.instruction,
            value
                .assignment
                .map_or_else(|| "null".into(), |n| n.to_string())
        )
        .unwrap();
    } else {
        out.push_str("null");
    }
}

pub(super) fn json(analysis: &Analysis) -> Result<String, String> {
    validate(analysis)?;
    let mut out = String::from(
        "{\n\"schema\":\"nirvana-record-shapes-v1\",\"identity\":\"ssa\",\"interpretations\":\"tentative\",\"status\":\"available\",\n\"records\":[\n",
    );
    for (i, record) in analysis.records.iter().enumerate() {
        if i > 0 {
            out.push_str(",\n");
        }
        write!(out, "{{\"id\":{},\"bases\":", record.id).unwrap();
        ids(&mut out, record.bases.iter().map(|v| v.0))?;
        out.push_str(",\"values\":");
        ids(&mut out, record.values.iter().map(|v| v.0))?;
        out.push_str(",\"null_alternatives\":");
        ids(&mut out, record.null_alternatives.iter().map(|v| v.0))?;
        out.push_str(",\"null_tests\":[");
        for (j, &s) in record.null_tests.iter().enumerate() {
            if j > 0 {
                out.push(',');
            }
            site(&mut out, Some(s));
            check(&out)?;
        }
        write!(
            out,
            "],\"excluded_offsets\":{},\"fields\":[",
            record.excluded_offsets
        )
        .unwrap();
        for (j, f) in record.fields.iter().enumerate() {
            if j > 0 {
                out.push(',');
            }
            write!(
                out,
                "{{\"offset\":{},\"width\":{},\"reads\":{},\"writes\":{},\"loaded_values\":",
                f.offset,
                f.width.bytes(),
                f.reads,
                f.writes
            )
            .unwrap();
            ids(&mut out, f.loaded_values.iter().map(|v| v.0))?;
            out.push_str(",\"pointer_targets\":");
            ids(&mut out, f.pointer_targets.iter().copied())?;
            out.push('}');
            check(&out)?;
        }
        out.push_str("],\"overlaps\":[");
        for (j, (a, b)) in record.overlaps.iter().enumerate() {
            if j > 0 {
                out.push(',');
            }
            write!(out, "[{a},{b}]").unwrap();
            check(&out)?;
        }
        out.push_str("]}");
    }
    out.push_str("\n],\"constraints\":[\n");
    for (i, c) in analysis.constraints.iter().enumerate() {
        if i > 0 {
            out.push_str(",\n");
        }
        let kind = match c.kind {
            ConstraintKind::Copy => "copy",
            ConstraintKind::Phi => "phi",
            ConstraintKind::Select => "select",
            ConstraintKind::Stack => "stack",
        };
        write!(
            out,
            "{{\"from\":{},\"to\":{},\"kind\":\"{kind}\",\"site\":",
            c.from.0, c.to.0
        )
        .unwrap();
        site(&mut out, c.site);
        out.push('}');
        check(&out)?;
    }
    write!(
        out,
        "\n],\"skipped_stack_flows\":{}\n}}\n",
        analysis.skipped_stack_flows
    )
    .unwrap();
    check(&out)?;
    Ok(out)
}

pub(super) fn unavailable(reason: &str) -> Result<String, String> {
    let mut out = String::from("{\"status\":\"unavailable\",\"reason\":\"");
    for c in reason.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c < ' ' => {
                write!(out, "\\u{:04x}", c as u32).unwrap();
            }
            c => out.push(c),
        }
        check(&out)?;
    }
    out.push_str("\"}");
    check(&out)?;
    Ok(out)
}

pub(super) fn declarations(analysis: &Analysis) -> Result<String, String> {
    validate(analysis)?;
    let mut out = String::from(
        "/* Tentative x86-64 record declarations inferred from value flow and accesses.\n * Checked program execution uses the original guest-memory operations. */\n#include <stdint.h>\n#include <stddef.h>\n_Static_assert(sizeof(void *) == 8, \"record candidates target x86-64\");\n\n",
    );
    for record in &analysis.records {
        writeln!(out, "struct record_{};", record.id).unwrap();
    }
    for record in &analysis.records {
        if record.fields.is_empty() {
            continue;
        }
        let mut end = 0;
        let mut opaque = record.excluded_offsets > 0 || !record.overlaps.is_empty();
        for f in &record.fields {
            opaque |= f.offset < end || f.offset % f.width.bytes() as u64 != 0;
            end = end.max(f.offset + f.width.bytes() as u64);
        }
        writeln!(
            out,
            "\n/* record_{}: {} observed bases, {} compatible SSA values. */\nstruct record_{} {{",
            record.id,
            record.bases.len(),
            record.values.len(),
            record.id
        )
        .unwrap();
        if opaque {
            writeln!(out,"    uint8_t storage[{end}]; /* overlapping, interior or unaligned views; see JSON */\n}};").unwrap();
            continue;
        }
        let mut cursor = 0;
        for f in &record.fields {
            if f.offset > cursor {
                writeln!(out, "    uint8_t padding_{cursor}[{}];", f.offset - cursor).unwrap();
            }
            if f.width == Width::U64 && f.pointer_targets.len() == 1 {
                writeln!(
                    out,
                    "    struct record_{} *field_{};",
                    f.pointer_targets[0], f.offset
                )
                .unwrap();
            } else {
                writeln!(out, "    uint{}_t field_{};", f.width.bits(), f.offset).unwrap();
            }
            cursor = f.offset + f.width.bytes() as u64;
        }
        out.push_str("};\n");
        for f in &record.fields {
            writeln!(out,"_Static_assert(offsetof(struct record_{}, field_{}) == {}, \"inferred field offset\");",record.id,f.offset,f.offset).unwrap();
        }
        check(&out)?;
    }
    check(&out)?;
    Ok(out)
}
