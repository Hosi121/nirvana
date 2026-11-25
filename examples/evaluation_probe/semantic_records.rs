//! Flat-memory snapshots for independent replay of observed state equality.
use nirvana::ir::{AccessKind, RunReport, RunStatus};
use std::fmt::{self, Write};

#[path = "semantic_records/registers.rs"]
mod registers;

pub(super) const MAX_BYTES: usize = 128 * 1024 * 1024;
pub(super) const MAX_LINE_BYTES: usize = 4 * 1024 * 1024;
pub(super) const FILE: &str = "selected-semantic-states.jsonl";
pub(super) const ENCODING: &str = "register-rle-u64-v1";

pub(super) struct Record {
    text: String,
    decoded_bytes: usize,
}

#[derive(Default)]
pub(super) struct Buffer {
    records: String,
    decoded_bytes: usize,
}

impl Buffer {
    pub fn push(&mut self, record: Record) -> bool {
        self.push_bounded(record, MAX_LINE_BYTES, MAX_BYTES)
    }

    fn push_bounded(&mut self, record: Record, line_limit: usize, file_limit: usize) -> bool {
        let Some(decoded_bytes) = self.decoded_bytes.checked_add(record.decoded_bytes) else {
            return false;
        };
        let physical_bytes = self.records.len().checked_add(record.text.len());
        if record.decoded_bytes > line_limit
            || record.text.len() > line_limit
            || decoded_bytes > file_limit
            || physical_bytes.is_none_or(|bytes| bytes > file_limit)
        {
            return false;
        }
        self.records.push_str(&record.text);
        self.decoded_bytes = decoded_bytes;
        true
    }

    pub fn as_str(&self) -> &str {
        &self.records
    }

    pub fn decoded_bytes(&self) -> usize {
        self.decoded_bytes
    }
}

struct Snapshot<'a> {
    report: &'a RunReport,
    compressed: bool,
}

impl fmt::Display for Snapshot<'_> {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        let report = self.report;
        let status = match report.status {
            RunStatus::Returned(value) => [0, value, 0, 0],
            RunStatus::Suspended => [2, 0, 0, 0],
            RunStatus::Fault(ref fault) => [
                1,
                fault.address,
                if fault.access == AccessKind::Read {
                    1
                } else {
                    2
                },
                fault.width.bytes() as u64,
            ],
        };
        write!(out, "{{\"status\":{status:?},\"registers\":")?;
        if self.compressed {
            write!(out, "{}", registers::Token(&report.state.registers))?;
        } else {
            write!(out, "{:?}", report.state.registers)?;
        }
        write!(
            out,
            ",\"memory_base\":{},\"memory\":{:?},\"instruction\":",
            report.state.memory_base, report.state.memory
        )?;
        match report.state.instruction {
            Some(pc) => write!(out, "{pc}")?,
            None => out.write_str("null")?,
        }
        write!(out, ",\"trace\":{:?}}}", report.state.trace)
    }
}

enum Pattern<'a> {
    Fresh(u64),
    Variant(&'a str),
}

fn write_pair(
    out: &mut impl Write,
    case: usize,
    budget: usize,
    pattern: &Pattern<'_>,
    input: &[u64],
    expected: Snapshot<'_>,
    actual: Snapshot<'_>,
) -> fmt::Result {
    write!(out, "{{\"case\":{case},\"budget\":{budget},")?;
    match pattern {
        Pattern::Fresh(initial) => write!(out, "\"fresh\":{initial},")?,
        Pattern::Variant(variant) => write!(out, "\"variant\":\"{variant}\",")?,
    }
    writeln!(
        out,
        "\"input\":{input:?},\"expected\":{expected},\"actual\":{actual}}}"
    )
}

struct Counter(usize);
impl Write for Counter {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.0 = self.0.checked_add(text.len()).ok_or(fmt::Error)?;
        Ok(())
    }
}

fn record(
    case: usize,
    budget: usize,
    pattern: Pattern<'_>,
    input: &[u64],
    expected: &RunReport,
    actual: &RunReport,
) -> Option<Record> {
    if expected.state.memory_layout.is_some() || actual.state.memory_layout.is_some() {
        return None;
    }
    // Count the exact old Vec Debug spelling without allocating a dense row.
    // A logically oversized row is rejected by Buffer just as before.
    let mut count = Counter(0);
    let result = write_pair(
        &mut count,
        case,
        budget,
        &pattern,
        input,
        Snapshot {
            report: expected,
            compressed: false,
        },
        Snapshot {
            report: actual,
            compressed: false,
        },
    );
    let decoded_bytes = if result.is_ok() { count.0 } else { usize::MAX };
    let mut text = String::new();
    if decoded_bytes <= MAX_LINE_BYTES {
        // Register encoding never grows a token, so this allocation is bounded
        // by the already checked logical row length.
        write_pair(
            &mut text,
            case,
            budget,
            &pattern,
            input,
            Snapshot {
                report: expected,
                compressed: true,
            },
            Snapshot {
                report: actual,
                compressed: true,
            },
        )
        .ok()?;
    }
    Some(Record {
        text,
        decoded_bytes,
    })
}

pub(super) fn middle_pair(
    case: usize,
    budget: usize,
    variant: &str,
    input: &[u64],
    expected: &RunReport,
    actual: &RunReport,
) -> Option<Record> {
    record(
        case,
        budget,
        Pattern::Variant(variant),
        input,
        expected,
        actual,
    )
}

pub(super) fn pair(
    case: usize,
    budget: usize,
    initial: u64,
    input: &[u64],
    expected: &RunReport,
    actual: &RunReport,
) -> Option<Record> {
    record(
        case,
        budget,
        Pattern::Fresh(initial),
        input,
        expected,
        actual,
    )
}

#[cfg(test)]
#[path = "semantic_records/tests.rs"]
mod tests;
