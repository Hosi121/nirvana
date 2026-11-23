//! Flat-memory snapshots for independent replay of observed state equality.
use nirvana::ir::{AccessKind, RunReport, RunStatus};

pub(super) const MAX_BYTES: usize = 128 * 1024 * 1024;
pub(super) const MAX_LINE_BYTES: usize = 4 * 1024 * 1024;
pub(super) const FILE: &str = "selected-semantic-states.jsonl";

pub(super) fn snapshot(report: &RunReport) -> Option<String> {
    if report.state.memory_layout.is_some() {
        return None;
    }
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
    let pc = report
        .state
        .instruction
        .map_or("null".into(), |pc| pc.to_string());
    Some(format!(
        "{{\"status\":{status:?},\"registers\":{:?},\"memory_base\":{},\"memory\":{:?},\"instruction\":{pc},\"trace\":{:?}}}",
        report.state.registers, report.state.memory_base, report.state.memory, report.state.trace
    ))
}

pub(super) fn middle_pair(
    case: usize,
    budget: usize,
    variant: &str,
    input: &[u64],
    expected: &RunReport,
    actual: &RunReport,
) -> Option<String> {
    Some(format!(
        "{{\"case\":{case},\"budget\":{budget},\"variant\":\"{variant}\",\"input\":{input:?},\"expected\":{},\"actual\":{}}}\n",
        snapshot(expected)?,
        snapshot(actual)?
    ))
}

pub(super) fn pair(
    case: usize,
    budget: usize,
    initial: u64,
    input: &[u64],
    expected: &RunReport,
    actual: &RunReport,
) -> Option<String> {
    Some(format!(
        "{{\"case\":{case},\"budget\":{budget},\"fresh\":{initial},\"input\":{input:?},\"expected\":{},\"actual\":{}}}\n",
        snapshot(expected)?,
        snapshot(actual)?
    ))
}
