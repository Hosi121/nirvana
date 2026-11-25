use super::*;
use nirvana::ir::{MemoryFault, Snapshot as StateSnapshot, Width};

fn report(registers: Vec<u64>) -> RunReport {
    RunReport {
        status: RunStatus::Returned(u64::MAX),
        state: StateSnapshot {
            registers,
            memory_base: 4224,
            memory: vec![0, 1, 255],
            memory_layout: None,
            trace: vec![0, 1, u64::MAX],
            instruction: Some(99),
        },
    }
}

fn decode_token(text: &str) -> Vec<u64> {
    if let Some(body) = text.strip_prefix("{\"rle\":[") {
        let body = body.strip_suffix("]}").unwrap();
        if body.is_empty() {
            return vec![];
        }
        let mut result = Vec::new();
        let mut previous = None;
        for run in body.split("],[") {
            let run = run.trim_start_matches('[').trim_end_matches(']');
            let (count, value) = run.split_once(',').unwrap();
            let count: usize = count.parse().unwrap();
            let value: u64 = value.parse().unwrap();
            assert!(count > 0);
            assert_ne!(previous, Some(value));
            result.extend(std::iter::repeat_n(value, count));
            previous = Some(value);
        }
        result
    } else {
        let body = text.strip_prefix('[').unwrap().strip_suffix(']').unwrap();
        if body.is_empty() {
            vec![]
        } else {
            body.split(", ")
                .map(|value| value.parse().unwrap())
                .collect()
        }
    }
}

fn check_token(values: &[u64]) {
    let token = registers::Token(values).to_string();
    let dense = format!("{values:?}");
    let (dense_bytes, rle_bytes) = registers::token_lengths(values);
    assert_eq!(dense_bytes, dense.len());
    assert_eq!(decode_token(&token), values);
    assert_eq!(token.len(), dense_bytes.min(rle_bytes));
    if rle_bytes >= dense_bytes {
        assert_eq!(token, dense);
    } else {
        assert!(token.starts_with("{\"rle\":["));
        assert!(!token.contains(' '));
    }
}

#[test]
fn boundary_and_random_registers_round_trip_with_only_strictly_shorter_rle() {
    for length in [0, 1, 2, 5, 6, 9, 10, 99, 100, 999, 1000] {
        for value in [0, 1, 9, 10, 99, 100, 255, u64::MAX] {
            check_token(&vec![value; length]);
        }
        check_token(
            &(0..length)
                .map(|index| index as u64 % 2)
                .collect::<Vec<_>>(),
        );
    }
    assert_eq!(registers::Token(&[0; 5]).to_string(), "[0, 0, 0, 0, 0]");
    assert_eq!(registers::Token(&[0; 6]).to_string(), "{\"rle\":[[6,0]]}");
    let mut seed = 0x726c_652d_7631_1234u64;
    for _ in 0..128 {
        let mut values = Vec::new();
        for _ in 0..32 {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            let value = match seed & 3 {
                0 => 0,
                1 => u64::MAX,
                _ => seed,
            };
            values.extend(std::iter::repeat_n(value, 1 + (seed >> 8) as usize % 17));
        }
        check_token(&values);
    }
}

fn legacy_snapshot(report: &RunReport) -> String {
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
    format!(
        "{{\"status\":{status:?},\"registers\":{:?},\"memory_base\":{},\"memory\":{:?},\"instruction\":{pc},\"trace\":{:?}}}",
        report.state.registers, report.state.memory_base, report.state.memory, report.state.trace
    )
}

fn restore(text: &str, expected: &RunReport, actual: &RunReport) -> String {
    let mut restored = text.to_string();
    for report in [expected, actual] {
        restored = restored.replace(
            &format!(
                "\"registers\":{}",
                registers::Token(&report.state.registers)
            ),
            &format!("\"registers\":{:?}", report.state.registers),
        );
    }
    restored
}

#[test]
fn both_pair_formats_restore_exact_legacy_bytes_and_count_debug_spaces() {
    let input = [0, 10, u64::MAX];
    for status in [
        RunStatus::Returned(u64::MAX),
        RunStatus::Suspended,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: u64::MAX,
            width: Width::U64,
        }),
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Write,
            address: 4224,
            width: Width::U8,
        }),
    ] {
        let mut expected = report(vec![0; 100]);
        expected.status = status;
        let mut actual = report((0..100).collect());
        actual.state.instruction = None;
        let record = pair(9, 100, u64::MAX, &input, &expected, &actual).unwrap();
        let legacy = format!(
            "{{\"case\":9,\"budget\":100,\"fresh\":{},\"input\":{input:?},\"expected\":{},\"actual\":{}}}\n",
            u64::MAX,
            legacy_snapshot(&expected),
            legacy_snapshot(&actual)
        );
        assert_eq!(record.decoded_bytes, legacy.len());
        assert_eq!(restore(&record.text, &expected, &actual), legacy);
        assert_eq!(record.text.matches("{\"rle\":[").count(), 1);
        let middle = middle_pair(9, 100, "saved_ones", &input, &expected, &actual).unwrap();
        let legacy = format!(
            "{{\"case\":9,\"budget\":100,\"variant\":\"saved_ones\",\"input\":{input:?},\"expected\":{},\"actual\":{}}}\n",
            legacy_snapshot(&expected),
            legacy_snapshot(&actual)
        );
        assert_eq!(middle.decoded_bytes, legacy.len());
        assert_eq!(restore(&middle.text, &expected, &actual), legacy);
    }
}

#[test]
fn logical_budgets_reject_compressible_rows_and_do_not_publish_partial_records() {
    let expected = report(vec![0; 1000]);
    let make = || pair(0, 0, 0, &[], &expected, &expected).unwrap();
    let record = make();
    let physical = record.text.len();
    let logical = record.decoded_bytes;
    assert!(physical < logical);
    let mut buffer = Buffer::default();
    assert!(!buffer.push_bounded(make(), physical, logical));
    assert!(buffer.as_str().is_empty());
    assert_eq!(buffer.decoded_bytes(), 0);
    assert!(buffer.push_bounded(make(), logical, logical * 2 - 1));
    let first = buffer.as_str().to_string();
    assert!(!buffer.push_bounded(make(), logical, logical * 2 - 1));
    assert_eq!(buffer.as_str(), first);
    assert_eq!(buffer.decoded_bytes(), logical);
    assert!(buffer.push_bounded(make(), logical, logical * 2));
    assert_eq!(buffer.decoded_bytes(), logical * 2);
    assert_eq!(buffer.as_str().len(), physical * 2);
}

#[test]
fn oversize_dense_rows_are_classified_before_allocating_even_if_rle_would_fit() {
    let expected = report(vec![u64::MAX; MAX_LINE_BYTES / 40]);
    let record = pair(0, 0, 0, &[], &expected, &expected).unwrap();
    assert!(record.decoded_bytes > MAX_LINE_BYTES);
    assert!(record.text.is_empty());
    let mut buffer = Buffer::default();
    assert!(!buffer.push(record));
    assert!(buffer.as_str().is_empty());
    assert_eq!(buffer.decoded_bytes(), 0);
}
