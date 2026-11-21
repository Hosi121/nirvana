//! Original C is an independent oracle for the handwritten IR and emitted C.
//! Future decoder cases are compiled and checked even without an IR model.

use crate::support::programs;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use nirvana::emit::emit_c;

use crate::support::native;
use native::{Scratch, fixture_root, link, object, run};

struct Fixture<'a> {
    id: &'a str,
    ir: Option<&'a str>,
}
struct Input<'a> {
    id: &'a str,
    state: [u64; 4],
}

fn rows(text: &str) -> impl Iterator<Item = Vec<&str>> {
    text.lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| line.split('\t').collect())
}

fn fixtures() -> Vec<Fixture<'static>> {
    rows(include_str!("../fixtures/cases.tsv"))
        .map(|row| {
            assert_eq!(row.len(), 3);
            assert!(!row[2].is_empty());
            assert!(
                row[0]
                    .bytes()
                    .all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit() || ch == b'-')
            );
            Fixture {
                id: row[0],
                ir: (row[1] != "-").then_some(row[1]),
            }
        })
        .collect()
}

fn inputs() -> Vec<Input<'static>> {
    rows(include_str!("../fixtures/inputs.tsv"))
        .map(|row| {
            assert_eq!(row.len(), 5);
            Input {
                id: row[0],
                state: std::array::from_fn(|i| row[i + 1].parse().unwrap()),
            }
        })
        .collect()
}

fn goldens() -> BTreeMap<(&'static str, &'static str), Vec<u64>> {
    let mut expected = BTreeMap::new();
    for row in rows(include_str!("../fixtures/golden.tsv")) {
        assert_eq!(row.len(), 7);
        let values = row[2..].iter().map(|word| word.parse().unwrap()).collect();
        assert!(expected.insert((row[0], row[1]), values).is_none());
    }
    expected
}

#[test]
fn fixture_catalog_covers_sources_ir_models_inputs_and_hand_checked_results() {
    let fixtures = fixtures();
    let case_ids: BTreeSet<_> = fixtures.iter().map(|fixture| fixture.id).collect();
    assert_eq!(case_ids.len(), fixtures.len(), "duplicate fixture id");
    let sources: BTreeSet<_> = std::fs::read_dir(fixture_root().join("cases"))
        .unwrap()
        .map(|entry| {
            let path = entry.unwrap().path();
            assert_eq!(path.extension().and_then(|value| value.to_str()), Some("c"));
            path.file_stem().unwrap().to_str().unwrap().to_owned()
        })
        .collect();
    assert_eq!(
        sources,
        case_ids.iter().map(|id| (*id).to_owned()).collect()
    );
    let ir_ids: BTreeSet<_> = fixtures.iter().filter_map(|fixture| fixture.ir).collect();
    assert_eq!(ir_ids, programs::NAMES.iter().copied().collect());
    assert_eq!(
        fixtures
            .iter()
            .filter(|fixture| fixture.ir.is_some())
            .count(),
        ir_ids.len()
    );
    let inputs = inputs();
    let input_ids: BTreeSet<_> = inputs.iter().map(|input| input.id).collect();
    assert_eq!(input_ids.len(), inputs.len());
    let goldens = goldens();
    assert_eq!(
        goldens
            .keys()
            .map(|&(case, _)| case)
            .collect::<BTreeSet<_>>(),
        case_ids
    );
    for (case, input) in goldens.keys() {
        assert!(case_ids.contains(case));
        assert!(input_ids.contains(input));
    }
    assert_eq!(fixtures.len(), 20);
    assert_eq!(inputs.len(), 63);
    assert_eq!(goldens.len(), 27);
}

#[test]
fn original_c_ir_and_generated_c_agree_at_o0_and_o2() {
    let scratch = Scratch::new();
    let root = fixture_root();
    let fixtures = fixtures();
    let inputs = inputs();
    let goldens = goldens();
    let mut input_text = String::new();
    for input in &inputs {
        writeln!(
            input_text,
            "{} {} {} {}",
            input.state[0], input.state[1], input.state[2], input.state[3]
        )
        .unwrap();
    }
    let mut source_comparisons = 0;
    let mut generated_comparisons = 0;
    let mut reference = BTreeMap::new();
    for optimization in ["-O0", "-O2"] {
        let directory = scratch.0.join(optimization);
        std::fs::create_dir(&directory).unwrap();
        let harness = directory.join("harness.o");
        let generated_harness = directory.join("generated-harness.o");
        let helpers = directory.join("helpers.o");
        object(&root.join("harness.c"), &harness, optimization, "fixture");
        object(
            &root.join("harness.c"),
            &generated_harness,
            optimization,
            "nirvana_fn",
        );
        object(&root.join("helpers.c"), &helpers, optimization, "fixture");
        for fixture in &fixtures {
            let source_object = directory.join(format!("{}-source.o", fixture.id));
            let source_binary = directory.join(format!("{}-source", fixture.id));
            object(
                &root.join("cases").join(format!("{}.c", fixture.id)),
                &source_object,
                optimization,
                "fixture",
            );
            link(&[&source_object, &harness, &helpers], &source_binary);
            let actual = run(&source_binary, &input_text);
            assert_eq!(actual.len(), inputs.len());
            if fixture.id == "diamond" && optimization == "-O0" {
                let expected: Vec<_> = actual
                    .iter()
                    .cycle()
                    .take(actual.len() * 4)
                    .cloned()
                    .collect();
                assert_eq!(
                    run(&source_binary, &input_text.repeat(4)),
                    expected,
                    "fixture I/O must keep draining streams larger than a pipe buffer"
                );
            }
            if optimization == "-O0" {
                reference.insert(fixture.id, actual.clone());
            } else {
                assert_eq!(
                    actual, reference[fixture.id],
                    "{} differs across optimization levels",
                    fixture.id
                );
            }
            for (input, outcome) in inputs.iter().zip(&actual) {
                if let Some(expected) = goldens.get(&(fixture.id, input.id)) {
                    assert_eq!(
                        outcome, expected,
                        "{} {optimization}, golden input {}",
                        fixture.id, input.id
                    );
                }
                source_comparisons += 1;
            }
            if let Some(ir_id) = fixture.ir {
                let program = programs::named(ir_id).unwrap();
                for (input, outcome) in inputs.iter().zip(&actual) {
                    let expected = program.execute(&input.state, 1000).unwrap();
                    let mut expected_values = vec![expected.value];
                    expected_values.extend(expected.registers);
                    assert_eq!(
                        outcome, &expected_values,
                        "{} {optimization}, IR input {}",
                        fixture.id, input.id
                    );
                }
                let generated_source = directory.join(format!("{}-generated.c", fixture.id));
                std::fs::write(&generated_source, emit_c(&program).unwrap().code).unwrap();
                let generated_object = directory.join(format!("{}-generated.o", fixture.id));
                object(
                    &generated_source,
                    &generated_object,
                    optimization,
                    "nirvana_fn",
                );
                let generated_binary = directory.join(format!("{}-generated", fixture.id));
                link(&[&generated_object, &generated_harness], &generated_binary);
                let generated = run(&generated_binary, &input_text);
                assert_eq!(
                    generated, actual,
                    "{} {optimization}: generated C differs from original C",
                    fixture.id
                );
                generated_comparisons += generated.len();
            }
        }
    }
    assert_eq!(source_comparisons, 2520);
    assert_eq!(generated_comparisons, 1764);
}
