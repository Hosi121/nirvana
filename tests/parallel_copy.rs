use nirvana::parallel_copy::{
    Copy, MAX_LOCALS, MAX_PARALLEL_COPIES, MAX_SEQUENTIAL_COPIES, schedule, validate,
};

fn copy(destination: usize, source: usize) -> Copy {
    Copy {
        destination,
        source,
    }
}

// Concrete simultaneous oracle, independent of the symbolic checker. The
// original values are deliberately distinct, unlike a zero-filled bank.
fn assert_concrete(local_count: usize, parallel: &[Copy], sequential: &[Copy]) {
    let input: Vec<_> = (0..local_count).map(|index| 91 + 17 * index).collect();
    let mut expected = input.clone();
    for step in parallel {
        expected[step.destination] = input[step.source];
    }
    let mut actual: Vec<_> = input.into_iter().map(Some).collect();
    actual.push(None);
    for step in sequential {
        actual[step.destination] = Some(actual[step.source].expect("initialized source"));
    }
    assert_eq!(
        actual[..local_count],
        expected.into_iter().map(Some).collect::<Vec<_>>()
    );
}

fn checked(local_count: usize, parallel: &[Copy]) {
    let result = schedule(local_count, parallel).unwrap();
    validate(local_count, parallel, &result.copies).unwrap();
    assert_concrete(local_count, parallel, &result.copies);
    assert!(
        result
            .copies
            .iter()
            .all(|step| step.destination != step.source)
    );
    assert_eq!(
        result.uses_temporary,
        result
            .copies
            .iter()
            .any(|step| step.destination == local_count)
    );
    let mut reversed = parallel.to_vec();
    reversed.reverse();
    assert_eq!(result, schedule(local_count, &reversed).unwrap());
}

#[test]
fn exhaustive_partial_maps_include_self_copies_cycles_and_fanout() {
    for local_count in 0usize..=5 {
        // Each destination is either absent or reads any original input.
        for mut encoding in 0..(local_count + 1).pow(local_count as u32) {
            let mut parallel = Vec::new();
            for destination in 0..local_count {
                let choice = encoding % (local_count + 1);
                encoding /= local_count + 1;
                if choice != local_count {
                    parallel.push(copy(destination, choice));
                }
            }
            checked(local_count, &parallel);
        }
    }
}

#[test]
fn exhaustive_permutations_through_seven_locals() {
    fn visit(values: &mut [usize], index: usize) {
        if index == values.len() {
            let parallel: Vec<_> = values
                .iter()
                .enumerate()
                .map(|(d, &s)| copy(d, s))
                .collect();
            checked(values.len(), &parallel);
            return;
        }
        for next in index..values.len() {
            values.swap(index, next);
            visit(values, index + 1);
            values.swap(index, next);
        }
    }
    for count in 0..=7 {
        visit(&mut (0..count).collect::<Vec<_>>(), 0);
    }
}

#[test]
fn scratch_is_reused_for_disjoint_cycles() {
    let parallel = [
        copy(0, 1),
        copy(1, 0),
        copy(2, 3),
        copy(3, 4),
        copy(4, 2),
        copy(5, 0),
    ];
    let result = schedule(7, &parallel).unwrap();
    assert_eq!(
        result.copies,
        [
            copy(5, 0),
            copy(7, 0),
            copy(0, 1),
            copy(1, 7),
            copy(7, 2),
            copy(2, 3),
            copy(3, 4),
            copy(4, 7)
        ]
    );
    checked(7, &parallel);
}

#[test]
fn malformed_parallel_inputs_are_rejected_by_both_apis() {
    for (count, parallel) in [
        (1, vec![copy(0, 0), copy(0, 0)]),
        (2, vec![copy(0, 0), copy(0, 1)]),
        (2, vec![copy(0, 1), copy(0, 0)]),
        (0, vec![copy(0, 0)]),
        (2, vec![copy(2, 0)]),
        (2, vec![copy(0, 2)]),
        (2, vec![copy(usize::MAX, 0)]),
        (2, vec![copy(0, usize::MAX)]),
    ] {
        assert!(schedule(count, &parallel).is_err(), "{parallel:?}");
        assert!(validate(count, &parallel, &[]).is_err(), "{parallel:?}");
    }
}

#[test]
fn symbolic_validation_catches_corruption_hidden_by_equal_inputs() {
    let parallel = [copy(0, 1), copy(1, 0)];
    // Both corrupt sequences pass a check with inputs [7, 7, 7].
    assert!(validate(3, &parallel, &[copy(0, 1), copy(1, 0)]).is_err());
    assert!(validate(3, &parallel, &[]).is_err());
    let mut corrupted = schedule(3, &parallel).unwrap().copies;
    corrupted.push(copy(2, 0));
    assert!(validate(3, &parallel, &corrupted).is_err());
    // A wrong requested destination and a clobbered self destination also fail.
    assert!(validate(3, &[copy(0, 1)], &[copy(0, 2)]).is_err());
    assert!(validate(3, &[copy(0, 0)], &[copy(0, 1)]).is_err());
    assert!(validate(3, &[], &[copy(2, 0)]).is_err());
}

#[test]
fn exhaustive_candidate_sequences_match_independent_dense_execution() {
    // Nine partial parallel maps, checked against all 7,381 sequences of
    // length 0..=4 over two originals and scratch. Unlike the production
    // checker, this oracle materializes the entire concrete storage bank.
    for mut parallel_encoding in 0..9 {
        let mut parallel = Vec::new();
        let mut expected = [41, 93];
        for destination in 0..2 {
            let source = parallel_encoding % 3;
            parallel_encoding /= 3;
            if source < 2 {
                parallel.push(copy(destination, source));
                expected[destination] = [41, 93][source];
            }
        }
        for length in 0..=4 {
            for mut encoding in 0..9usize.pow(length) {
                let mut sequential = Vec::new();
                for _ in 0..length {
                    let operation = encoding % 9;
                    encoding /= 9;
                    sequential.push(copy(operation / 3, operation % 3));
                }
                let mut bank = [Some(41), Some(93), None];
                let mut initialized = true;
                for step in &sequential {
                    if bank[step.source].is_none() {
                        initialized = false;
                        break;
                    }
                    bank[step.destination] = bank[step.source];
                }
                let valid = initialized && bank[..2] == expected.map(Some);
                assert_eq!(
                    validate(2, &parallel, &sequential).is_ok(),
                    valid,
                    "parallel={parallel:?}, sequential={sequential:?}"
                );
            }
        }
    }
}

#[test]
fn validator_accepts_restoration_and_alternative_schedules() {
    validate(3, &[], &[copy(3, 0), copy(0, 1), copy(0, 3)]).unwrap();
    validate(3, &[copy(0, 1)], &[copy(0, 0), copy(0, 1), copy(3, 2)]).unwrap();
    validate(
        2,
        &[copy(0, 1), copy(1, 0)],
        &[copy(2, 1), copy(1, 0), copy(0, 2)],
    )
    .unwrap();
    validate(0, &[], &[]).unwrap();
}

#[test]
fn scratch_reads_require_initialization_even_for_self_copies() {
    for sequential in [
        vec![copy(0, 2)],
        vec![copy(2, 2)],
        vec![copy(2, 2), copy(0, 1)],
    ] {
        assert!(
            validate(2, &[], &sequential)
                .unwrap_err()
                .contains("uninitialized")
        );
    }
    assert!(validate(0, &[], &[copy(0, 0)]).is_err());
    validate(2, &[], &[copy(2, 0), copy(2, 2)]).unwrap();
}

#[test]
fn sequential_indices_allow_exactly_one_scratch() {
    for sequential in [
        vec![copy(3, 0)],
        vec![copy(0, 3)],
        vec![copy(usize::MAX, 0)],
        vec![copy(0, usize::MAX)],
    ] {
        assert!(validate(2, &[], &sequential).is_err());
    }
}

#[test]
fn budgets_reject_before_processing_or_cloning_input() {
    for count in [MAX_LOCALS + 1, usize::MAX] {
        assert!(schedule(count, &[]).unwrap_err().contains("limit"));
        assert!(validate(count, &[], &[]).unwrap_err().contains("limit"));
    }
    let parallel = vec![copy(usize::MAX, usize::MAX); MAX_PARALLEL_COPIES + 1];
    assert!(schedule(1, &parallel).unwrap_err().contains("count limit"));
    assert!(
        validate(1, &parallel, &[])
            .unwrap_err()
            .contains("count limit")
    );
    let sequential = vec![copy(usize::MAX, usize::MAX); MAX_SEQUENTIAL_COPIES + 1];
    assert!(
        validate(1, &[], &sequential)
            .unwrap_err()
            .contains("count limit")
    );
    let accepted = vec![copy(0, 0); MAX_SEQUENTIAL_COPIES];
    validate(1, &[], &accepted).unwrap();
}

#[test]
fn maximum_cycle_and_maximum_scratch_reuse_stay_within_bounds() {
    let count = MAX_LOCALS.min(MAX_PARALLEL_COPIES);
    let cycle: Vec<_> = (0..count)
        .map(|destination| copy(destination, (destination + 1) % count))
        .collect();
    let result = schedule(count, &cycle).unwrap();
    assert_eq!(result.copies.len(), count + 1);
    validate(count, &cycle, &result.copies).unwrap();

    let pairs: Vec<_> = (0..count)
        .map(|destination| copy(destination, destination ^ 1))
        .collect();
    let result = schedule(count, &pairs).unwrap();
    assert_eq!(result.copies.len(), count + count / 2);
    assert!(result.copies.len() <= MAX_SEQUENTIAL_COPIES);
    validate(count, &pairs, &result.copies).unwrap();
}

#[test]
fn sparse_maps_preserve_unreferenced_large_index_ranges() {
    let parallel = [copy(MAX_LOCALS - 1, 12), copy(12, MAX_LOCALS - 1)];
    checked(MAX_LOCALS, &parallel);
    assert!(validate(MAX_LOCALS, &parallel, &[copy(11, 10)]).is_err());
}
