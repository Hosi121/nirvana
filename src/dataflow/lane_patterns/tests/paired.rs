use super::*;

fn masked_zero(offsets: &[u64]) -> Program {
    let source = fixture(offsets, false, false);
    let mut code = source.instructions().to_vec();
    if offsets.first() == Some(&0) {
        code[1].assignments[0].value = Expr::Register(Reg(0));
    }
    Program::new(0, source.register_count(), code).unwrap()
}

#[test]
fn masked_zero_offsets_need_no_advisory_cap_but_raw_peeled_values_still_do() {
    let source = masked_zero(&[0, 1, 2]);
    let found = discover(&source).unwrap();
    assert_eq!(found.minimum_lanes(), MIN_LANES);
    assert_eq!(found.groups()[0].offsets, [0, 1, 2]);
    let peeled = discover(&fixture(&[0, 1, 2, 3], false, true)).unwrap();
    assert_eq!(peeled.groups()[0].offsets, [1, 2, 3]);
}

#[test]
fn explicit_pair_profile_preserves_source_binding_and_ordinary_discovery() {
    let source = masked_zero(&[0, 1]);
    let ordinary = discover(&source).unwrap();
    assert!(ordinary.groups().is_empty());
    let paired = ordinary.with_pair_groups().unwrap();
    assert_eq!(paired.minimum_lanes(), MIN_PAIR_LANES);
    assert!(paired.belongs_to(&source));
    assert_eq!(paired.kernels(), ordinary.kernels());
    assert_eq!(paired.groups()[0].offsets, [0, 1]);
    assert!(ordinary.groups().is_empty());
    let hinted = paired.with_advisory_entry_caps(0, &[]).unwrap();
    assert_eq!(hinted.minimum_lanes(), MIN_PAIR_LANES);
    assert_eq!(hinted.groups(), paired.groups());
    assert!(!paired.belongs_to(&masked_zero(&[0, 2])));
    for offsets in [&[0][..], &[1, 1][..]] {
        assert!(
            discover(&masked_zero(offsets))
                .unwrap()
                .with_pair_groups()
                .unwrap()
                .groups()
                .is_empty()
        );
    }
    let mut code = source.instructions().to_vec();
    let Expr::Load { width, .. } = &mut code[3].assignments[1].value else {
        panic!()
    };
    *width = Width::U32;
    let different = Program::new(0, source.register_count(), code).unwrap();
    assert!(
        discover(&different)
            .unwrap()
            .with_pair_groups()
            .unwrap()
            .groups()
            .is_empty()
    );
}

#[test]
fn masked_pair_templates_match_sequential_aliasing_kernels_for_full_word_inputs() {
    let source = masked_zero(&[0, 1]);
    let found = discover(&source).unwrap().with_pair_groups().unwrap();
    let group = &found.groups()[0];
    for seed in [0, 1, 2, 3, 4, 1 << 31, 1 << 63, u64::MAX] {
        let mut registers = vec![seed, 4224, seed.wrapping_mul(29), 0, 0, 0];
        let mut memory: Vec<_> = (0..512).map(|n| (n * 29 + 7) as u8).collect();
        registers = source
            .run_block_with_memory(0, &registers, 4096, &memory)
            .unwrap()
            .state
            .registers;
        for (kernel, &offset) in group.kernels.iter().zip(&group.offsets) {
            let address = evaluate(
                &group.load_address,
                found.ssa(),
                &registers,
                registers[2],
                0,
                offset,
            );
            let location = (address - 4096) as usize;
            let loaded = u64::from_le_bytes(memory[location..location + 8].try_into().unwrap());
            let predicted = evaluate(
                &group.update_expression,
                found.ssa(),
                &registers,
                registers[2],
                loaded,
                offset,
            );
            let report = source
                .run_block_with_memory(kernel.load.instruction, &registers, 4096, &memory)
                .unwrap();
            assert_eq!(
                report.state.registers[2], predicted,
                "seed={seed} offset={offset}"
            );
            registers = report.state.registers;
            memory = report.state.memory;
        }
    }
}
