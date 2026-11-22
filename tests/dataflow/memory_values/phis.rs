use super::*;

#[test]
fn equal_saved_slices_cross_register_phis_nested_copies_and_loop_backedges() {
    use nirvana::ir::UnaryOp;
    let mut checked = 0;
    for source in crate::support::byte_values::register_phi_programs() {
        let plan = MemoryValuePlan::analyze(&source).expect("equal incoming saved-word slices");
        assert_eq!(plan.evidence().snapshot_values, 1);
        let candidate = plan.lower(&source).unwrap();
        let returned = source
            .instructions()
            .iter()
            .position(|i| matches!(i.control, Control::Return(_)))
            .unwrap();
        assert!(matches!(
            &candidate.instructions()[returned].control,
            Control::Return(Expr::Unary(UnaryOp::Extract { start: 8, width: Width::U16 }, value))
                if matches!(&**value, Expr::Register(r) if r.0 >= source.register_count())
        ));
        checked += compare(&source, &candidate);
    }
    println!("{checked} register-phi saved-slice full-state/fault/budget observations");
}

#[test]
fn differing_unknown_and_initial_phi_inputs_keep_the_merged_value() {
    let source = crate::support::byte_values::register_phi_programs().remove(0);
    for replacement in [
        vec![set(
            2,
            Expr::load(b(nirvana::ir::BinaryOp::Add, r(7), c(34)), Width::U16),
        )],
        vec![set(
            2,
            Expr::load(b(nirvana::ir::BinaryOp::Add, r(7), c(48)), Width::U16),
        )],
        vec![],
    ] {
        let mut rows = source.instructions().to_vec();
        rows[2].assignments = replacement;
        let different = Program::new(0, 8, rows).unwrap();
        if let Some(plan) = MemoryValuePlan::analyze(&different) {
            let candidate = plan.lower(&different).unwrap();
            assert_eq!(
                candidate.instructions()[3].control,
                different.instructions()[3].control
            );
            compare(&different, &candidate);
        }
        // A source-bound proof for the equal join must fail after either arm changes.
        let old = MemoryValuePlan::analyze(&source).unwrap();
        assert!(old.lower(&different).is_none());
    }
    let source = crate::support::byte_values::register_phi_programs().remove(2);
    let mut rows = source.instructions().to_vec();
    rows[3].assignments[1] = set(2, b(nirvana::ir::BinaryOp::Add, r(2), c(1)));
    let changing = Program::new(0, 8, rows).unwrap();
    if let Some(plan) = MemoryValuePlan::analyze(&changing) {
        let candidate = plan.lower(&changing).unwrap();
        assert_eq!(
            candidate.instructions()[2].control,
            changing.instructions()[2].control
        );
        compare(&changing, &candidate);
    }
}
