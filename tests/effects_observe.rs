use nirvana::effects::{Report, Status, Suspend};
use nirvana::effects_observe::{Comparison, Contract, Difference};
use nirvana::ir::{AccessKind, MemoryFault, Snapshot, Width};
fn report() -> Report {
    Report {
        status: Status::Returned(7),
        state: Snapshot {
            registers: vec![7, 8],
            memory_base: 4096,
            memory: vec![1, 2],
            trace: vec![0, 1],
            instruction: Some(1),
        },
        output: b"hello\n".to_vec(),
        consumed: 1,
    }
}
#[test]
fn stdout_and_consumed_calls_are_part_of_the_completed_observation() {
    let left = report();
    let mut right = left.clone();
    let contract = Contract::return_memory_output();
    assert_eq!(contract.compare(&left, &right), Comparison::MatchForInput);
    right.output[0] = b'H';
    assert!(matches!(
        contract.compare(&left, &right),
        Comparison::Counterexample(Difference::OutputByte { index: 0, .. })
    ));
    right = left.clone();
    right.consumed = 0;
    assert!(matches!(
        contract.compare(&left, &right),
        Comparison::Counterexample(Difference::Consumed { .. })
    ));
}
#[test]
fn full_state_profile_also_compares_registers_and_trace() {
    let left = report();
    let mut right = left.clone();
    right.state.registers[1] = 9;
    assert_eq!(
        Contract::return_memory_output().compare(&left, &right),
        Comparison::MatchForInput
    );
    assert!(matches!(
        Contract::full_ir_state().compare(&left, &right),
        Comparison::Counterexample(Difference::Core(_))
    ));
    right = left.clone();
    right.state.trace.reverse();
    assert!(matches!(
        Contract::full_ir_state().compare(&left, &right),
        Comparison::Counterexample(Difference::Core(_))
    ));
}
#[test]
fn incomplete_environment_or_budgets_never_establish_completed_equivalence() {
    for status in [
        Status::EnvironmentExhausted,
        Status::InvalidOutcome,
        Status::UnknownTarget(99),
        Status::Suspended(Suspend::Reads),
        Status::Suspended(Suspend::Instructions),
    ] {
        let mut left = report();
        left.status = status;
        assert!(matches!(
            Contract::return_memory_output().compare(&left, &left),
            Comparison::Inconclusive { .. }
        ));
        assert!(matches!(
            Contract::return_memory_output().compare(&left, &report()),
            Comparison::Inconclusive { .. }
        ));
    }
}
#[test]
fn fault_observations_keep_prior_ram_and_output() {
    let mut left = report();
    left.status = Status::Fault(MemoryFault {
        access: AccessKind::Read,
        address: 999,
        width: Width::U8,
    });
    let mut right = left.clone();
    right.output.clear();
    assert!(matches!(
        Contract::return_memory_output().compare(&left, &right),
        Comparison::Counterexample(Difference::OutputByte { .. })
    ));
    right = left.clone();
    right.state.memory[0] = 3;
    assert!(matches!(
        Contract::return_memory_output().compare(&left, &right),
        Comparison::Counterexample(Difference::Core(_))
    ));
}
