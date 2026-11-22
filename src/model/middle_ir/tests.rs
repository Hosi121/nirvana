use super::*;
use crate::model::ir::{Control, Expr, IrInstruction};

fn source(value: Expr) -> Program {
    Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(value),
        }],
    )
    .unwrap()
}
fn loads() -> Function {
    Function::from_low(&source(Expr::binary(
        BinaryOp::Add,
        Expr::load(Expr::Const(4096), Width::U64),
        Expr::load(Expr::Const(4104), Width::U64),
    )))
    .unwrap()
}
fn result(function: &mut Function) -> &mut Region {
    let Terminator::Return(region) = &mut function.blocks[0].terminator else {
        unreachable!()
    };
    region
}
#[test]
fn lower_rejects_dropped_duplicated_and_reordered_loads() {
    for change in 0..3 {
        let mut function = loads();
        let region = result(&mut function);
        let a = region.bindings[1].id;
        match change {
            0 => region.result = a,
            1 => region.bindings[4].operation = Operation::Pure(Pure::Binary(BinaryOp::Add, a, a)),
            _ => {
                region.bindings.swap(0, 2);
                region.bindings.swap(1, 3);
            }
        }
        assert_eq!(
            function.lower().unwrap_err(),
            Error::Invalid("dropped, duplicated or reordered memory effect")
        );
    }
}
#[test]
fn lower_rejects_forward_duplicate_out_of_range_and_cross_region_values() {
    for change in 0..3 {
        let mut function = loads();
        let region = result(&mut function);
        match change {
            0 => {
                region.bindings[0].operation =
                    Operation::Pure(Pure::Unary(UnaryOp::SignExtend(Width::U64), region.result))
            }
            1 => region.bindings[2].id = region.bindings[0].id,
            _ => region.bindings[0].id = ValueId(usize::MAX),
        }
        assert!(function.lower().is_err());
    }
    let mut function = Function::from_low(&source(Expr::select(
        Expr::Register(Reg(0)),
        Expr::Const(1),
        Expr::Const(2),
    )))
    .unwrap();
    let region = result(&mut function);
    let Operation::Select { taken, .. } = &region.bindings.last().unwrap().operation else {
        unreachable!()
    };
    region.result = taken.result;
    assert_eq!(
        function.lower().unwrap_err(),
        Error::Invalid("value scope or forward reference")
    );
}
#[test]
fn unused_and_live_reads_must_have_the_right_source_ssa_version() {
    let mut function = Function::from_low(&source(Expr::Register(Reg(0)))).unwrap();
    result(&mut function).bindings[0].operation = Operation::ReadStorage {
        storage: StorageId(0),
        version: None,
    };
    assert_eq!(
        function.lower().unwrap_err(),
        Error::Invalid("storage read version")
    );
    let mut function = loads();
    let id = ValueId(function.value_count);
    function.value_count += 1;
    let region = result(&mut function);
    region.bindings.push(Binding {
        id,
        origin: region.origin,
        operation: Operation::ReadStorage {
            storage: StorageId(0),
            version: Some(ssa::ValueId(usize::MAX)),
        },
    });
    assert_eq!(
        function.lower().unwrap_err(),
        Error::Invalid("storage read version")
    );
}
#[test]
fn source_origins_and_exact_source_binding_are_checked() {
    let mut function = loads();
    result(&mut function).bindings[0].origin.operand = Operand::Address;
    assert!(function.lower().is_err());
    let original = source(Expr::Const(7));
    let mut function = Function::from_low(&original).unwrap();
    result(&mut function).bindings[0].operation = Operation::Pure(Pure::Constant(8));
    assert!(function.validate_source(&original).is_err());
}
#[test]
fn pure_dag_sharing_can_lower_without_changing_effects() {
    let original = source(Expr::binary(BinaryOp::Add, Expr::Const(7), Expr::Const(7)));
    let mut function = Function::from_low(&original).unwrap();
    let region = result(&mut function);
    let a = region.bindings[0].id;
    region.bindings[2].operation = Operation::Pure(Pure::Binary(BinaryOp::Add, a, a));
    function.validate_source(&original).unwrap();
    assert_eq!(
        function.run_with_memory(&[0; 2], 0, &[], 1).unwrap().status,
        ir::RunStatus::Returned(14)
    );
}
#[test]
fn original_depth_limits_are_checked_before_recursive_lifting() {
    let mut expr = Expr::Const(0);
    for _ in 0..ssa::MAX_DEPTH {
        expr = Expr::unary(UnaryOp::SignExtend(Width::U64), expr);
    }
    assert!(Function::from_low(&source(expr)).is_err());
}
