//! Native full-register C observes the complete partial guest state on faults.
//! The event oracle is independent of both C rendering and sequence::sequence.
use crate::support::checked_c;
use crate::support::native;

use nirvana::emit::emit_c;
use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, MemoryFault, Place, Program,
    Reg, RunStatus, Width,
};
use nirvana::sequence::{MAX_EXPRESSION_DEPTH, SequenceError};
use std::fmt::Write as _;

const REGISTERS: usize = 8;
const BYTES: usize = 64;
const EVENTS: usize = 64;

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn load(address: Expr) -> Expr {
    Expr::load(address, Width::U64)
}
fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn returning(assignments: Vec<Assignment>, value: Expr) -> Program {
    Program::new(
        0,
        REGISTERS,
        vec![ins(0, assignments, Control::Return(value))],
    )
    .unwrap()
}

#[derive(Clone)]
struct Input {
    base: u64,
    registers: [u64; REGISTERS],
    memory: [u8; BYTES],
}
impl Input {
    fn new(a: u64, b: u64) -> Self {
        let mut memory = std::array::from_fn(|i| (i as u8).wrapping_mul(29).wrapping_add(7));
        for (word, value) in [0x1020_u64, 0x1030, 0, 0x1234].into_iter().enumerate() {
            memory[word * 8..word * 8 + 8].copy_from_slice(&value.to_le_bytes());
        }
        Self {
            base: 0x1000,
            registers: [a, b, 0xfeed, 0xabcd, u64::MAX, 65, 63, 0xbad],
            memory,
        }
    }
}

struct Oracle {
    registers: Vec<u64>,
    base: u64,
    memory: Vec<u8>,
    events: Vec<(u64, u64, u64)>,
}
impl Oracle {
    fn offset(&self, address: u64, width: Width, access: AccessKind) -> Result<usize, MemoryFault> {
        let fault = MemoryFault {
            address,
            width,
            access,
        };
        address.checked_add(width.bytes() as u64 - 1).ok_or(fault)?;
        let offset = address
            .checked_sub(self.base)
            .and_then(|o| usize::try_from(o).ok())
            .ok_or(fault)?;
        if offset
            .checked_add(width.bytes())
            .is_none_or(|end| end > self.memory.len())
        {
            return Err(fault);
        }
        Ok(offset)
    }
    fn expr(&mut self, expr: &Expr) -> Result<u64, MemoryFault> {
        Ok(match expr {
            Expr::Const(value) => *value,
            Expr::Unary(op, value) => crate::support::ir::unary_value(*op, self.expr(value)?),
            Expr::Register(reg) => self.registers[reg.0],
            Expr::Load { address, width } => {
                let address = self.expr(address)?;
                self.events.push((1, address, width.bytes() as u64));
                let offset = self.offset(address, *width, AccessKind::Read)?;
                let mut bytes = [0; 8];
                bytes[..width.bytes()]
                    .copy_from_slice(&self.memory[offset..offset + width.bytes()]);
                u64::from_le_bytes(bytes)
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                if self.expr(condition)? != 0 {
                    self.expr(taken)?
                } else {
                    self.expr(not_taken)?
                }
            }
            Expr::Binary(op, left, right) => {
                let a = self.expr(left)?;
                let z = self.expr(right)?;
                match op {
                    BinaryOp::Add => a.wrapping_add(z),
                    BinaryOp::Sub => a.wrapping_sub(z),
                    BinaryOp::Mul => a.wrapping_mul(z),
                    BinaryOp::UMulHigh => ((a as u128 * z as u128) >> 64) as u64,
                    BinaryOp::SMulHigh => {
                        ((i128::from(a as i64) * i128::from(z as i64)) >> 64) as u64
                    }
                    BinaryOp::AShr => ((a as i64) >> (z & 63)) as u64,
                    BinaryOp::And => a & z,
                    BinaryOp::Or => a | z,
                    BinaryOp::Xor => a ^ z,
                    BinaryOp::Shl => a.wrapping_shl((z & 63) as u32),
                    BinaryOp::Shr => a.wrapping_shr((z & 63) as u32),
                    BinaryOp::Eq => (a == z) as u64,
                    BinaryOp::Ne => (a != z) as u64,
                    BinaryOp::Ult => (a < z) as u64,
                    BinaryOp::Ule => (a <= z) as u64,
                }
            }
        })
    }
    fn run(&mut self, program: &Program) -> Result<u64, MemoryFault> {
        let mut pc = program.cfg().block(program.cfg().entry()).start;
        for _ in 0..256 {
            let instruction = program
                .instructions()
                .iter()
                .find(|i| i.address == pc)
                .unwrap();
            for assignment in &instruction.assignments {
                match &assignment.destination {
                    Place::Register(reg) => self.registers[reg.0] = self.expr(&assignment.value)?,
                    Place::Memory { address, width } => {
                        let address = self.expr(address)?;
                        let offset = self.offset(address, *width, AccessKind::Write)?;
                        let value = self.expr(&assignment.value)?.to_le_bytes();
                        self.events.push((2, address, width.bytes() as u64));
                        self.memory[offset..offset + width.bytes()]
                            .copy_from_slice(&value[..width.bytes()]);
                    }
                }
            }
            pc = match &instruction.control {
                Control::Next => pc + 1,
                Control::Jump(target) => *target,
                Control::Branch { condition, target } => {
                    if self.expr(condition)? != 0 {
                        *target
                    } else {
                        pc + 1
                    }
                }
                Control::Return(value) => return self.expr(value),
            };
        }
        panic!("test oracle exceeded finite execution budget")
    }
}

fn expected(program: &Program, input: &Input) -> Vec<u64> {
    let run = program
        .run_with_memory(&input.registers, input.base, &input.memory, 256)
        .unwrap();
    let mut oracle = Oracle {
        registers: input.registers.to_vec(),
        base: input.base,
        memory: input.memory.to_vec(),
        events: vec![],
    };
    let status = oracle.run(program);
    assert_eq!(oracle.registers, run.state.registers);
    assert_eq!(oracle.memory, run.state.memory);
    let mut fields = match (status, run.status) {
        (Ok(a), RunStatus::Returned(z)) => {
            assert_eq!(a, z);
            vec![0, 0, 0, 0, a]
        }
        (Err(a), RunStatus::Fault(z)) => {
            assert_eq!(a, z);
            vec![
                1,
                a.address,
                if a.access == AccessKind::Read { 1 } else { 2 },
                a.width.bytes() as u64,
                0,
            ]
        }
        other => panic!("oracle disagreement {other:?}"),
    };
    fields.extend(oracle.registers);
    fields.extend(oracle.memory.into_iter().map(u64::from));
    assert!(oracle.events.len() <= EVENTS);
    fields.push(oracle.events.len() as u64);
    for event in oracle
        .events
        .iter()
        .copied()
        .chain(std::iter::repeat((0, 0, 0)))
        .take(EVENTS)
    {
        fields.extend([event.0, event.1, event.2]);
    }
    fields
}

fn native_compare(program: &Program, inputs: &[Input], name: &str) {
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/full-c-sequence")
        .join(name);
    std::fs::create_dir_all(&directory).unwrap();
    let emitted = emit_c(program).unwrap();
    let mut code = checked_c::instrument(&emitted.code);
    let load = "uint64_t offset = nirvana_test_read_offset(m, address, width), value = 0;";
    assert_eq!(code.matches(load).count(), 1);
    code = code.replace(load, &format!("oracle_event(1,address,width); {load}"));
    let store = "uint64_t offset = nirvana_offset(m, address, width);";
    assert_eq!(code.matches(store).count(), 1);
    code = code.replace(store, &format!("{store} oracle_event(2,address,width);"));
    let prefix = format!(
        "#include <stdint.h>\nstatic uint64_t events[{EVENTS}][3], event_count;\nstatic void oracle_event(uint64_t kind,uint64_t address,uint64_t width) {{ if(event_count < {EVENTS}) {{ events[event_count][0]=kind;events[event_count][1]=address;events[event_count][2]=width; }} ++event_count; }}\n"
    );
    code = prefix + &code;
    code.push_str("\n#undef abort\n#include <stdio.h>\n#include <inttypes.h>\n#include <string.h>\nstatic jmp_buf jump;\nstatic uint64_t registers[8], result;\nstatic uint8_t memory[64];\nstatic unsigned fault;\n_Noreturn void nirvana_test_abort(void) { longjmp(jump,1); }\n");
    writeln!(
        code,
        "static const uint64_t inputs[{}][{}] = {{",
        inputs.len(),
        1 + REGISTERS + BYTES
    )
    .unwrap();
    for input in inputs {
        let words = std::iter::once(input.base)
            .chain(input.registers)
            .chain(input.memory.map(u64::from));
        writeln!(
            code,
            "{{{}}},",
            words
                .map(|v| format!("UINT64_C({v})"))
                .collect::<Vec<_>>()
                .join(",")
        )
        .unwrap();
    }
    code.push_str("};\nint main(void) {\n");
    writeln!(
        code,
        "static unsigned row; for(row=0;row<{};++row) {{",
        inputs.len()
    )
    .unwrap();
    code.push_str(r#"
        for(unsigned i=0;i<8;++i) registers[i]=inputs[row][i+1];
        for(unsigned i=0;i<64;++i) memory[i]=(uint8_t)inputs[row][i+9];
        memset(events,0,sizeof(events));event_count=0;
        result=0;fault=0;nirvana_test_address=0;nirvana_test_access=0;nirvana_test_width=0;
        if(setjmp(jump)==0) result=nirvana_fn(registers,memory,inputs[row][0],sizeof(memory));
        else fault=1;
        printf("%u %" PRIu64 " %u %" PRIu64 " %" PRIu64,fault,fault?nirvana_test_address:UINT64_C(0),fault?nirvana_test_access:0,fault?nirvana_test_width:UINT64_C(0),result);
        for(unsigned i=0;i<8;++i) printf(" %" PRIu64,registers[i]);
        for(unsigned i=0;i<64;++i) printf(" %u",(unsigned)memory[i]);
        printf(" %" PRIu64,event_count);
"#);
    writeln!(code,"for(unsigned i=0;i<{EVENTS};++i) for(unsigned j=0;j<3;++j) printf(\" %\" PRIu64,events[i][j]);").unwrap();
    code.push_str("putchar('\\n');\n}\nreturn 0;\n}\n");
    let source = directory.join("generated.c");
    std::fs::write(&source, code).unwrap();
    let rows: Vec<_> = inputs
        .iter()
        .map(|input| expected(program, input))
        .collect();
    std::fs::write(
        directory.join("expected.txt"),
        rows.iter()
            .map(|row| row.iter().map(u64::to_string).collect::<Vec<_>>().join(" "))
            .collect::<Vec<_>>()
            .join("\n")
            + "\n",
    )
    .unwrap();
    for optimization in ["-O0", "-O2"] {
        let binary = directory.join(format!("run{optimization}"));
        native::object(
            &source,
            &directory.join(format!("run{optimization}.o")),
            optimization,
            "unused",
        );
        native::link(&[&directory.join(format!("run{optimization}.o"))], &binary);
        let actual = native::run_fields(&binary, "", rows[0].len());
        assert_eq!(actual.len(), rows.len());
        for (row, (actual, expected)) in actual.iter().zip(&rows).enumerate() {
            assert_eq!(
                actual,
                expected,
                "{name} {optimization} row {row}; source {}",
                source.display()
            );
        }
    }
}

fn grid() -> Vec<Input> {
    [0x1000, 0x1008, 0x1038, 0x103f, 12345, u64::MAX]
        .into_iter()
        .flat_map(|a| {
            [0x1000, 0x1008, 0x1038, 0x103f, 23456, u64::MAX]
                .into_iter()
                .map(move |z| Input::new(a, z))
        })
        .collect()
}

#[test]
fn native_store_address_fault_precedes_rhs_and_keeps_partial_guest_state() {
    let program = returning(
        vec![
            set(2, c(17)),
            store(c(0x103f), Width::U8, c(0xaa)),
            store(load(r(0)), Width::U64, load(r(1))),
            set(3, c(99)),
        ],
        r(2),
    );
    native_compare(&program, &grid(), "store-address-rhs");
}

#[test]
fn native_store_full_width_check_precedes_rhs_and_failure_is_atomic() {
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let program = returning(
            vec![set(2, c(37)), store(r(0), width, load(r(1))), set(3, c(99))],
            load(c(0x1000)),
        );
        native_compare(&program, &grid(), &format!("store-width{}", width.bits()));
    }
}

#[test]
fn native_binary_and_umul_high_reads_are_left_to_right() {
    for op in [
        BinaryOp::Add,
        BinaryOp::UMulHigh,
        BinaryOp::SMulHigh,
        BinaryOp::AShr,
        BinaryOp::Shl,
        BinaryOp::Eq,
    ] {
        let program = returning(
            vec![
                set(2, c(71)),
                set(3, b(op, load(r(0)), load(r(1)))),
                set(2, c(19)),
            ],
            r(3),
        );
        native_compare(&program, &grid(), &format!("binary-{op:?}"));
    }
}

#[test]
fn native_nested_addresses_and_unused_values_preserve_every_read() {
    let expressions = [
        load(load(r(0))),
        b(
            BinaryOp::Mul,
            c(0),
            b(BinaryOp::Add, load(r(0)), load(r(1))),
        ),
        Expr::select(load(r(0)), c(7), c(7)),
    ];
    for (index, expr) in expressions.into_iter().enumerate() {
        native_compare(
            &returning(vec![set(3, c(45)), set(2, expr)], r(2)),
            &grid(),
            &format!("nested-{index}"),
        );
    }
}

#[test]
fn native_select_condition_and_only_chosen_arms_are_evaluated() {
    let expressions = [
        Expr::select(
            Expr::load(r(0), Width::U8),
            b(BinaryOp::Add, load(r(1)), load(c(0x1008))),
            load(c(23456)),
        ),
        Expr::select(r(0), c(91), load(r(1))),
        Expr::select(
            Expr::select(r(0), load(r(1)), c(0)),
            load(c(0x1008)),
            load(c(12345)),
        ),
    ];
    let mut inputs = grid();
    inputs.extend([Input::new(0, 23456), Input::new(1, 23456)]);
    for (index, expr) in expressions.into_iter().enumerate() {
        native_compare(
            &returning(vec![set(2, c(81))], expr),
            &inputs,
            &format!("select-{index}"),
        );
    }
}

#[test]
fn native_control_conditions_and_evaluate_nodes_keep_order() {
    for target in [1, 2] {
        let program = Program::new(
            0,
            REGISTERS,
            vec![
                ins(
                    0,
                    vec![set(2, c(17))],
                    Control::Branch {
                        condition: b(BinaryOp::Eq, load(r(0)), load(r(1))),
                        target,
                    },
                ),
                ins(1, vec![set(3, c(19))], Control::Return(c(43))),
                ins(2, vec![set(3, c(23))], Control::Return(c(47))),
            ],
        )
        .unwrap();
        native_compare(&program, &grid(), &format!("branch-{target}"));
    }
}

#[test]
fn native_loop_repeats_sequenced_guard_before_each_iteration() {
    let program = Program::new(
        0,
        REGISTERS,
        vec![
            ins(0, vec![set(2, c(0))], Control::Next),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: b(
                        BinaryOp::Ule,
                        b(BinaryOp::Add, load(r(0)), r(2)),
                        load(r(1)),
                    ),
                    target: 3,
                },
            ),
            ins(2, vec![], Control::Return(r(2))),
            ins(
                3,
                vec![set(2, b(BinaryOp::Add, r(2), c(1)))],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(2), c(3)),
                    target: 1,
                },
            ),
            ins(4, vec![], Control::Return(r(2))),
        ],
    )
    .unwrap();
    native_compare(&program, &grid(), "loop-guard");
}

#[test]
fn native_irreducible_goto_conditions_are_also_sequenced() {
    let program = Program::new(
        0,
        REGISTERS,
        vec![
            ins(
                0,
                vec![set(2, c(0))],
                Control::Branch {
                    condition: r(3),
                    target: 3,
                },
            ),
            ins(
                1,
                vec![set(2, b(BinaryOp::Add, r(2), c(1)))],
                Control::Branch {
                    condition: b(BinaryOp::Eq, load(r(0)), load(r(1))),
                    target: 3,
                },
            ),
            ins(2, vec![], Control::Jump(5)),
            ins(
                3,
                vec![set(2, b(BinaryOp::Add, r(2), c(1)))],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(2), c(2)),
                    target: 1,
                },
            ),
            ins(4, vec![], Control::Jump(5)),
            // Two independent cycles retain the goto path under one split.
            ins(
                5,
                vec![set(2, c(0))],
                Control::Branch {
                    condition: r(3),
                    target: 7,
                },
            ),
            ins(
                6,
                vec![set(2, b(BinaryOp::Add, r(2), c(1)))],
                Control::Jump(7),
            ),
            ins(
                7,
                vec![set(2, b(BinaryOp::Add, r(2), c(1)))],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(2), c(2)),
                    target: 6,
                },
            ),
            ins(8, vec![], Control::Return(r(2))),
        ],
    )
    .unwrap();
    assert!(emit_c(&program).unwrap().fallback_reason.is_some());
    let mut inputs = grid();
    for (i, input) in inputs.iter_mut().enumerate() {
        input.registers[3] = (i & 1) as u64;
    }
    native_compare(&program, &inputs, "gotos");
}

#[test]
fn native_wrapping_addresses_keep_first_fault_and_all_state() {
    let program = returning(
        vec![
            set(2, c(5)),
            store(
                load(r(0)),
                Width::U64,
                b(BinaryOp::Add, load(r(1)), load(c(u64::MAX - 7))),
            ),
        ],
        r(2),
    );
    let mut input = Input::new(u64::MAX - 7, u64::MAX - 15);
    input.base = u64::MAX - 63;
    input.memory[56..64].copy_from_slice(&(u64::MAX - 3).to_le_bytes());
    native_compare(
        &program,
        &[input.clone(), {
            input.registers[0] = u64::MAX;
            input
        }],
        "wrapping",
    );
}

#[test]
fn pure_and_single_read_fast_paths_do_not_allocate_guest_or_c_temporaries() {
    for expr in [
        b(BinaryOp::Add, r(0), c(3)),
        Expr::select(r(0), load(r(1)), c(3)),
    ] {
        let output = emit_c(&returning(vec![], expr)).unwrap();
        assert!(!output.code.contains("nirvana_t"));
        assert!(!output.code.contains("r[8]"));
    }
}

#[test]
fn expression_limits_return_errors_even_for_unreachable_or_lazy_input() {
    let mut deep = c(1);
    for _ in 0..MAX_EXPRESSION_DEPTH {
        deep = b(BinaryOp::Add, c(1), deep);
    }
    for program in [
        returning(vec![], Expr::select(c(1), c(7), deep.clone())),
        Program::new(
            0,
            REGISTERS,
            vec![
                ins(0, vec![], Control::Return(c(7))),
                ins(
                    1,
                    vec![store(deep, Width::U64, c(7))],
                    Control::Return(c(9)),
                ),
            ],
        )
        .unwrap(),
    ] {
        assert_eq!(
            emit_c(&program).unwrap_err(),
            SequenceError::ExpressionTooDeep
        );
    }
}

#[test]
fn temporary_index_overflow_returns_error_instead_of_unsafe_fallback() {
    let program = Program::new(
        0,
        usize::MAX,
        vec![ins(
            0,
            vec![],
            Control::Return(b(BinaryOp::Add, load(c(0x1000)), load(c(0x1008)))),
        )],
    )
    .unwrap();
    assert_eq!(
        emit_c(&program).unwrap_err(),
        SequenceError::RegisterOverflow
    );
}

#[test]
fn native_store_address_plans_and_rhs_plans_have_disjoint_private_temporaries() {
    let address = b(BinaryOp::Add, load(r(0)), load(r(1)));
    let value = Expr::select(
        Expr::load(c(0x1010), Width::U8),
        b(BinaryOp::Xor, load(c(0x1020)), load(c(0x1030))),
        b(BinaryOp::Add, load(c(0x1028)), load(c(0x1038))),
    );
    let program = returning(
        vec![
            set(2, c(0x777)),
            store(address, Width::U64, value),
            set(3, c(0x888)),
        ],
        r(3),
    );
    let mut inputs = grid();
    for input in &mut inputs {
        input.memory[0..8].copy_from_slice(&0x1000_u64.to_le_bytes());
        input.memory[8..16].copy_from_slice(&0x20_u64.to_le_bytes());
    }
    let mut other = inputs[0].clone();
    other.memory[16] = 1;
    inputs.push(other);
    native_compare(&program, &inputs, "store-both-plans");
}

#[test]
fn native_aliasing_stores_read_old_rhs_then_commit_before_later_loads() {
    let program = returning(
        vec![
            store(r(0), Width::U64, b(BinaryOp::Add, load(r(0)), load(r(1)))),
            set(2, b(BinaryOp::Add, load(r(0)), load(r(1)))),
            store(b(BinaryOp::Add, r(0), c(1)), Width::U16, load(r(1))),
            set(3, load(r(0))),
        ],
        b(BinaryOp::Xor, r(2), r(3)),
    );
    native_compare(&program, &grid(), "overlap-alias");
}

#[test]
fn program_wide_budget_returns_error_before_building_or_rendering_any_ast() {
    fn balanced(depth: usize) -> Expr {
        if depth == 0 {
            c(1)
        } else {
            b(BinaryOp::Add, balanced(depth - 1), balanced(depth - 1))
        }
    }
    let program = returning((0..8).map(|_| set(0, balanced(16))).collect(), c(7));
    assert_eq!(
        emit_c(&program).unwrap_err(),
        SequenceError::ExpressionTooLarge
    );
}
