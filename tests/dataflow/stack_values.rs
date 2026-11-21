//! Adversarial reaching-store tests, independent of the analysis implementation.
//! The concrete oracle tracks actual byte addresses and the last overlapping
//! executed store, then checks coverage by a static definition set or unknown.

use std::collections::BTreeSet;

use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, MemoryFault, Place, Program,
    Reg, RunStatus, Width,
};
use nirvana::stack_values::{StackRead, StackValues};

use crate::support::ir::c;
use crate::support::ir::r;
fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn add(left: Expr, right: Expr) -> Expr {
    binary(BinaryOp::Add, left, right)
}
fn address(offset: i64) -> Expr {
    add(r(0), c(offset as u64))
}
fn load(offset: i64, width: Width) -> Expr {
    Expr::load(address(offset), width)
}
fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}
fn store(offset: i64, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: address(offset),
            width,
        },
        value,
    }
}
fn raw_store(at: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address: at, width },
        value,
    }
}
fn instruction(pc: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address: pc,
        size: 1,
        assignments,
        control,
    }
}
fn program(instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, 4, instructions).unwrap()
}
fn analyze(program: &Program) -> StackValues {
    StackValues::analyze(program, Reg(0)).expect("bounded directed input should analyze")
}
fn definition(a: &StackValues, pc: u64, assignment: usize, offset: i64, width: Width) -> usize {
    let found: Vec<_> = a
        .definitions()
        .iter()
        .filter(|d| {
            d.instruction == pc
                && d.assignment == assignment
                && d.location.offset == offset
                && d.location.width == width
        })
        .collect();
    assert_eq!(
        found.len(),
        1,
        "definition at {pc}:{assignment}, offset={offset}, width={width:?}"
    );
    found[0].id
}
fn reads(
    a: &StackValues,
    pc: u64,
    assignment: usize,
    offset: i64,
    width: Width,
) -> Vec<&StackRead> {
    let found: Vec<_> = a
        .reads()
        .iter()
        .filter(|r| {
            r.instruction == pc
                && r.assignment == assignment
                && r.location.offset == offset
                && r.location.width == width
        })
        .collect();
    assert!(
        !found.is_empty(),
        "missing read at {pc}:{assignment}, offset={offset}, width={width:?}"
    );
    found
}
fn reaching(
    a: &StackValues,
    pc: u64,
    assignment: usize,
    offset: i64,
    width: Width,
    ids: &[usize],
    unknown: bool,
) {
    let expected: BTreeSet<_> = ids.iter().copied().collect();
    for read in reads(a, pc, assignment, offset, width) {
        assert_eq!(
            read.definitions.iter().copied().collect::<BTreeSet<_>>(),
            expected,
            "definitions at {pc}:{assignment}, offset={offset}"
        );
        assert_eq!(
            read.has_unknown, unknown,
            "unknown at {pc}:{assignment}, offset={offset}"
        );
    }
}
fn unknown(a: &StackValues, pc: u64, assignment: usize, offset: i64, width: Width) {
    for read in reads(a, pc, assignment, offset, width) {
        assert!(
            read.has_unknown,
            "missing unknown at {pc}:{assignment}, offset={offset}"
        );
    }
}

#[derive(Clone, Copy)]
struct Written {
    pc: u64,
    assignment: usize,
    address: u64,
    width: Width,
}
struct Concrete<'a> {
    analysis: &'a StackValues,
    entry_sp: u64,
    registers: Vec<u64>,
    memory: Vec<u8>,
    history: Vec<Written>,
    checked_reads: usize,
}
impl Concrete<'_> {
    fn offset(&self, address: u64, width: Width, access: AccessKind) -> Result<usize, MemoryFault> {
        let offset = usize::try_from(address).ok().filter(|offset| {
            offset
                .checked_add(width.bytes())
                .is_some_and(|end| end <= self.memory.len())
        });
        if address.checked_add(width.bytes() as u64 - 1).is_none() || offset.is_none() {
            return Err(MemoryFault {
                access,
                address,
                width,
            });
        }
        Ok(offset.unwrap())
    }
    fn check_read(&mut self, pc: u64, assignment: usize, address: u64, width: Width) {
        let offset = address.wrapping_sub(self.entry_sp) as i64;
        for read in self.analysis.reads().iter().filter(|r| {
            r.instruction == pc
                && r.assignment == assignment
                && r.location.offset == offset
                && r.location.width == width
        }) {
            self.checked_reads += 1;
            let last = self.history.iter().rev().find(|w| {
                (w.address as u128) < address as u128 + width.bytes() as u128
                    && (address as u128) < w.address as u128 + w.width.bytes() as u128
            });
            let exact = last
                .filter(|w| w.address == address && w.width == width)
                .and_then(|w| {
                    self.analysis.definitions().iter().find(|d| {
                        d.instruction == w.pc
                            && d.assignment == w.assignment
                            && d.location.offset == offset
                            && d.location.width == width
                    })
                });
            match exact {
                Some(def) => assert!(
                    read.has_unknown || read.definitions.contains(&def.id),
                    "actual exact store {}:{} missing from read {pc}:{assignment}",
                    def.instruction,
                    def.assignment
                ),
                None => assert!(
                    read.has_unknown,
                    "read {pc}:{assignment} has initial/partial/untracked concrete bytes"
                ),
            }
        }
    }
    fn eval(&mut self, expression: &Expr, pc: u64, assignment: usize) -> Result<u64, MemoryFault> {
        Ok(match expression {
            Expr::Const(value) => *value,
            Expr::Unary(op, value) => {
                crate::support::ir::unary_value(*op, self.eval(value, pc, assignment)?)
            }
            Expr::Register(reg) => self.registers[reg.0],
            Expr::Load { address, width } => {
                let address = self.eval(address, pc, assignment)?;
                self.check_read(pc, assignment, address, *width);
                let offset = self.offset(address, *width, AccessKind::Read)?;
                let mut value = [0; 8];
                value[..width.bytes()]
                    .copy_from_slice(&self.memory[offset..offset + width.bytes()]);
                u64::from_le_bytes(value)
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let condition = self.eval(condition, pc, assignment)?;
                self.eval(
                    if condition != 0 { taken } else { not_taken },
                    pc,
                    assignment,
                )?
            }
            Expr::Binary(op, left, right) => {
                let left = self.eval(left, pc, assignment)?;
                let right = self.eval(right, pc, assignment)?;
                match op {
                    BinaryOp::Add => left.wrapping_add(right),
                    BinaryOp::Sub => left.wrapping_sub(right),
                    BinaryOp::Mul => left.wrapping_mul(right),
                    BinaryOp::And => left & right,
                    BinaryOp::Or => left | right,
                    BinaryOp::Xor => left ^ right,
                    BinaryOp::Shl => left.wrapping_shl((right & 63) as u32),
                    BinaryOp::Shr => left.wrapping_shr((right & 63) as u32),
                    BinaryOp::Eq => u64::from(left == right),
                    BinaryOp::Ne => u64::from(left != right),
                    BinaryOp::Ult => u64::from(left < right),
                    BinaryOp::Ule => u64::from(left <= right),
                    BinaryOp::UMulHigh => ((u128::from(left) * u128::from(right)) >> 64) as u64,
                    BinaryOp::SMulHigh => {
                        ((i128::from(left as i64) * i128::from(right as i64)) >> 64) as u64
                    }
                    BinaryOp::AShr => ((left as i64) >> (right & 63)) as u64,
                }
            }
        })
    }
}
fn concrete(
    p: &Program,
    analysis: &StackValues,
    input: [u64; 4],
    initial: &[u8],
    limit: usize,
) -> usize {
    let mut state = Concrete {
        analysis,
        entry_sp: input[0],
        registers: input.to_vec(),
        memory: initial.to_vec(),
        history: vec![],
        checked_reads: 0,
    };
    let mut pc = p.cfg().block(p.cfg().entry()).start;
    let mut trace = Vec::new();
    let mut remaining = limit;
    let status = loop {
        if remaining == 0 {
            break RunStatus::Suspended;
        }
        remaining -= 1;
        trace.push(pc);
        let instruction = p.instructions().iter().find(|i| i.address == pc).unwrap();
        let result = (|| -> Result<Option<u64>, MemoryFault> {
            for (index, assignment) in instruction.assignments.iter().enumerate() {
                match &assignment.destination {
                    Place::Register(reg) => {
                        state.registers[reg.0] = state.eval(&assignment.value, pc, index)?
                    }
                    Place::Memory { address, width } => {
                        let address = state.eval(address, pc, index)?;
                        let offset = state.offset(address, *width, AccessKind::Write)?;
                        let value = state.eval(&assignment.value, pc, index)?.to_le_bytes();
                        state.memory[offset..offset + width.bytes()]
                            .copy_from_slice(&value[..width.bytes()]);
                        state.history.push(Written {
                            pc,
                            assignment: index,
                            address,
                            width: *width,
                        });
                    }
                }
            }
            let point = instruction.assignments.len();
            match &instruction.control {
                Control::Return(value) => return Ok(Some(state.eval(value, pc, point)?)),
                Control::Next => pc += u64::from(instruction.size),
                Control::Jump(target) => pc = *target,
                Control::Branch { condition, target } => {
                    pc = if state.eval(condition, pc, point)? != 0 {
                        *target
                    } else {
                        pc + u64::from(instruction.size)
                    }
                }
            }
            Ok(None)
        })();
        match result {
            Ok(Some(value)) => break RunStatus::Returned(value),
            Err(fault) => break RunStatus::Fault(fault),
            Ok(None) => {}
        }
    };
    let report = p.run_with_memory(&input, 0, initial, limit).unwrap();
    assert_eq!(status, report.status);
    assert_eq!(state.registers, report.state.registers);
    assert_eq!(state.memory, report.state.memory);
    assert_eq!(trace, report.state.trace);
    assert_eq!(Some(pc), report.state.instruction);
    state.checked_reads
}
fn replay(p: &Program, analysis: &StackValues, inputs: &[[u64; 4]]) {
    let memory: Vec<_> = (0..64).map(|i| (i * 17 + 3) as u8).collect();
    let mut checked = 0;
    for input in inputs {
        for limit in [0, 1, 2, 4, 16, 40] {
            checked += concrete(p, analysis, *input, &memory, limit);
        }
    }
    assert!(checked > 0, "oracle must reach a proven stack read");
}

#[test]
fn exact_full_width_stores_replace_the_previous_definition() {
    let p = program(vec![instruction(
        0,
        vec![
            store(0, Width::U64, c(11)),
            set(2, load(0, Width::U64)),
            store(0, Width::U64, c(22)),
            set(3, load(0, Width::U64)),
        ],
        Control::Return(r(3)),
    )]);
    let a = analyze(&p);
    let first = definition(&a, 0, 0, 0, Width::U64);
    let last = definition(&a, 0, 2, 0, Width::U64);
    assert_ne!(first, last);
    reaching(&a, 0, 1, 0, Width::U64, &[first], false);
    reaching(&a, 0, 3, 0, Width::U64, &[last], false);
    replay(&p, &a, &[[16, 0, 0, 0]]);
}

#[test]
fn diamond_joins_union_both_definitions_without_unknown() {
    let p = program(vec![
        instruction(
            0,
            vec![],
            Control::Branch {
                condition: r(1),
                target: 2,
            },
        ),
        instruction(1, vec![store(0, Width::U64, c(11))], Control::Jump(3)),
        instruction(2, vec![store(0, Width::U64, c(22))], Control::Jump(3)),
        instruction(3, vec![set(2, load(0, Width::U64))], Control::Return(r(2))),
    ]);
    let a = analyze(&p);
    let left = definition(&a, 1, 0, 0, Width::U64);
    let right = definition(&a, 2, 0, 0, Width::U64);
    reaching(&a, 3, 0, 0, Width::U64, &[left, right], false);
    replay(
        &p,
        &a,
        &[[16, 0, 0, 0], [16, 1, 0, 0], [16, u64::MAX, 0, 0]],
    );
}

#[test]
fn a_path_without_a_store_keeps_initial_unknown_at_the_join() {
    let p = program(vec![
        instruction(
            0,
            vec![],
            Control::Branch {
                condition: r(1),
                target: 2,
            },
        ),
        instruction(1, vec![store(0, Width::U64, c(11))], Control::Jump(3)),
        instruction(2, vec![], Control::Jump(3)),
        instruction(3, vec![set(2, load(0, Width::U64))], Control::Return(r(2))),
    ]);
    let a = analyze(&p);
    let left = definition(&a, 1, 0, 0, Width::U64);
    reaching(&a, 3, 0, 0, Width::U64, &[left], true);
    replay(&p, &a, &[[16, 0, 0, 0], [16, 1, 0, 0]]);
}

#[test]
fn loop_header_merges_entry_and_loop_store_definitions() {
    let p = program(vec![
        instruction(0, vec![store(0, Width::U64, c(0))], Control::Jump(1)),
        instruction(
            1,
            vec![
                set(2, load(0, Width::U64)),
                store(0, Width::U64, add(r(2), c(1))),
            ],
            Control::Branch {
                condition: binary(BinaryOp::Ult, r(2), r(1)),
                target: 1,
            },
        ),
        instruction(2, vec![set(3, load(0, Width::U64))], Control::Return(r(3))),
    ]);
    let a = analyze(&p);
    let entry = definition(&a, 0, 0, 0, Width::U64);
    let update = definition(&a, 1, 1, 0, Width::U64);
    reaching(&a, 1, 0, 0, Width::U64, &[entry, update], false);
    reaching(&a, 2, 0, 0, Width::U64, &[update], false);
    replay(&p, &a, &[[16, 0, 0, 0], [16, 3, 0, 0]]);
}

#[test]
fn entry_backedge_never_discards_initial_unknown() {
    let p = program(vec![
        instruction(
            0,
            vec![set(2, load(0, Width::U64)), store(0, Width::U64, c(1))],
            Control::Branch {
                condition: r(1),
                target: 0,
            },
        ),
        instruction(1, vec![], Control::Return(r(2))),
    ]);
    let a = analyze(&p);
    let update = definition(&a, 0, 1, 0, Width::U64);
    reaching(&a, 0, 0, 0, Width::U64, &[update], true);
    replay(&p, &a, &[[16, 0, 0, 0], [16, 1, 0, 0]]);
}

#[test]
fn store_rhs_reads_same_cell_before_generating_the_new_definition() {
    let p = program(vec![instruction(
        0,
        vec![
            store(0, Width::U64, c(7)),
            store(0, Width::U64, add(load(0, Width::U64), c(1))),
            set(2, load(0, Width::U64)),
        ],
        Control::Return(r(2)),
    )]);
    let a = analyze(&p);
    let before = definition(&a, 0, 0, 0, Width::U64);
    let after = definition(&a, 0, 1, 0, Width::U64);
    reaching(&a, 0, 1, 0, Width::U64, &[before], false);
    reaching(&a, 0, 2, 0, Width::U64, &[after], false);
    replay(&p, &a, &[[16, 0, 0, 0]]);
}

#[test]
fn loads_in_unknown_store_address_and_rhs_both_see_pre_store_facts() {
    let p = program(vec![instruction(
        0,
        vec![
            store(0, Width::U64, c(7)),
            store(8, Width::U64, r(0)),
            raw_store(load(8, Width::U64), Width::U64, load(0, Width::U64)),
            set(2, load(0, Width::U64)),
        ],
        Control::Return(r(2)),
    )]);
    let a = analyze(&p);
    let value = definition(&a, 0, 0, 0, Width::U64);
    let pointer = definition(&a, 0, 1, 8, Width::U64);
    reaching(&a, 0, 2, 8, Width::U64, &[pointer], false);
    reaching(&a, 0, 2, 0, Width::U64, &[value], false);
    unknown(&a, 0, 3, 0, Width::U64);
    replay(&p, &a, &[[16, 0, 0, 0]]);
}

#[test]
fn unknown_external_store_may_alias_every_stack_cell() {
    let p = program(vec![instruction(
        0,
        vec![
            store(0, Width::U64, c(7)),
            store(8, Width::U64, c(9)),
            raw_store(r(1), Width::U8, c(0xaa)),
            set(2, load(0, Width::U64)),
            set(3, load(8, Width::U64)),
        ],
        Control::Return(r(3)),
    )]);
    let a = analyze(&p);
    unknown(&a, 0, 3, 0, Width::U64);
    unknown(&a, 0, 4, 8, Width::U64);
    replay(
        &p,
        &a,
        &[
            [16, 16, 0, 0],
            [16, 24, 0, 0],
            [16, 48, 0, 0],
            [16, 100, 0, 0],
        ],
    );
}

#[test]
fn disjoint_stores_preserve_facts_but_partial_overlaps_do_not_compose() {
    let p = program(vec![instruction(
        0,
        vec![
            store(0, Width::U64, c(7)),
            store(8, Width::U8, c(9)),
            set(2, load(0, Width::U64)),
            store(0, Width::U32, c(11)),
            store(4, Width::U32, c(13)),
            set(2, load(0, Width::U64)),
            set(2, load(0, Width::U32)),
            set(3, load(4, Width::U32)),
        ],
        Control::Return(r(3)),
    )]);
    let a = analyze(&p);
    let full = definition(&a, 0, 0, 0, Width::U64);
    let low = definition(&a, 0, 3, 0, Width::U32);
    let high = definition(&a, 0, 4, 4, Width::U32);
    reaching(&a, 0, 2, 0, Width::U64, &[full], false);
    unknown(&a, 0, 5, 0, Width::U64);
    reaching(&a, 0, 6, 0, Width::U32, &[low], false);
    reaching(&a, 0, 7, 4, Width::U32, &[high], false);
    replay(&p, &a, &[[16, 0, 0, 0]]);
}

#[test]
fn modular_overlap_at_zero_and_the_signed_offset_boundary_is_conservative() {
    for offset in [-4i64, i64::MAX] {
        let overlap = offset.wrapping_add(4);
        let adjacent = offset.wrapping_add(8);
        let p = program(vec![instruction(
            0,
            vec![
                store(offset, Width::U64, c(7)),
                store(adjacent, Width::U8, c(9)),
                set(2, load(offset, Width::U64)),
                store(overlap, Width::U8, c(11)),
                set(2, load(offset, Width::U64)),
                set(3, load(overlap, Width::U8)),
            ],
            Control::Return(r(3)),
        )]);
        let a = analyze(&p);
        let full = definition(&a, 0, 0, offset, Width::U64);
        let byte = definition(&a, 0, 3, overlap, Width::U8);
        reaching(&a, 0, 2, offset, Width::U64, &[full], false);
        unknown(&a, 0, 4, offset, Width::U64);
        reaching(&a, 0, 5, overlap, Width::U8, &[byte], false);
        let sp = 16u64.wrapping_sub(offset as u64);
        replay(&p, &a, &[[sp, 0, 0, 0]]);
    }
}

#[test]
fn stack_pointer_updates_and_frame_copies_use_the_original_entry_origin() {
    let p = program(vec![instruction(
        0,
        vec![
            set(3, r(0)),
            set(0, binary(BinaryOp::Sub, r(0), c(8))),
            raw_store(r(0), Width::U64, c(7)),
            set(2, Expr::load(binary(BinaryOp::Sub, r(3), c(8)), Width::U64)),
        ],
        Control::Return(r(2)),
    )]);
    let a = analyze(&p);
    let id = definition(&a, 0, 2, -8, Width::U64);
    reaching(&a, 0, 3, -8, Width::U64, &[id], false);
    replay(&p, &a, &[[24, 0, 0, 0]]);
}

#[test]
fn nested_loads_record_the_known_inner_cell_without_forwarding_a_pointer_value() {
    let p = program(vec![instruction(
        0,
        vec![
            store(0, Width::U64, c(32)),
            store(16, Width::U64, c(42)),
            set(2, Expr::load(load(0, Width::U64), Width::U64)),
        ],
        Control::Return(r(2)),
    )]);
    let a = analyze(&p);
    let pointer = definition(&a, 0, 0, 0, Width::U64);
    reaching(&a, 0, 2, 0, Width::U64, &[pointer], false);
    assert_eq!(
        a.reads()
            .iter()
            .filter(|r| r.instruction == 0 && r.assignment == 2)
            .count(),
        1
    );
    replay(&p, &a, &[[16, 0, 0, 0]]);
}

#[test]
fn lazy_select_arms_are_potential_reads_and_control_point_is_after_assignments() {
    let p = program(vec![instruction(
        0,
        vec![
            store(0, Width::U8, c(7)),
            store(1, Width::U8, c(9)),
            set(
                2,
                Expr::select(r(1), load(0, Width::U8), load(1, Width::U8)),
            ),
        ],
        Control::Return(Expr::select(
            load(2, Width::U8),
            load(0, Width::U8),
            load(1, Width::U8),
        )),
    )]);
    let a = analyze(&p);
    let left = definition(&a, 0, 0, 0, Width::U8);
    let right = definition(&a, 0, 1, 1, Width::U8);
    for point in [2, 3] {
        reaching(&a, 0, point, 0, Width::U8, &[left], false);
        reaching(&a, 0, point, 1, Width::U8, &[right], false);
    }
    unknown(&a, 0, 3, 2, Width::U8);
    replay(&p, &a, &[[16, 0, 0, 0], [16, 1, 0, 0]]);
}

#[test]
fn invalid_stack_register_and_whole_input_depth_fail_without_partial_analysis() {
    let p = program(vec![instruction(
        0,
        vec![store(0, Width::U64, c(7)), set(2, load(0, Width::U64))],
        Control::Return(r(2)),
    )]);
    assert!(StackValues::analyze(&p, Reg(4)).is_none());
    assert!(StackValues::analyze(&p, Reg(usize::MAX)).is_none());
    let mut deep = c(0);
    for _ in 0..512 {
        deep = add(deep, c(0));
    }
    let p = program(vec![
        instruction(
            0,
            vec![store(0, Width::U64, c(7)), set(2, load(0, Width::U64))],
            Control::Return(r(2)),
        ),
        instruction(
            10,
            vec![raw_store(deep, Width::U8, c(1))],
            Control::Return(c(0)),
        ),
    ]);
    assert!(
        StackValues::analyze(&p, Reg(0)).is_none(),
        "unreachable deep address must discard prior facts"
    );
}
