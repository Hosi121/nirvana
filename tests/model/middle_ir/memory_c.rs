use super::*;
use crate::support::{checked_c, native};
use nirvana::{ir::RunStatus, readable, x86};
use std::fmt::Write;

#[test]
fn refined_c_preserves_partial_stores_lazy_reads_and_first_faults() {
    let scratch = native::Scratch::new();
    let p = r(x86::RDI);
    let read = Expr::load(p.clone(), Width::U32);
    let mut statuses = [0; 3];
    let mut observations = 0;
    for case in 0..3 {
        let mut assignments = vec![
            store(p.clone(), Width::U64, c(0x8877665544332211)),
            store(b(B::Add, p.clone(), c(2)), Width::U16, c(0xbbaa)),
        ];
        let result = match case {
            0 => Expr::select(
                Expr::load(b(B::Add, p.clone(), c(8)), Width::U64),
                read.clone(),
                Expr::load(c(u64::MAX), Width::U8),
            ),
            1 => {
                assignments.push(store(b(B::Add, p.clone(), c(56)), Width::U64, read.clone()));
                read.clone()
            }
            _ => b(
                B::Add,
                read.clone(),
                Expr::load(b(B::Add, p.clone(), c(64)), Width::U64),
            ),
        };
        let source = Program::new(
            0,
            32,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments,
                control: Control::Return(result),
            }],
        )
        .unwrap();
        let middle = Function::from_low(&source).unwrap();
        let (refined, evidence) = middle.recover_memory_constants().unwrap();
        assert!(evidence.proved_loads > 0);
        let low = refined.lower().unwrap();
        let mut input = String::new();
        let mut expected = Vec::new();
        for pointer in [4095u64, 4096, 4097, 4104, 4144, 4152, 4159, u64::MAX] {
            for flag in [0u64, 1, u64::MAX] {
                writeln!(input, "{pointer} 13 {flag} 19 23").unwrap();
                let mut memory: Vec<_> = (0..64usize).map(|i| (i * 29 + 7) as u8).collect();
                for (i, v) in [13, flag, 19, 23].into_iter().enumerate() {
                    if let Some(offset) = pointer
                        .checked_add(i as u64 * 8)
                        .and_then(|a| a.checked_sub(4096))
                        .filter(|p| *p <= 56)
                    {
                        memory[offset as usize..offset as usize + 8]
                            .copy_from_slice(&v.to_le_bytes());
                    }
                }
                let mut regs = vec![0; 32];
                regs[x86::RDI] = pointer;
                regs[x86::RSP] = 4160;
                let report = source.run_with_memory(&regs, 4096, &memory, 4).unwrap();
                assert_eq!(
                    refined.run_with_memory(&regs, 4096, &memory, 4).unwrap(),
                    report
                );
                let mut row = match report.status {
                    RunStatus::Returned(value) => {
                        statuses[0] += 1;
                        vec![0, 0, 0, 0, value]
                    }
                    RunStatus::Fault(fault) => {
                        let access = if fault.access == nirvana::ir::AccessKind::Read {
                            1
                        } else {
                            2
                        };
                        statuses[access] += 1;
                        vec![
                            1,
                            fault.address,
                            access as u64,
                            fault.width.bytes() as u64,
                            0,
                        ]
                    }
                    _ => panic!("bounded straight line"),
                };
                row.extend(
                    report
                        .state
                        .memory
                        .chunks_exact(8)
                        .map(|b| u64::from_le_bytes(b.try_into().unwrap())),
                );
                expected.push(row);
            }
        }
        for coalesce in [false, true] {
            let options = readable::ReadableOptions {
                stack_register: Some(Reg(x86::RSP)),
                recover_objects: true,
                coalesce_locals: coalesce,
                compact_memory: true,
            };
            // Exercise materialization even if the render selection keeps baseline.
            let materialized = readable::emit_readable_c_with_options(&low, options).unwrap();
            let selected = readable::emit_middle_c_with_options(&middle, options).unwrap();
            for (name, output) in [("materialized", materialized), ("selected", selected)] {
                let path = scratch.0.join(format!("memory-{case}-{coalesce}-{name}.c"));
                std::fs::write(&path, checked_c::source(&output, 32, 4)).unwrap();
                for opt in ["-O0", "-O2"] {
                    let binary = path.with_extension(format!("{opt}.bin"));
                    native::compile_c(
                        &path,
                        &binary,
                        &[
                            opt,
                            "-fsanitize=undefined",
                            "-fno-sanitize-recover=undefined",
                        ],
                    );
                    assert_eq!(native::run_fields(&binary, &input, 13), expected);
                    observations += expected.len();
                }
            }
        }
    }
    assert!(statuses.into_iter().all(|n| n > 0));
    assert_eq!(observations, 576);
}
