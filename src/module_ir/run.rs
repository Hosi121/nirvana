use super::{Fault, Instruction, Limit, Limits, Program, ROOT_RETURN, Report, Status, Target};
use crate::ir::{AccessKind, Control, ExecutionError, Machine, Stop, Width};
use crate::x86::{RAX, RSP};

/// Explicit external effects. Implementations receive checked guest bytes,
/// never a native pointer derived from a guest address.
pub trait Environment {
    fn call(&mut self, name: &str, context: &mut ExternalContext<'_>) -> Result<(), Status>;
}
pub struct RejectImports;
impl Environment for RejectImports {
    fn call(&mut self, name: &str, _: &mut ExternalContext<'_>) -> Result<(), Status> {
        Err(Status::UnsupportedImport(name.to_owned()))
    }
}
pub struct ExternalContext<'a> {
    machine: &'a mut Machine,
    errno_address: u64,
}
impl ExternalContext<'_> {
    pub fn registers(&self) -> &[u64] {
        &self.machine.registers
    }
    pub fn registers_mut(&mut self) -> &mut [u64] {
        &mut self.machine.registers
    }
    pub fn errno_address(&self) -> u64 {
        self.errno_address
    }
    pub fn read(&self, address: u64, width: usize) -> Result<&[u8], Status> {
        self.machine
            .checked_bytes(address, width)
            .ok_or(Status::Fault(Fault {
                address,
                width: width as u64,
                access: AccessKind::Read,
            }))
    }
    pub fn write(&mut self, address: u64, bytes: &[u8]) -> Result<(), Status> {
        self.machine
            .checked_bytes_mut(address, bytes.len())
            .ok_or(Status::Fault(Fault {
                address,
                width: bytes.len() as u64,
                access: AccessKind::Write,
            }))?
            .copy_from_slice(bytes);
        Ok(())
    }
    /// One deterministic caller-clobber policy permitted by the SysV ABI.
    pub fn return_bits(&mut self, value: u64) {
        for register in [0, 1, 2, 6, 7, 8, 9, 10, 11, 16, 17, 18, 19, 20] {
            self.machine.registers[register] = 0;
        }
        self.machine.registers[32..64].fill(0);
        self.machine.registers[RAX] = value;
    }
}

impl Program {
    pub fn run(
        &self,
        registers: &[u64],
        base: u64,
        memory: &[u8],
        limits: Limits,
        environment: &mut impl Environment,
    ) -> Result<Report, ExecutionError> {
        self.run_from(self.entry(), registers, base, memory, limits, environment)
    }

    /// Resume at a guest PC using the same instruction/import semantics.
    pub fn run_from(
        &self,
        pc: u64,
        registers: &[u64],
        base: u64,
        memory: &[u8],
        limits: Limits,
        environment: &mut impl Environment,
    ) -> Result<Report, ExecutionError> {
        let mut machine = Machine::with_memory(
            self.register_count(),
            registers,
            base,
            memory,
            limits.instructions,
        )?;
        if let Some(layout) = self.memory_layout() {
            machine.set_memory_layout(layout)?;
        }
        let mut pc = pc;
        let mut imports = 0usize;
        let result = (|| -> Result<u64, Status> {
            loop {
                if pc == ROOT_RETURN {
                    return Ok(machine.registers[RAX]);
                }
                if let Ok(index) = self.imports().binary_search_by_key(&pc, |i| i.address) {
                    if imports == limits.imports {
                        return Err(Status::Suspended(Limit::Imports));
                    }
                    imports += 1;
                    environment.call(
                        &self.imports()[index].name,
                        &mut ExternalContext {
                            machine: &mut machine,
                            errno_address: self.errno_address(),
                        },
                    )?;
                    pc = pop(&mut machine, 0)?;
                    continue;
                }
                let index = self
                    .instructions()
                    .binary_search_by_key(&pc, Instruction::address)
                    .map_err(|_| Status::UnknownTarget(pc))?;
                match &self.instructions()[index] {
                    Instruction::Divide {
                        source,
                        width,
                        signed,
                        size,
                        ..
                    } => {
                        machine.step(pc, &[]).map_err(stop)?;
                        let divisor = source.evaluate(&machine).map_err(fault)?;
                        let (a, d) = crate::x86::divide::evaluate(
                            *width,
                            *signed,
                            machine.registers[crate::x86::RAX],
                            machine.registers[crate::x86::RDX],
                            divisor,
                        )
                        .ok_or(Status::DivideError)?;
                        machine.registers[crate::x86::RAX] = a;
                        machine.registers[crate::x86::RDX] = d;
                        pc += u64::from(*size);
                    }
                    Instruction::Core(instruction) => {
                        machine.step(pc, &instruction.assignments).map_err(stop)?;
                        pc = match &instruction.control {
                            Control::Next => pc + u64::from(instruction.size),
                            Control::Jump(target) => *target,
                            Control::Branch { condition, target } => {
                                if condition.evaluate(&machine).map_err(fault)? != 0 {
                                    *target
                                } else {
                                    pc + u64::from(instruction.size)
                                }
                            }
                            Control::Return(value) => {
                                return value.evaluate(&machine).map_err(fault);
                            }
                        };
                    }
                    Instruction::Transfer { target, link, .. } => {
                        machine.step(pc, &[]).map_err(stop)?;
                        let mut value = match target {
                            Target::Value(value) => value.evaluate(&machine).map_err(fault)?,
                            Target::Plt(_) => 0,
                        };
                        if let Some(next) = link {
                            machine.registers[RSP] = machine.registers[RSP].wrapping_sub(8);
                            machine
                                .store(machine.registers[RSP], Width::U64, *next)
                                .map_err(fault)?;
                        }
                        if let Target::Plt(address) = target {
                            value = machine.load(*address, Width::U64).map_err(fault)?;
                        }
                        pc = value;
                    }
                    Instruction::Return { extra_pop, .. } => {
                        machine.step(pc, &[]).map_err(stop)?;
                        pc = pop(&mut machine, *extra_pop)?;
                    }
                    Instruction::Vector(instruction) => {
                        machine.step(pc, &[]).map_err(stop)?;
                        if let Some(memory) = &instruction.memory {
                            let address = memory.address.evaluate(&machine).map_err(fault)?;
                            let observation = Fault {
                                address,
                                width: u64::from(memory.width),
                                access: memory.access,
                            };
                            if machine
                                .checked_range(address, memory.width as usize, memory.access)
                                .is_none()
                            {
                                return Err(Status::Fault(observation));
                            }
                            if memory.alignment == 0 || address % u64::from(memory.alignment) != 0 {
                                return Err(Status::Alignment(observation));
                            }
                        }
                        machine.assign(&instruction.assignments).map_err(stop)?;
                        pc += u64::from(instruction.size);
                    }
                }
            }
        })();
        Ok(Report {
            status: match result {
                Ok(value) => Status::Returned(value),
                Err(status) => status,
            },
            state: machine.snapshot(),
            imports,
            pc,
        })
    }
}
fn pop(machine: &mut Machine, extra: u16) -> Result<u64, Status> {
    let target = machine
        .load(machine.registers[RSP], Width::U64)
        .map_err(fault)?;
    machine.registers[RSP] = machine.registers[RSP].wrapping_add(8 + u64::from(extra));
    Ok(target)
}
fn fault(value: crate::ir::MemoryFault) -> Status {
    Status::Fault(value.into())
}
fn stop(value: Stop) -> Status {
    match value {
        Stop::Fault(value) => fault(value),
        Stop::Limit => Status::Suspended(Limit::Instructions),
    }
}
