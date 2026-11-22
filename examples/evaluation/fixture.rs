//! Shared fixed entry/RAM profile for M0 semantic probes and path inputs.
pub const BASE: u64 = 4096;
pub const SIZE: usize = 512;
pub const STACK: u64 = BASE + SIZE as u64 - 8;
pub const POINTER: u64 = BASE + 128;

pub fn memory(words: [u64; 4], pointer: u64) -> Vec<u8> {
    let mut ram: Vec<_> = (0..SIZE).map(|n| (n * 29 + 7) as u8).collect();
    for (n, value) in words.into_iter().enumerate() {
        if let Some(offset) = pointer
            .checked_add(n as u64 * 8)
            .and_then(|p| p.checked_sub(BASE))
            .filter(|p| *p <= SIZE as u64 - 8)
        {
            ram[offset as usize..offset as usize + 8].copy_from_slice(&value.to_le_bytes());
        }
    }
    ram
}

pub fn registers(count: usize, pointer: u64) -> Vec<u64> {
    let mut regs = vec![0; count];
    regs[nirvana::x86::RDI] = pointer;
    regs[nirvana::x86::RSP] = STACK;
    regs
}
