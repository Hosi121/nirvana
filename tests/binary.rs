//! binary integration suite.
#[allow(dead_code)]
mod support;

#[path = "binary/divide_arithmetic.rs"]
mod divide_arithmetic;
#[path = "binary/effects_frontend.rs"]
mod effects_frontend;
#[path = "binary/eh_frame.rs"]
mod eh_frame;
#[path = "binary/elf.rs"]
mod elf;
#[path = "binary/elf_context.rs"]
mod elf_context;
#[path = "binary/jump_table_context.rs"]
mod jump_table_context;
#[path = "binary/jump_tables.rs"]
mod jump_tables;
#[path = "binary/linked_elf.rs"]
mod linked_elf;
#[path = "binary/loader.rs"]
mod loader;
#[path = "binary/object_refs.rs"]
mod object_refs;
#[path = "binary/reference_decode.rs"]
mod reference_decode;
#[path = "binary/x86.rs"]
mod x86;
#[path = "binary/x86_bswap.rs"]
mod x86_bswap;
#[path = "binary/x86_bt.rs"]
mod x86_bt;
#[path = "binary/x86_double_shift.rs"]
mod x86_double_shift;
#[path = "binary/x86_movbe.rs"]
mod x86_movbe;
#[path = "binary/x86_mul.rs"]
mod x86_mul;
#[path = "binary/x86_rotate.rs"]
mod x86_rotate;
#[path = "binary/x86_strings.rs"]
mod x86_strings;
#[path = "binary/x86_tls.rs"]
mod x86_tls;
#[path = "binary/x86_vector.rs"]
mod x86_vector;
