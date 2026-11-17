mod programs;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let name = std::env::args().nth(1).unwrap_or_else(|| "diamond".into());
    let program = programs::named(&name)
        .ok_or_else(|| format!("unknown example {name}; choose {:?}", programs::NAMES))?;
    let output = nirvana::emit::emit_c(&program)?;
    if let Some(reason) = output.fallback_reason {
        eprintln!("retaining goto control flow: {reason}");
    }
    print!("{}", output.code);
    Ok(())
}
