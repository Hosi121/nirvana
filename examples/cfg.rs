use nirvana::analysis::ControlFlowAnalysis;
use nirvana::cfg::{Cfg, Flow, Instruction};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let name = std::env::args().nth(1).unwrap_or_else(|| "loop".into());
    // These are hand-authored control-flow facts, not decoded machine code.
    let flows = match name.as_str() {
        "diamond" => vec![Flow::Branch(2), Flow::Jump(3), Flow::Next, Flow::Return],
        "loop" => vec![
            Flow::Next,
            Flow::Branch(4),
            Flow::Next,
            Flow::Jump(1),
            Flow::Return,
        ],
        "irreducible" => vec![
            Flow::Branch(2),
            Flow::Jump(2),
            Flow::Branch(1),
            Flow::Return,
        ],
        "unknown" => vec![Flow::Branch(2), Flow::Return, Flow::IndirectJump],
        _ => {
            return Err(
                "usage: cargo run --example cfg -- [diamond|loop|irreducible|unknown]".into(),
            );
        }
    };
    let instructions = flows
        .into_iter()
        .enumerate()
        .map(|(address, flow)| Instruction::new(address as u64, 1, flow))
        .collect();
    let cfg = Cfg::build(0, instructions)?;
    // Comments keep the entire output valid DOT, suitable for Graphviz.
    match ControlFlowAnalysis::compute(&cfg) {
        Ok(analysis) => {
            println!("// reducible: {}", analysis.is_reducible());
            for block in cfg.blocks() {
                println!(
                    "// {}: dominators={:?}, idom={:?}",
                    block.id,
                    analysis.dominators(block.id),
                    analysis.immediate_dominator(block.id)
                );
            }
            for natural_loop in analysis.natural_loops() {
                println!(
                    "// loop: header={}, latches={:?}, body={:?}",
                    natural_loop.header, natural_loop.latches, natural_loop.body
                );
            }
        }
        Err(error) => println!("// {error}"),
    }
    print!("{}", cfg.to_dot());
    Ok(())
}
