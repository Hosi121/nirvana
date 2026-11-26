//! Export raw syntax, with real validator verdicts, for the finite Quint trial.
use nirvana as library;
#[path = "../tests/support/formal_structure.rs"]
mod cases;
use library::ir::Control;
use library::structure::Node;
use library::structure_verify::{ValidationError, validate};
use std::collections::BTreeMap;

#[derive(Clone, Default)]
struct Raw {
    kind: usize,
    pc: u64,
    token: usize,
    first: usize,
    other: usize,
    next: usize,
    level: usize,
}
impl Raw {
    fn json(&self) -> String {
        format!(
            "{{\"kind\":{},\"pc\":{},\"token\":{},\"first\":{},\"other\":{},\"next\":{},\"level\":{}}}",
            self.kind, self.pc, self.token, self.first, self.other, self.next, self.level
        )
    }
}
fn token(tokens: &mut BTreeMap<String, usize>, value: String) -> usize {
    let next = tokens.len();
    *tokens.entry(value).or_insert(next)
}
fn sequence(nodes: &[Node], arena: &mut Vec<Raw>, tokens: &mut BTreeMap<String, usize>) -> usize {
    let mut next = 0;
    // This encodes lexical child/sibling links, without resolving transfers.
    for node in nodes.iter().rev() {
        let mut n = Raw {
            next,
            ..Raw::default()
        };
        match node {
            Node::Step {
                address,
                assignments,
            } => {
                n.kind = 1;
                n.pc = *address;
                n.token = token(tokens, format!("body:{assignments:?}"));
            }
            Node::Evaluate(e) => {
                n.kind = 2;
                n.token = token(tokens, format!("expr:{e:?}"));
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                n.kind = 3;
                n.token = token(tokens, format!("expr:{condition:?}"));
                n.first = sequence(taken, arena, tokens);
                n.other = sequence(not_taken, arena, tokens);
            }
            Node::Loop(body) => {
                n.kind = 4;
                n.first = sequence(body, arena, tokens);
            }
            Node::Break => n.kind = 5,
            Node::Continue => n.kind = 6,
            Node::BreakOuter { levels } => {
                n.kind = 5;
                n.level = *levels;
            }
            Node::ContinueOuter { levels } => {
                n.kind = 6;
                n.level = *levels;
            }
            Node::Return(e) => {
                n.kind = 7;
                n.token = token(tokens, format!("expr:{e:?}"));
            }
        }
        next = arena.len();
        arena.push(n);
    }
    next
}
fn main() {
    let mut exported = Vec::new();
    for case in cases::cases() {
        let verdict = match validate(&case.program, &case.body) {
            Ok(_) => "accepted",
            Err(ValidationError::ResourceLimit) => "resource_limit",
            Err(_) => "rejected",
        };
        let mut tokens = BTreeMap::new();
        let mut code = Vec::new();
        for instruction in case.program.instructions() {
            let body = token(&mut tokens, format!("body:{:?}", instruction.assignments));
            let (kind, expression, yes, no) = match &instruction.control {
                Control::Next => (0, 0, instruction.address + 1, 0),
                Control::Jump(next) => (0, 0, *next, 0),
                Control::Branch { condition, target } => (
                    1,
                    token(&mut tokens, format!("expr:{condition:?}")),
                    *target,
                    instruction.address + u64::from(instruction.size),
                ),
                Control::Return(e) => (2, token(&mut tokens, format!("expr:{e:?}")), 0, 0),
            };
            let may_fault = matches!(
                &instruction.control,
                Control::Branch {
                    condition: library::ir::Expr::Load { .. },
                    ..
                }
            );
            code.push(format!("{{\"pc\":{},\"body\":{body},\"kind\":{kind},\"expression\":{expression},\"yes\":{yes},\"no\":{no},\"faulty\":{may_fault}}}",instruction.address));
        }
        let mut arena = vec![Raw::default()];
        let root = sequence(&case.body, &mut arena, &mut tokens);
        exported.push(format!("{{\"name\":{:?},\"verdict\":{:?},\"early\":{},\"root\":{root},\"code\":[{}],\"arena\":[{}]}}",
            case.name,verdict,case.early_budget,code.join(","),arena.iter().map(Raw::json).collect::<Vec<_>>().join(",")));
    }
    println!(
        "{{\"schema\":\"nirvana-structured-events-trial-v1\",\"cases\":[{}]}}",
        exported.join(",")
    );
}
