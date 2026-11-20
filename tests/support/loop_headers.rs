//! Inspect generated C loop tests, excluding for initializers and updates.

pub fn conditions(code: &str) -> Vec<String> {
    let start = code.find("uint64_t nirvana_readable(").unwrap();
    let mut rest = &code[start..];
    let mut result = Vec::new();
    loop {
        let next = [("while (", false), ("for (", true)]
            .into_iter()
            .filter_map(|(token, is_for)| rest.find(token).map(|at| (at, token.len(), is_for)))
            .min_by_key(|v| v.0);
        let Some((at, length, is_for)) = next else {
            break;
        };
        let inside = &rest[at + length..];
        let mut depth = 1;
        let mut separators = Vec::new();
        let mut end = None;
        for (index, byte) in inside.bytes().enumerate() {
            match byte {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(index);
                        break;
                    }
                }
                b';' if depth == 1 => separators.push(index),
                _ => {}
            }
        }
        let end = end.expect("balanced generated loop header");
        let condition = if is_for {
            assert_eq!(separators.len(), 2);
            &inside[separators[0] + 1..separators[1]]
        } else {
            &inside[..end]
        };
        result.push(condition.trim().to_owned());
        rest = &inside[end + 1..];
    }
    result
}

pub fn assert_pure_conditions(code: &str) -> Vec<String> {
    let result = conditions(code);
    for condition in &result {
        assert!(
            !condition.contains("++") && !condition.contains("--"),
            "update in loop test: {condition}"
        );
        let bytes = condition.as_bytes();
        for (index, &byte) in bytes.iter().enumerate() {
            if byte == b'=' {
                let comparison = index > 0 && b"=!<>".contains(&bytes[index - 1])
                    || bytes.get(index + 1) == Some(&b'=');
                assert!(comparison, "assignment in loop test: {condition}");
            }
        }
    }
    result
}
