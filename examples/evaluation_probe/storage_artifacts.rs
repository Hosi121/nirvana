//! Bounded artifact text and JSON formatting for storage stage records.
use std::fmt::{self, Write};

pub(super) const MAX_BYTES: usize = 16 * 1024 * 1024;

pub(super) struct Text(pub(super) String);
impl Write for Text {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        if self
            .0
            .len()
            .checked_add(text.len())
            .is_none_or(|n| n > MAX_BYTES)
        {
            return Err(fmt::Error);
        }
        self.0.push_str(text);
        Ok(())
    }
}

pub(super) fn quote(text: &str) -> String {
    let mut result = String::from("\"");
    for character in text.chars() {
        match character {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c if c < ' ' => write!(result, "\\u{:04x}", c as u32).unwrap(),
            c => result.push(c),
        }
    }
    result.push('"');
    result
}

pub(super) struct Failure(pub(super) &'static str, pub(super) String);
impl Failure {
    pub(super) fn unavailable(reason: impl Into<String>) -> Self {
        Self("unavailable", reason.into())
    }
    pub(super) fn invalid(reason: &str) -> Self {
        Self("rejected", reason.into())
    }
}
