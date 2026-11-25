use std::fmt;

pub(super) struct Token<'a>(pub &'a [u64]);

fn digits(mut value: u64) -> usize {
    let mut count = 1;
    while value >= 10 {
        value /= 10;
        count += 1;
    }
    count
}

fn lengths(values: &[u64]) -> (usize, usize) {
    let dense = values
        .iter()
        .fold(2usize, |bytes, value| {
            bytes.saturating_add(digits(*value)).saturating_add(2)
        })
        .saturating_sub(if values.is_empty() { 0 } else { 2 });
    let mut rle = 10usize; // {"rle":[]}
    let mut rest = values;
    let mut first = true;
    while let Some(&value) = rest.first() {
        let count = rest.iter().take_while(|&&next| next == value).count();
        rle = rle
            .saturating_add(usize::from(!first))
            .saturating_add(3 + digits(count as u64) + digits(value));
        first = false;
        rest = &rest[count..];
    }
    (dense, rle)
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (dense, rle) = lengths(self.0);
        if rle >= dense {
            return write!(out, "{:?}", self.0);
        }
        out.write_str("{\"rle\":[")?;
        let mut rest = self.0;
        let mut first = true;
        while let Some(&value) = rest.first() {
            let count = rest.iter().take_while(|&&next| next == value).count();
            if !first {
                out.write_str(",")?;
            }
            write!(out, "[{count},{value}]")?;
            first = false;
            rest = &rest[count..];
        }
        out.write_str("]}")
    }
}

#[cfg(test)]
pub(super) fn token_lengths(values: &[u64]) -> (usize, usize) {
    lengths(values)
}
