//! The shared lexer splits `5.e-05` incorrectly. Insert the mathematically
//! redundant fractional zero before lexing, without touching comments, strings,
//! identifiers, malformed exponents, or converting through binary floats.
use std::borrow::Cow;

pub(super) fn normalize(source: &str) -> Cow<'_, str> {
    let bytes = source.as_bytes();
    let mut i = 0;
    let mut insertions = Vec::new();
    while i < bytes.len() {
        if bytes[i..].starts_with(b"//") {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
        } else if bytes[i] == b'"' {
            i += 1;
            while i < bytes.len() {
                if bytes[i] == b'\\' {
                    i = (i + 2).min(bytes.len());
                } else if bytes[i] == b'"' {
                    i += 1;
                    break;
                } else {
                    i += 1;
                }
            }
        } else if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' || !bytes[i].is_ascii() {
            i += 1;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || !bytes[i].is_ascii())
            {
                i += 1;
            }
        } else if bytes[i].is_ascii_digit() {
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            if bytes.get(i) == Some(&b'.') {
                i += 1;
                if matches!(bytes.get(i), Some(b'e' | b'E')) {
                    let mut end = i + 1;
                    if matches!(bytes.get(end), Some(b'+' | b'-')) {
                        end += 1;
                    }
                    if bytes.get(end).is_some_and(u8::is_ascii_digit) {
                        insertions.push(i);
                    }
                }
            }
        } else {
            i += 1;
        }
    }
    if insertions.is_empty() {
        return Cow::Borrowed(source);
    }
    let mut result = String::with_capacity(source.len() + insertions.len());
    let mut start = 0;
    for offset in insertions {
        result.push_str(&source[start..offset]);
        result.push('0');
        start = offset;
    }
    result.push_str(&source[start..]);
    Cow::Owned(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn only_numeric_spelling_is_normalized() {
        assert_eq!(
            normalize("rz(5.e-05); // 5.e-05\n\"5.e-05\" x5.e-05 5.e- x"),
            "rz(5.0e-05); // 5.e-05\n\"5.e-05\" x5.e-05 5.e- x"
        );
    }
}
