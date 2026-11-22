//! Lowercase hexadecimal encoding.

/// Encode bytes as lowercase hexadecimal without separators.
pub(crate) fn encode(bytes: &[u8]) -> String {
    let mut text = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        text.push_str(&format!("{byte:02x}"));
    }
    text
}
