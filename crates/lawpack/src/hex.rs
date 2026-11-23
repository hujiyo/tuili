//! Lowercase hexadecimal encoding and the `sha256:` value format.

/// Encode bytes as lowercase hexadecimal without separators.
pub(crate) fn encode(bytes: &[u8]) -> String {
    let mut text = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        text.push_str(&format!("{byte:02x}"));
    }
    text
}

/// Is this `sha256:` followed by exactly 64 lowercase hex digits?
///
/// The corpus, the lock and the official whitelist all record hashes this way,
/// so they share one check.
pub(crate) fn is_sha256(value: &str) -> bool {
    let Some(digest) = value.strip_prefix("sha256:") else {
        return false;
    };
    digest.len() == 64
        && digest
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
