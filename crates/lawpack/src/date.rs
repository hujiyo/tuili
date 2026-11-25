//! Calendar-date validation, shared by pack manifests, corpora, rule scopes and
//! the CLI.
//!
//! The pure logic lives in [`std_deduce_kernel::meta`] so the language layer can
//! validate a rule's `effective` / `repealed` clause without depending on this
//! crate. This module keeps the original `lawpack::validate_date` entry point, so
//! a manifest, a corpus, a rule clause and `--as-of` accept exactly the same
//! dates.

/// Check that `value` is a real `YYYY-MM-DD` calendar day.
///
/// See [`std_deduce_kernel::meta::validate_date`].
pub fn validate(field: &str, value: &str) -> Result<(), String> {
    std_deduce_kernel::meta::validate_date(field, value)
}
