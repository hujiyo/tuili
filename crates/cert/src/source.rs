//! Sources cited by assumptions and rule applications.

use serde::{Deserialize, Serialize};

use std_deduce_kernel::env::SourceRef;

/// A citation attached to an assumption or a rule application.
///
/// The fields mirror the kernel's [`SourceRef`] so a certificate preserves
/// everything the reasoner knows about provenance. A change to these fields
/// requires a new certificate format version.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Source {
    /// The file or law name, for example `中华人民共和国宪法`.
    pub text: String,
    /// The article or section within `text`, for example `第三十九条`.
    pub locator: String,
    /// The version of the cited instrument, if known.
    #[serde(default)]
    pub version: String,
    /// When the cited version took effect, if known.
    #[serde(default)]
    pub effective: Option<String>,
    /// Why the citation was formalised this way, when that is not obvious.
    #[serde(default)]
    pub note: String,
    /// The quoted wording of the provision.
    #[serde(default)]
    pub quote: String,
    /// Where the cited text can be retrieved.
    #[serde(default)]
    pub url: String,
    /// The jurisdiction the cited instrument belongs to.
    #[serde(default)]
    pub jurisdiction: String,
    /// When the citation was retrieved.
    #[serde(default)]
    pub retrieved_at: String,
    /// A content hash of the retrieved text, when recorded.
    #[serde(default)]
    pub hash: String,
}

impl Source {
    /// The citation in one line: `「<text><locator>」`, followed by
    /// `（<version>）` when a version is recorded. Delegating to the kernel
    /// keeps the certificate and the ledger rendering byte-for-byte equal.
    pub fn one_line(&self) -> String {
        SourceRef::from(self).one_line()
    }
}

impl From<&SourceRef> for Source {
    fn from(source: &SourceRef) -> Self {
        Source {
            text: source.text.clone(),
            locator: source.locator.clone(),
            version: source.version.clone(),
            effective: source.effective.clone(),
            note: source.note.clone(),
            quote: source.quote.clone(),
            url: source.url.clone(),
            jurisdiction: source.jurisdiction.clone(),
            retrieved_at: source.retrieved_at.clone(),
            hash: source.hash.clone(),
        }
    }
}

impl From<SourceRef> for Source {
    fn from(source: SourceRef) -> Self {
        Source::from(&source)
    }
}

impl From<&Source> for SourceRef {
    fn from(source: &Source) -> Self {
        SourceRef {
            text: source.text.clone(),
            locator: source.locator.clone(),
            version: source.version.clone(),
            effective: source.effective.clone(),
            note: source.note.clone(),
            quote: source.quote.clone(),
            url: source.url.clone(),
            jurisdiction: source.jurisdiction.clone(),
            retrieved_at: source.retrieved_at.clone(),
            hash: source.hash.clone(),
        }
    }
}

impl From<Source> for SourceRef {
    fn from(source: Source) -> Self {
        SourceRef::from(&source)
    }
}
