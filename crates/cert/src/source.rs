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
    /// The cited text, for example the article's wording.
    pub text: String,
    /// Where the text lives, for example `刑法第二十条`.
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
}

impl Source {
    /// The citation in one line: `「<text><locator>」`, followed by
    /// `（<version>）` when a version is recorded.
    pub fn one_line(&self) -> String {
        let mut line = format!("「{}{}」", self.text, self.locator);
        if !self.version.is_empty() {
            line.push_str(&format!("（{}）", self.version));
        }
        line
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
        }
    }
}

impl From<Source> for SourceRef {
    fn from(source: Source) -> Self {
        SourceRef::from(&source)
    }
}
