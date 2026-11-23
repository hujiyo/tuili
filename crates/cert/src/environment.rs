//! The environment identity recorded by a certificate.
//!
//! A certificate only means something relative to the legal environment that
//! produced it: which profile was active, which packs and versions were loaded,
//! under which trust level, and which corpus files bounded their citations.
//! [`EnvironmentRecord`] is that identity. [`EnvironmentIdentity`] wraps it so
//! the reasoner can produce certificates that deliberately record nothing
//! ([`EnvironmentIdentity::Unrecorded`]); such a certificate cannot be
//! serialized, because an exported certificate without an identity would claim
//! a portability it does not have.
//!
//! The format is strict: every field is required, and the optional fields
//! (`profile`, `as_of`, `jurisdiction`) are present as an explicit `null`.
//! A missing key is an error, never a silent `None`; [`ExplicitText`] is the
//! small wrapper that enforces it.
//!
//! Comparing a recorded identity with the current environment is a set
//! comparison: packs are keyed by name, corpora by `(law, version)`, and the
//! order of an array in JSON does not matter. [`EnvironmentRecord::differences`]
//! reports every difference in a stable order; it does not stop at the first.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use serde::de::Visitor;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// How much a legal pack was trusted when the certificate was produced.
///
/// The levels are ordered: `official` is the highest, `experimental` the
/// lowest. The certificate crate defines its own closed enum so it does not
/// depend on the pack registry; the CLI maps `lawpack::Trust` onto it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum TrustLevel {
    Experimental,
    Local,
    Community,
    Official,
}

impl TrustLevel {
    /// The lowercase wire name.
    pub const fn as_str(self) -> &'static str {
        match self {
            TrustLevel::Experimental => "experimental",
            TrustLevel::Local => "local",
            TrustLevel::Community => "community",
            TrustLevel::Official => "official",
        }
    }
}

impl fmt::Display for TrustLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A text field that is always present in JSON but may be `null`.
///
/// `Option<String>` would serialize as `null` too, but serde deserializes a
/// missing field of an optional type as `None`: its missing-field path calls
/// `deserialize_option`, which answers `visit_none`. For a format where `null`
/// is a statement ("no profile was active"), a missing key must be an error
/// instead. This wrapper therefore deserializes with `deserialize_any`: a
/// missing key reaches the deserializer's error path and reports `missing
/// field`, while an explicit `null` arrives as a unit and is accepted.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ExplicitText(Option<String>);

impl ExplicitText {
    /// The explicit `null` value.
    pub const fn none() -> Self {
        ExplicitText(None)
    }

    /// A present string value.
    pub fn some(value: impl Into<String>) -> Self {
        ExplicitText(Some(value.into()))
    }

    /// The text, if present.
    pub fn as_deref(&self) -> Option<&str> {
        self.0.as_deref()
    }

    /// Whether the value is the explicit `null`.
    pub fn is_none(&self) -> bool {
        self.0.is_none()
    }

    /// The underlying option.
    pub fn into_option(self) -> Option<String> {
        self.0
    }
}

impl From<Option<String>> for ExplicitText {
    fn from(value: Option<String>) -> Self {
        ExplicitText(value)
    }
}

impl Serialize for ExplicitText {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match &self.0 {
            Some(text) => serializer.serialize_some(text),
            None => serializer.serialize_none(),
        }
    }
}

impl<'de> Deserialize<'de> for ExplicitText {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct ExplicitTextVisitor;

        impl<'de> Visitor<'de> for ExplicitTextVisitor {
            type Value = ExplicitText;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("字符串或 null")
            }

            fn visit_none<E: serde::de::Error>(self) -> Result<Self::Value, E> {
                Ok(ExplicitText(None))
            }

            fn visit_unit<E: serde::de::Error>(self) -> Result<Self::Value, E> {
                Ok(ExplicitText(None))
            }

            fn visit_str<E: serde::de::Error>(self, value: &str) -> Result<Self::Value, E> {
                Ok(ExplicitText::some(value))
            }

            fn visit_string<E: serde::de::Error>(self, value: String) -> Result<Self::Value, E> {
                Ok(ExplicitText::some(value))
            }
        }

        // Deliberately not `deserialize_option`: serde's missing-field
        // deserializer answers that method with `visit_none`, which would turn
        // an absent key into a silent null. `deserialize_any` reports the
        // missing field instead.
        deserializer.deserialize_any(ExplicitTextVisitor)
    }
}

/// One pack as recorded in a certificate's environment identity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PackRecord {
    /// The pack's stable name.
    pub name: String,
    /// The manifest version that was loaded.
    pub version: String,
    /// The lock's content hash: `sha256:` plus 64 lowercase hex digits.
    pub hash: String,
    /// The trust level the pack was loaded under.
    pub trust: TrustLevel,
}

/// One corpus file as recorded in a certificate's environment identity.
///
/// `file_sha256` hashes the corpus file's bytes (with `\r\n` normalized to
/// `\n`), not any article text; it is the corpus's physical identity, like a
/// pack's lock hash. It is unrelated to the corpus's `text_sha256` provenance
/// field, which is never recomputed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CorpusRecord {
    /// The corpus's law id.
    pub law: String,
    /// The corpus's version.
    pub version: String,
    /// The corpus file hash: `sha256:` plus 64 lowercase hex digits.
    pub file_sha256: String,
}

/// The environment a certificate was produced in.
///
/// JSON field order is `profile`, `packs`, `corpora`, `as_of`, `jurisdiction`.
/// `packs` is written sorted by name and `corpora` by `(law, version)`, but
/// comparison is by set, so a reader may accept any order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EnvironmentRecord {
    /// The canonical profile name, or `null` when no default environment was
    /// active. An alias is never recorded: selecting `cn` records
    /// `cn.default`.
    pub profile: ExplicitText,
    /// Loaded packs, one entry per pack name.
    pub packs: Vec<PackRecord>,
    /// Corpus files the packs link, one entry per `(law, version)`.
    pub corpora: Vec<CorpusRecord>,
    /// The legal as-of date, `YYYY-MM-DD`, or `null` when unspecified.
    pub as_of: ExplicitText,
    /// The jurisdiction code, or `null` when unspecified.
    pub jurisdiction: ExplicitText,
}

impl EnvironmentRecord {
    /// An identity with no profile, no packs, no corpora and no dates.
    ///
    /// This is the identity of a session that never prepared a default
    /// environment and loaded no registry pack: an explicit "nothing was
    /// active" that still round-trips through JSON.
    pub fn empty() -> Self {
        EnvironmentRecord {
            profile: ExplicitText::none(),
            packs: Vec::new(),
            corpora: Vec::new(),
            as_of: ExplicitText::none(),
            jurisdiction: ExplicitText::none(),
        }
    }

    /// Validate the record's invariants.
    ///
    /// Rejects duplicate pack names, duplicate `(law, version)` corpora, empty
    /// names/versions, malformed `sha256` values, a profile that is present but
    /// empty, an `as_of` that is not a real `YYYY-MM-DD` date and a
    /// `jurisdiction` that is not non-empty ASCII letters, digits and `-`.
    /// An invalid trust level cannot occur here: [`TrustLevel`] is a closed
    /// enum and its deserializer rejects unknown values.
    pub fn validate(&self) -> Result<(), String> {
        if let Some(profile) = self.profile.as_deref() {
            if profile.is_empty() {
                return Err("environment profile must not be empty".to_owned());
            }
        }
        if let Some(as_of) = self.as_of.as_deref() {
            if !is_date(as_of) {
                return Err(format!(
                    "environment as_of `{as_of}` is not a real YYYY-MM-DD date"
                ));
            }
        }
        if let Some(jurisdiction) = self.jurisdiction.as_deref() {
            let valid = !jurisdiction.is_empty()
                && jurisdiction
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-');
            if !valid {
                return Err(format!(
                    "environment jurisdiction `{jurisdiction}` must be non-empty ASCII letters, digits or `-`"
                ));
            }
        }

        let mut pack_names = BTreeSet::new();
        for pack in &self.packs {
            if pack.name.is_empty() {
                return Err("environment pack name must not be empty".to_owned());
            }
            if pack.version.is_empty() {
                return Err(format!(
                    "environment pack `{}` version must not be empty",
                    pack.name
                ));
            }
            if !is_sha256(&pack.hash) {
                return Err(format!(
                    "environment pack `{}` hash must be `sha256:` followed by 64 lowercase hex digits",
                    pack.name
                ));
            }
            if !pack_names.insert(pack.name.as_str()) {
                return Err(format!(
                    "environment pack name `{}` is duplicated",
                    pack.name
                ));
            }
        }

        let mut corpora = BTreeSet::new();
        for corpus in &self.corpora {
            if corpus.law.is_empty() {
                return Err("environment corpus law must not be empty".to_owned());
            }
            if corpus.version.is_empty() {
                return Err(format!(
                    "environment corpus `{}` version must not be empty",
                    corpus.law
                ));
            }
            if !is_sha256(&corpus.file_sha256) {
                return Err(format!(
                    "environment corpus `{}@{}` file_sha256 must be `sha256:` followed by 64 lowercase hex digits",
                    corpus.law, corpus.version
                ));
            }
            if !corpora.insert((corpus.law.as_str(), corpus.version.as_str())) {
                return Err(format!(
                    "environment corpus `{}@{}` is duplicated",
                    corpus.law, corpus.version
                ));
            }
        }
        Ok(())
    }

    /// Every difference between this recorded identity and `current`.
    ///
    /// `self` is the certificate's record and `current` is the environment the
    /// certificate is being checked against. Profile, `as_of` and jurisdiction
    /// are compared exactly, including `null`. Packs are compared by name:
    /// a name only on one side is reported as a whole missing/extra pack, a
    /// version difference suppresses the hash and trust differences for that
    /// pack, and otherwise hash and trust are reported separately. Corpora are
    /// compared by `(law, version)` and their file hash.
    ///
    /// All differences are returned in a stable order: profile, `as_of`,
    /// jurisdiction, then packs by name and corpora by `(law, version)`.
    pub fn differences(&self, current: &EnvironmentRecord) -> Vec<EnvironmentDifference> {
        let mut differences = Vec::new();

        if self.profile != current.profile {
            differences.push(EnvironmentDifference::Profile {
                recorded: self.profile.clone().into_option(),
                current: current.profile.clone().into_option(),
            });
        }
        if self.as_of != current.as_of {
            differences.push(EnvironmentDifference::AsOf {
                recorded: self.as_of.clone().into_option(),
                current: current.as_of.clone().into_option(),
            });
        }
        if self.jurisdiction != current.jurisdiction {
            differences.push(EnvironmentDifference::Jurisdiction {
                recorded: self.jurisdiction.clone().into_option(),
                current: current.jurisdiction.clone().into_option(),
            });
        }

        let recorded: BTreeMap<&str, &PackRecord> = self
            .packs
            .iter()
            .map(|pack| (pack.name.as_str(), pack))
            .collect();
        let active: BTreeMap<&str, &PackRecord> = current
            .packs
            .iter()
            .map(|pack| (pack.name.as_str(), pack))
            .collect();
        let names: BTreeSet<&str> = recorded.keys().chain(active.keys()).copied().collect();
        for name in names {
            match (recorded.get(name), active.get(name)) {
                (Some(one), None) => {
                    differences.push(EnvironmentDifference::MissingPack((*one).clone()));
                }
                (None, Some(other)) => {
                    differences.push(EnvironmentDifference::ExtraPack((*other).clone()));
                }
                (Some(one), Some(other)) => {
                    if one.version != other.version {
                        differences.push(EnvironmentDifference::PackVersion {
                            name: name.to_owned(),
                            recorded: one.version.clone(),
                            current: other.version.clone(),
                        });
                        continue;
                    }
                    if one.hash != other.hash {
                        differences.push(EnvironmentDifference::PackHash {
                            name: name.to_owned(),
                            version: one.version.clone(),
                            recorded: one.hash.clone(),
                            current: other.hash.clone(),
                        });
                    }
                    if one.trust != other.trust {
                        differences.push(EnvironmentDifference::PackTrust {
                            name: name.to_owned(),
                            version: one.version.clone(),
                            recorded: one.trust,
                            current: other.trust,
                        });
                    }
                }
                (None, None) => {}
            }
        }

        let recorded: BTreeMap<(&str, &str), &CorpusRecord> = self
            .corpora
            .iter()
            .map(|corpus| ((corpus.law.as_str(), corpus.version.as_str()), corpus))
            .collect();
        let active: BTreeMap<(&str, &str), &CorpusRecord> = current
            .corpora
            .iter()
            .map(|corpus| ((corpus.law.as_str(), corpus.version.as_str()), corpus))
            .collect();
        let keys: BTreeSet<(&str, &str)> = recorded.keys().chain(active.keys()).copied().collect();
        for key in keys {
            match (recorded.get(&key), active.get(&key)) {
                (Some(one), None) => {
                    differences.push(EnvironmentDifference::MissingCorpus((*one).clone()));
                }
                (None, Some(other)) => {
                    differences.push(EnvironmentDifference::ExtraCorpus((*other).clone()));
                }
                (Some(one), Some(other)) => {
                    if one.file_sha256 != other.file_sha256 {
                        differences.push(EnvironmentDifference::CorpusHash {
                            law: key.0.to_owned(),
                            version: key.1.to_owned(),
                            recorded: one.file_sha256.clone(),
                            current: other.file_sha256.clone(),
                        });
                    }
                }
                (None, None) => {}
            }
        }

        differences
    }
}

/// Which part of a recorded environment differs from the current one.
///
/// The CLI renders these; the strings are raw recorded/current values, so the
/// renderer escapes them before printing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentDifference {
    /// The active profile name differs, including recorded/current `null`.
    Profile {
        recorded: Option<String>,
        current: Option<String>,
    },
    /// The recorded `as_of` date differs, including `null`.
    AsOf {
        recorded: Option<String>,
        current: Option<String>,
    },
    /// The recorded jurisdiction differs, including `null`.
    Jurisdiction {
        recorded: Option<String>,
        current: Option<String>,
    },
    /// The certificate recorded a pack the current environment does not have.
    MissingPack(PackRecord),
    /// The current environment has a pack the certificate did not record.
    ExtraPack(PackRecord),
    /// The pack exists on both sides but its version differs.
    PackVersion {
        name: String,
        recorded: String,
        current: String,
    },
    /// The pack exists on both sides with one version but another content hash.
    PackHash {
        name: String,
        version: String,
        recorded: String,
        current: String,
    },
    /// The pack exists on both sides with one hash but another trust level.
    PackTrust {
        name: String,
        version: String,
        recorded: TrustLevel,
        current: TrustLevel,
    },
    /// The certificate recorded a corpus the current environment does not have.
    MissingCorpus(CorpusRecord),
    /// The current environment has a corpus the certificate did not record.
    ExtraCorpus(CorpusRecord),
    /// The corpus file content hash differs.
    CorpusHash {
        law: String,
        version: String,
        recorded: String,
        current: String,
    },
}

/// An environment identity as a certificate carries it.
///
/// A [`Recorded`](EnvironmentIdentity::Recorded) identity serializes as an
/// inline JSON object and is the only form a certificate can be exported in.
/// [`Unrecorded`](EnvironmentIdentity::Unrecorded) exists only in memory: the
/// reasoner produces it, and serialization fails until the CLI stamps a real
/// identity with [`Certificate::with_environment`](crate::Certificate::with_environment).
/// Deserialization accepts only an object; `null` and strings are rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentIdentity {
    Recorded(EnvironmentRecord),
    Unrecorded,
}

impl EnvironmentIdentity {
    /// An empty recorded environment: no profile, packs, corpora or dates.
    ///
    /// This is a real identity, not an "unrecorded" marker: it says the
    /// session had no default environment and no registry pack. It serializes
    /// and compares like any other record.
    pub fn none() -> Self {
        EnvironmentIdentity::Recorded(EnvironmentRecord::empty())
    }

    /// Wrap a validated environment record.
    pub fn recorded(record: EnvironmentRecord) -> Self {
        EnvironmentIdentity::Recorded(record)
    }

    /// The record, if one was recorded.
    pub fn as_recorded(&self) -> Option<&EnvironmentRecord> {
        match self {
            EnvironmentIdentity::Recorded(record) => Some(record),
            EnvironmentIdentity::Unrecorded => None,
        }
    }

    /// Validate the recorded environment; `Unrecorded` is always an error.
    pub fn validate(&self) -> Result<(), String> {
        match self {
            EnvironmentIdentity::Recorded(record) => record.validate(),
            EnvironmentIdentity::Unrecorded => {
                Err("certificate environment identity is not recorded".to_owned())
            }
        }
    }

    /// Compare the recorded identity with `current`.
    ///
    /// An unrecorded identity cannot be compared: a certificate that records
    /// nothing cannot be shown to belong to any environment, so the caller must
    /// treat it as a failure, not as an empty match.
    pub fn differences(
        &self,
        current: &EnvironmentRecord,
    ) -> Result<Vec<EnvironmentDifference>, UnrecordedEnvironment> {
        match self {
            EnvironmentIdentity::Recorded(record) => Ok(record.differences(current)),
            EnvironmentIdentity::Unrecorded => Err(UnrecordedEnvironment),
        }
    }
}

impl From<EnvironmentRecord> for EnvironmentIdentity {
    fn from(record: EnvironmentRecord) -> Self {
        EnvironmentIdentity::Recorded(record)
    }
}

impl Serialize for EnvironmentIdentity {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            EnvironmentIdentity::Recorded(record) => record.serialize(serializer),
            EnvironmentIdentity::Unrecorded => Err(serde::ser::Error::custom(
                "certificate environment identity is not recorded and cannot be serialized",
            )),
        }
    }
}

impl<'de> Deserialize<'de> for EnvironmentIdentity {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        EnvironmentRecord::deserialize(deserializer).map(EnvironmentIdentity::Recorded)
    }
}

/// The certificate carries no environment identity to compare. Always an
/// error: treating it as an empty environment would let an unrecorded
/// certificate pass any check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnrecordedEnvironment;

impl fmt::Display for UnrecordedEnvironment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("证书没有记录环境身份")
    }
}

impl std::error::Error for UnrecordedEnvironment {}

/// Is this `sha256:` followed by exactly 64 lowercase hex digits?
fn is_sha256(value: &str) -> bool {
    let Some(digest) = value.strip_prefix("sha256:") else {
        return false;
    };
    digest.len() == 64
        && digest
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// Is this a real `YYYY-MM-DD` calendar day?
fn is_date(value: &str) -> bool {
    let bytes = value.as_bytes();
    let shaped = bytes.len() == 10
        && bytes[4] == b'-'
        && bytes[7] == b'-'
        && bytes[..4].iter().all(u8::is_ascii_digit)
        && bytes[5..7].iter().all(u8::is_ascii_digit)
        && bytes[8..10].iter().all(u8::is_ascii_digit);
    if !shaped {
        return false;
    }
    let year = decimal(&bytes[..4]);
    let month = decimal(&bytes[5..7]);
    let max_day = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap_year(year) => 29,
        2 => 28,
        _ => return false,
    };
    (1..=max_day).contains(&decimal(&bytes[8..10]))
}

fn leap_year(year: u32) -> bool {
    year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400))
}

fn decimal(bytes: &[u8]) -> u32 {
    bytes
        .iter()
        .fold(0, |value, byte| value * 10 + u32::from(byte - b'0'))
}
