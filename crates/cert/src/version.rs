//! The certificate format version.

use std::fmt;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// The certificate format version this build reads and writes.
pub const FORMAT_VERSION: u32 = 1;

/// A certificate format version.
///
/// The value is serialized as a bare unsigned integer. Deserialization accepts
/// only [`FORMAT_VERSION`]: a certificate written for another version is
/// rejected rather than interpreted under the wrong rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FormatVersion(u32);

impl FormatVersion {
    /// The only version this build implements.
    pub const CURRENT: FormatVersion = FormatVersion(FORMAT_VERSION);

    /// The integer written into the `format_version` field.
    pub const fn get(self) -> u32 {
        self.0
    }
}

impl Default for FormatVersion {
    fn default() -> Self {
        Self::CURRENT
    }
}

impl fmt::Display for FormatVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Serialize for FormatVersion {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_u32(self.0)
    }
}

impl<'de> Deserialize<'de> for FormatVersion {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let version = u32::deserialize(deserializer)?;
        if version != FORMAT_VERSION {
            return Err(serde::de::Error::custom(format!(
                "unsupported certificate format version {version}; this build supports \
                 {FORMAT_VERSION}"
            )));
        }
        Ok(FormatVersion(version))
    }
}
