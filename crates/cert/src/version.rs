//! The certificate format version.

use std::fmt;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// The certificate format version this build reads and writes.
///
/// Version 3 made the `environment` identity mandatory after
/// `format_version`. Version 4 records how a conflict was adjudicated: a
/// defeated conflict carries its basis (a strict fact, or the declared
/// priority edges with their origins and sources), and an unresolved conflict
/// carries the reason. Version 5 records the fact identity of every
/// assumption and the reason for an unresolved claim that met a rule
/// conclusion. Version 6 records the enabled interpretations: a mandatory
/// `interpretations` table (empty when none were used) sorted by id, the
/// `interpretation_application` node, and the interpretation witness of a
/// conflict. Version 7 records the temporal/spatial applicability of every
/// rule application and gap candidate: the verdict, the reference dates and
/// places, the rule's declared scope, the session fallback values actually
/// used, the reason code and its explanation, plus each assumption's recorded
/// `occurred_at` / `occurred_in`. Version 8 records universal elimination: an
/// `axiom_instance` node naming the universal fact, the identity it is
/// asserted under, the closed value of every binding variable and the
/// substituted conclusion, plus the universal facts a gap goal could be
/// instantiated from and why they were refused. Version 9 records every
/// independent witness of each derived conclusion: the `alternatives` table
/// names a proposition and the nodes that derive it, in a stable order, with an
/// explicit truncation flag for the per-conclusion bound. Version 10 records
/// exact integers: a certificate expression may carry a `num` literal, a rule
/// application may carry the `computed` form of its conclusion (the rule's own
/// conclusion under the recorded bindings, before the kernel evaluated the
/// arithmetic), and the recorded conclusion is its evaluated value. The field
/// is required exactly when that substitution really computes something: a
/// step whose instance evaluates differently must record the pre-evaluation
/// form, so a missing arithmetic step cannot hide behind the recorded number.
/// Older certificates are
/// refused rather than read with guessed evidence: a proof that silently drops
/// an applicability judgement, an interpretation step, a universal
/// elimination step, an independent argument or the arithmetic step cannot be
/// checked.
pub const FORMAT_VERSION: u32 = 10;

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
