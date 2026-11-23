//! The manifest data model and its format validation.

use std::collections::BTreeMap;
use std::fmt;

use serde::{Deserialize, Deserializer};

use crate::date;

/// Longest accepted pack or profile name, in bytes.
pub(crate) const MAX_NAME_LEN: usize = 128;
/// Longest accepted version string, in bytes.
pub(crate) const MAX_VERSION_LEN: usize = 64;
/// Longest accepted maintainer or reviewer text, in bytes.
pub(crate) const MAX_REVIEWER_LEN: usize = 128;

/// How much a legal pack is trusted.
///
/// The levels are ordered: `official` is the highest, `experimental` the
/// lowest. A manifest without `trust` is `community`, so a pack is never
/// treated as official by omission.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Trust {
    Experimental,
    Local,
    #[default]
    Community,
    Official,
}

impl fmt::Display for Trust {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            Trust::Experimental => "experimental",
            Trust::Local => "local",
            Trust::Community => "community",
            Trust::Official => "official",
        };
        f.write_str(label)
    }
}

/// Whether a pack release was reviewed by this project.
///
/// A manifest without `audit_status` is `unreviewed`, so a pack is never
/// treated as reviewed by omission. Only an `official` pack may be `reviewed`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AuditStatus {
    #[default]
    Unreviewed,
    Reviewed,
}

impl fmt::Display for AuditStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            AuditStatus::Unreviewed => "unreviewed",
            AuditStatus::Reviewed => "reviewed",
        };
        f.write_str(label)
    }
}

/// A parsed `lawpack.toml`.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    /// The pack's identity and scope.
    pub pack: PackInfo,
    /// Files belonging to the pack. They are recorded, not loaded or checked.
    #[serde(default)]
    pub files: Vec<PackFile>,
}

/// The `[pack]` table of a manifest.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PackInfo {
    /// Stable pack name: lowercase ASCII letters, digits, `.` and `-`; at most
    /// 128 bytes, and the first and last character are neither `.` nor `-`.
    pub name: String,
    /// Version: at least two dot-separated non-empty digit groups; at most 64
    /// bytes.
    pub version: String,
    /// Jurisdiction code: ASCII letters, digits and `-`.
    pub jurisdiction: String,
    /// Territory code: ASCII letters, digits and `-`.
    pub territory: String,
    /// Namespace owned by the pack, if declared.
    #[serde(default)]
    pub namespace: Option<String>,
    /// Optional link to the pack's article corpus, written as
    /// `<law-id>/<version>`. Only the format is validated; whether the corpus
    /// file exists is decided by the command that reads it.
    #[serde(default, deserialize_with = "empty_string_as_none")]
    pub corpus: Option<String>,
    /// Trust level; absence means `community`.
    #[serde(default)]
    pub trust: Trust,
    /// Groups or people that maintain this pack. Required for `official`.
    #[serde(default)]
    pub maintainers: Vec<String>,
    /// Review state; absence means `unreviewed`.
    #[serde(default)]
    pub audit_status: AuditStatus,
    /// Who reviewed this release. Only a `reviewed` pack may set it.
    #[serde(default, deserialize_with = "empty_string_as_none")]
    pub audited_by: Option<String>,
    /// Review date, `YYYY-MM-DD`. Only a `reviewed` pack may set it.
    #[serde(default, deserialize_with = "empty_string_as_none")]
    pub audited_at: Option<String>,
    /// First effective date, `YYYY-MM-DD`; an empty string means "not set".
    #[serde(default, deserialize_with = "empty_string_as_none")]
    pub effective_from: Option<String>,
    /// Last effective date, `YYYY-MM-DD`; an empty string means "not set".
    #[serde(default, deserialize_with = "empty_string_as_none")]
    pub effective_to: Option<String>,
    /// Human-readable summary.
    #[serde(default)]
    pub description: Option<String>,
}

/// One `[[files]]` entry.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PackFile {
    /// Path relative to the pack directory. This crate never opens it.
    #[serde(default)]
    pub path: Option<String>,
    /// Caller-defined kind label, for example `theory`.
    #[serde(default)]
    pub kind: Option<String>,
}

/// A manifest that is not valid TOML or fails format validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ManifestError {
    message: String,
}

impl ManifestError {
    fn new(message: impl Into<String>) -> Self {
        ManifestError {
            message: message.into(),
        }
    }

    /// The validation message.
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for ManifestError {}

impl Manifest {
    /// Parse and validate a manifest.
    ///
    /// Only format is checked: required fields, name/version/code character
    /// sets and lengths, dates that are real calendar days, and the agreement
    /// between `trust`, `audit_status` and the review fields — an `official`
    /// pack must be `reviewed` and carry a reviewer and a review date, while a
    /// non-official pack carries no review record. Whether a date range makes
    /// legal sense, whether listed files exist, and whether the content is
    /// correct are all left to later steps.
    pub fn parse(text: &str) -> Result<Manifest, ManifestError> {
        let manifest: Manifest = toml::from_str(text)
            .map_err(|error| ManifestError::new(format!("TOML 解析失败：{error}")))?;
        manifest.validate()?;
        Ok(manifest)
    }

    fn validate(&self) -> Result<(), ManifestError> {
        validate_name("pack.name", &self.pack.name).map_err(ManifestError::new)?;
        validate_version("pack.version", &self.pack.version).map_err(ManifestError::new)?;
        validate_code("pack.jurisdiction", &self.pack.jurisdiction)?;
        validate_code("pack.territory", &self.pack.territory)?;
        if let Some(corpus) = &self.pack.corpus {
            validate_corpus("pack.corpus", corpus).map_err(ManifestError::new)?;
        }
        if let Some(date) = &self.pack.effective_from {
            date::validate("pack.effective_from", date).map_err(ManifestError::new)?;
        }
        if let Some(date) = &self.pack.effective_to {
            date::validate("pack.effective_to", date).map_err(ManifestError::new)?;
        }
        self.validate_review()?;
        Ok(())
    }

    /// Validate the maintainer list and the review record.
    ///
    /// `official` and `reviewed` are two sides of one claim, so they must agree:
    /// an official pack states who maintains it, who reviewed it and when, and
    /// a non-official pack carries no review record at all. `reviewed` without
    /// both review fields, or either field without `reviewed`, is an error
    /// instead of a half-filled record.
    fn validate_review(&self) -> Result<(), ManifestError> {
        let pack = &self.pack;
        let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
        for (index, maintainer) in pack.maintainers.iter().enumerate() {
            validate_reviewer_text("pack.maintainers", Some(index + 1), maintainer)
                .map_err(ManifestError::new)?;
            if let Some(first) = seen.insert(maintainer, index + 1) {
                return Err(ManifestError::new(format!(
                    "pack.maintainers 第 {} 项与第 {first} 项重复：`{maintainer}`",
                    index + 1
                )));
            }
        }
        if let Some(audited_by) = &pack.audited_by {
            validate_reviewer_text("pack.audited_by", None, audited_by)
                .map_err(ManifestError::new)?;
        }
        if let Some(audited_at) = &pack.audited_at {
            date::validate("pack.audited_at", audited_at).map_err(ManifestError::new)?;
        }

        match (pack.trust, pack.audit_status) {
            (Trust::Official, AuditStatus::Reviewed) => {}
            (Trust::Official, AuditStatus::Unreviewed) => {
                return Err(ManifestError::new(
                    "pack.trust 是 official 时 pack.audit_status 必须是 `reviewed`",
                ));
            }
            (_, AuditStatus::Reviewed) => {
                return Err(ManifestError::new(format!(
                    "包 `{}` 的 pack.audit_status 是 `reviewed`，但只有 trust = \"official\" 的包能带审核记录",
                    pack.name
                )));
            }
            (_, AuditStatus::Unreviewed) => {}
        }
        if pack.trust == Trust::Official {
            if pack.maintainers.is_empty() {
                return Err(ManifestError::new(
                    "pack.trust 是 official 时 pack.maintainers 不能为空",
                ));
            }
            if pack.audited_by.is_none() {
                return Err(ManifestError::new(
                    "pack.trust 是 official 时 pack.audited_by 必须存在",
                ));
            }
            if pack.audited_at.is_none() {
                return Err(ManifestError::new(
                    "pack.trust 是 official 时 pack.audited_at 必须存在",
                ));
            }
        } else if pack.audited_by.is_some() || pack.audited_at.is_some() {
            return Err(ManifestError::new(format!(
                "包 `{}` 填写了 pack.audited_by/pack.audited_at，但只有 trust = \"official\" 且 audit_status = \"reviewed\" 的包能带审核记录",
                pack.name
            )));
        }
        Ok(())
    }
}

/// Validate one maintainer or reviewer string.
///
/// `index` is the 1-based position inside `pack.maintainers`; it is `None` for
/// the single-valued `pack.audited_by`. The text must be non-empty, at most
/// [`MAX_REVIEWER_LEN`] bytes, free of control characters (so it cannot forge
/// an output line) and free of leading or trailing whitespace.
fn validate_reviewer_text(field: &str, index: Option<usize>, value: &str) -> Result<(), String> {
    let label = match index {
        Some(index) => format!("{field} 第 {index} 项"),
        None => field.to_owned(),
    };
    if value.is_empty() {
        return Err(format!("{label}不能为空"));
    }
    if value.len() > MAX_REVIEWER_LEN {
        return Err(format!("{label}长度不能超过 {MAX_REVIEWER_LEN}"));
    }
    if value.chars().any(char::is_control) {
        return Err(format!("{label}含控制字符"));
    }
    if value.trim() != value {
        return Err(format!("{label}不能有首尾空白"));
    }
    Ok(())
}

/// Validate an identity name (`pack.name` or a profile name/alias).
pub(crate) fn validate_name(field: &str, name: &str) -> Result<(), String> {
    if name.is_empty() {
        return Err(format!("{field} 不能为空"));
    }
    if name.len() > MAX_NAME_LEN {
        return Err(format!("{field} 长度不能超过 {MAX_NAME_LEN}"));
    }
    let allowed = name
        .bytes()
        .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'.' || b == b'-');
    if !allowed {
        return Err(format!(
            "{field} `{name}` 含非法字符：只允许小写字母、数字、点和短横"
        ));
    }
    let bytes = name.as_bytes();
    let first = bytes[0];
    let last = bytes[bytes.len() - 1];
    if first == b'.' || first == b'-' || last == b'.' || last == b'-' {
        return Err(format!("{field} `{name}` 的首尾字符不能是点或短横"));
    }
    Ok(())
}

/// Validate a pack version or a profile version constraint.
pub(crate) fn validate_version(field: &str, version: &str) -> Result<(), String> {
    if version.is_empty() {
        return Err(format!("{field} 不能为空"));
    }
    if version.len() > MAX_VERSION_LEN {
        return Err(format!("{field} 长度不能超过 {MAX_VERSION_LEN}"));
    }
    let parts: Vec<&str> = version.split('.').collect();
    let valid = parts.len() >= 2
        && parts
            .iter()
            .all(|part| !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()));
    if !valid {
        return Err(format!(
            "{field} `{version}` 格式无效：必须是至少两段的数字和点，如 1.0"
        ));
    }
    Ok(())
}

/// Validate a manifest's optional corpus link.
///
/// The link is `<law-id>/<version>`: exactly one `/`, the law id uses the pack
/// name character set, and the version is non-empty and cannot escape the
/// corpus directory. The file's existence is checked only when a command reads
/// it.
fn validate_corpus(field: &str, value: &str) -> Result<(), String> {
    let Some((law, version)) = value.split_once('/') else {
        return Err(format!(
            "{field} `{value}` 格式无效：必须是 `<law-id>/<version>`"
        ));
    };
    validate_name(&format!("{field} 的 law-id"), law)?;
    if version.is_empty() {
        return Err(format!("{field} 的 version 不能为空"));
    }
    if version.trim() != version {
        return Err(format!("{field} 的 version `{version}` 不能有首尾空白"));
    }
    if version.contains('/') || version.contains('\\') || version.contains(':') {
        return Err(format!(
            "{field} 的 version `{version}` 不能包含路径分隔符或冒号"
        ));
    }
    if version.contains("..") {
        return Err(format!("{field} 的 version `{version}` 不能包含 `..`"));
    }
    Ok(())
}

/// Validate a jurisdiction or territory code.
///
/// The code must be non-empty and contain only ASCII letters, digits and `-`.
/// `pack.jurisdiction` and `pack.territory` use this rule, and so does the
/// CLI's `--jurisdiction` option, so both accept exactly the same codes.
/// `field` names the value in the error.
pub fn validate_jurisdiction_code(field: &str, value: &str) -> Result<(), String> {
    validate_code(field, value).map_err(|error| error.to_string())
}

fn validate_code(field: &str, value: &str) -> Result<(), ManifestError> {
    if value.is_empty() {
        return Err(ManifestError::new(format!("{field} 不能为空")));
    }
    let allowed = value
        .bytes()
        .all(|b| b.is_ascii_alphanumeric() || b == b'-');
    if !allowed {
        return Err(ManifestError::new(format!(
            "{field} `{value}` 含非法字符：只允许 ASCII 字母、数字和短横"
        )));
    }
    Ok(())
}

fn empty_string_as_none<'de, D>(deserializer: D) -> Result<Option<String>, D::Error>
where
    D: Deserializer<'de>,
{
    let value = Option::<String>::deserialize(deserializer)?;
    Ok(value.filter(|text| !text.is_empty()))
}
