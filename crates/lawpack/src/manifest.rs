//! The manifest data model and its format validation.

use std::fmt;

use serde::{Deserialize, Deserializer};

/// Longest accepted pack name, in bytes.
const MAX_NAME_LEN: usize = 128;
/// Longest accepted version string, in bytes.
const MAX_VERSION_LEN: usize = 64;

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
    /// sets and lengths, and dates that are real calendar days. Whether a date
    /// range makes legal sense, whether listed files exist, and whether the
    /// content is correct are all left to later steps.
    pub fn parse(text: &str) -> Result<Manifest, ManifestError> {
        let manifest: Manifest = toml::from_str(text)
            .map_err(|error| ManifestError::new(format!("TOML 解析失败：{error}")))?;
        manifest.validate()?;
        Ok(manifest)
    }

    fn validate(&self) -> Result<(), ManifestError> {
        validate_name(&self.pack.name)?;
        validate_version(&self.pack.version)?;
        validate_code("pack.jurisdiction", &self.pack.jurisdiction)?;
        validate_code("pack.territory", &self.pack.territory)?;
        if let Some(date) = &self.pack.effective_from {
            validate_date("pack.effective_from", date)?;
        }
        if let Some(date) = &self.pack.effective_to {
            validate_date("pack.effective_to", date)?;
        }
        Ok(())
    }
}

fn validate_name(name: &str) -> Result<(), ManifestError> {
    if name.is_empty() {
        return Err(ManifestError::new("pack.name 不能为空"));
    }
    if name.len() > MAX_NAME_LEN {
        return Err(ManifestError::new(format!(
            "pack.name 长度不能超过 {MAX_NAME_LEN}"
        )));
    }
    let allowed = name
        .bytes()
        .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'.' || b == b'-');
    if !allowed {
        return Err(ManifestError::new(format!(
            "pack.name `{name}` 含非法字符：只允许小写字母、数字、点和短横"
        )));
    }
    let bytes = name.as_bytes();
    let first = bytes[0];
    let last = bytes[bytes.len() - 1];
    if first == b'.' || first == b'-' || last == b'.' || last == b'-' {
        return Err(ManifestError::new(format!(
            "pack.name `{name}` 的首尾字符不能是点或短横"
        )));
    }
    Ok(())
}

fn validate_version(version: &str) -> Result<(), ManifestError> {
    if version.is_empty() {
        return Err(ManifestError::new("pack.version 不能为空"));
    }
    if version.len() > MAX_VERSION_LEN {
        return Err(ManifestError::new(format!(
            "pack.version 长度不能超过 {MAX_VERSION_LEN}"
        )));
    }
    let parts: Vec<&str> = version.split('.').collect();
    let valid = parts.len() >= 2
        && parts
            .iter()
            .all(|part| !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()));
    if !valid {
        return Err(ManifestError::new(format!(
            "pack.version `{version}` 格式无效：必须是至少两段的数字和点，如 1.0"
        )));
    }
    Ok(())
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

fn validate_date(field: &str, value: &str) -> Result<(), ManifestError> {
    let bytes = value.as_bytes();
    let shaped = bytes.len() == 10
        && bytes[4] == b'-'
        && bytes[7] == b'-'
        && digits(&bytes[0..4])
        && digits(&bytes[5..7])
        && digits(&bytes[8..10]);
    if !shaped {
        return Err(ManifestError::new(format!(
            "{field} `{value}` 不是 YYYY-MM-DD 日期"
        )));
    }
    let year = decimal(&bytes[0..4]);
    let month = decimal(&bytes[5..7]);
    let max_day = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap_year(year) => 29,
        2 => 28,
        _ => {
            return Err(ManifestError::new(format!(
                "{field} `{value}` 的月份 {month} 超出 1..12"
            )));
        }
    };
    let day = decimal(&bytes[8..10]);
    if !(1..=max_day).contains(&day) {
        return Err(ManifestError::new(format!(
            "{field} `{value}` 的日期 {day} 超出 1..{max_day}"
        )));
    }
    Ok(())
}

fn leap_year(year: u32) -> bool {
    year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400))
}

fn digits(bytes: &[u8]) -> bool {
    bytes.iter().all(|b| b.is_ascii_digit())
}

fn decimal(bytes: &[u8]) -> u32 {
    bytes
        .iter()
        .fold(0, |value, b| value * 10 + u32::from(b - b'0'))
}

fn empty_string_as_none<'de, D>(deserializer: D) -> Result<Option<String>, D::Error>
where
    D: Deserializer<'de>,
{
    let value = Option::<String>::deserialize(deserializer)?;
    Ok(value.filter(|text| !text.is_empty()))
}
