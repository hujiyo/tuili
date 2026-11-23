//! The official-release whitelist.
//!
//! A registry may list the releases this project audited in
//! `<registry>/official.toml`:
//!
//! ```toml
//! [[pack]]
//! name = "cn.constitution"
//! version = "0.4.0"
//! hash = "sha256:...."
//! ```
//!
//! The file is the only source of the `official` trust level: a manifest can
//! claim `trust = "official"`, but the loader honours the claim only when the
//! whitelist lists exactly that name, version and content hash. The hash is
//! the same value `std.lock` records, so the lock binds the directory content
//! to the release the whitelist names.
//!
//! Reading is strict and complete: a symbolic link, a non-regular file, bad
//! TOML, an unknown field, a bad name/version/hash and a duplicate
//! `(name, version)` are all errors, and every one is returned. An absent file
//! is not an error by itself — it means the registry publishes no audited
//! release, and an `official` claim then cannot be verified. An empty file is
//! legal and means the same.

use std::fs;
use std::io;
use std::path::Path;

use serde::Deserialize;

use crate::hex::is_sha256;
use crate::manifest::{validate_name, validate_version};
use crate::PackError;

/// The whitelist file name, read at the registry root.
pub const OFFICIAL_FILE: &str = "official.toml";

/// The parsed contents of an `official.toml`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Whitelist {
    /// One entry per audited release, ordered by name in a file this project
    /// writes.
    #[serde(default)]
    pub pack: Vec<WhitelistPack>,
}

/// One `[[pack]]` entry: an audited release and the hash it shipped with.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WhitelistPack {
    /// Pack name, using the pack-name character set.
    pub name: String,
    /// The released version.
    pub version: String,
    /// `sha256:` followed by 64 lowercase hex digits, the same form
    /// `std.lock` uses.
    pub hash: String,
}

impl Whitelist {
    /// Whether the whitelist lists exactly this `(name, version, hash)`.
    ///
    /// All three must match: an audited name at another version or with other
    /// content is a different release and is not covered.
    pub fn covers(&self, name: &str, version: &str, hash: &str) -> bool {
        self.pack
            .iter()
            .any(|entry| entry.name == name && entry.version == version && entry.hash == hash)
    }

    /// How many releases the whitelist lists.
    pub fn len(&self) -> usize {
        self.pack.len()
    }

    /// Whether the whitelist lists no release.
    pub fn is_empty(&self) -> bool {
        self.pack.is_empty()
    }
}

/// Read and validate `<root>/official.toml`.
///
/// A missing file is `Ok(None)`; an empty file is `Ok(Some(empty whitelist))`,
/// because both mean that no release is audited. Every other problem is an
/// error pointing at the whitelist path, and every validation error found is
/// returned together.
pub fn read_whitelist(root: &Path) -> Result<Option<Whitelist>, Vec<PackError>> {
    let path = root.join(OFFICIAL_FILE);
    let metadata = match fs::symlink_metadata(&path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => {
            return Err(vec![PackError::new(
                path,
                format!("无法读取官方白名单：{error}"),
            )]);
        }
    };
    if metadata.file_type().is_symlink() {
        return Err(vec![PackError::new(
            path,
            "拒绝符号链接：official.toml 不能是符号链接",
        )]);
    }
    if !metadata.is_file() {
        return Err(vec![PackError::new(
            path,
            "官方白名单路径存在但不是普通文件",
        )]);
    }
    let text = fs::read_to_string(&path).map_err(|error| {
        vec![PackError::new(
            path.clone(),
            format!("无法读取官方白名单：{error}"),
        )]
    })?;
    let whitelist: Whitelist = toml::from_str(&text).map_err(|error| {
        vec![PackError::new(
            path.clone(),
            format!("官方白名单解析失败：{error}"),
        )]
    })?;
    validate(&path, &whitelist)?;
    Ok(Some(whitelist))
}

/// Validate every whitelist entry, collecting all errors.
fn validate(path: &Path, whitelist: &Whitelist) -> Result<(), Vec<PackError>> {
    let mut errors = Vec::new();
    let mut seen: std::collections::BTreeMap<(&str, &str), usize> =
        std::collections::BTreeMap::new();
    for (index, entry) in whitelist.pack.iter().enumerate() {
        let position = index + 1;
        if let Err(error) = validate_name("pack.name", &entry.name) {
            errors.push(PackError::new(
                path.to_path_buf(),
                format!("pack 第 {position} 条：{error}"),
            ));
        }
        if let Err(error) = validate_version("pack.version", &entry.version) {
            errors.push(PackError::new(
                path.to_path_buf(),
                format!("pack 第 {position} 条：{error}"),
            ));
        }
        if !is_sha256(&entry.hash) {
            errors.push(PackError::new(
                path.to_path_buf(),
                format!(
                    "pack 第 {position} 条的 hash `{}` 格式无效：必须是 sha256: 后接 64 位小写十六进制",
                    entry.hash
                ),
            ));
        }
        let key = (entry.name.as_str(), entry.version.as_str());
        if let Some(first) = seen.insert(key, position) {
            errors.push(PackError::new(
                path.to_path_buf(),
                format!(
                    "pack 第 {position} 条的 `{}@{}` 与第 {first} 条重复",
                    entry.name, entry.version
                ),
            ));
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}
