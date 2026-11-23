//! Environment profiles: which packs a default legal environment contains.
//!
//! A profile lives in `<registry>/profiles/*.toml`. It names a set of packs
//! with version constraints and the minimum trust level the environment
//! requires. `scan_profiles` validates every file and every cross-file rule;
//! `select_default` and `select_named` then choose the environment to load.
//! A profile that is the automatic default must require `official` trust; a
//! profile selected by name may require a lower level.
//!
//! Profiles are not packs: they do not enter the content hash and `std.lock`
//! never records them. Validation is strict and complete — a misspelled file
//! name, an unknown field or a duplicate alias fails the whole scan instead of
//! silently producing "no default environment".

use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use serde::Deserialize;

use crate::manifest::{validate_name, validate_version};
use crate::{PackError, Trust};

/// Directory below the registry root that holds profiles.
pub const PROFILES_DIR: &str = "profiles";

/// A parsed and validated environment profile.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Profile {
    /// Profile name; selects this profile with `--profile <name>`.
    pub name: String,
    /// Alternative names for `--profile`.
    #[serde(default)]
    pub aliases: Vec<String>,
    /// Whether this profile is the automatic default. At most one may be true.
    #[serde(default)]
    pub default: bool,
    /// Human-readable description.
    #[serde(default)]
    pub description: Option<String>,
    /// Minimum trust level every pack in the environment must reach.
    ///
    /// A profile defaults to `official`, unlike a pack manifest.
    #[serde(default = "default_profile_trust")]
    pub trust: Trust,
    /// Packs the environment contains. At least one is required.
    #[serde(default)]
    pub packs: Vec<ProfilePack>,
}

/// One `[[packs]]` entry of a profile.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProfilePack {
    /// Pack name.
    pub name: String,
    /// Version constraint: dot-separated prefixes, compared as text.
    pub version: String,
}

fn default_profile_trust() -> Trust {
    Trust::Official
}

impl Profile {
    fn parse(text: &str) -> Result<Profile, String> {
        let profile: Profile =
            toml::from_str(text).map_err(|error| format!("TOML 解析失败：{error}"))?;
        profile.validate()?;
        Ok(profile)
    }

    fn validate(&self) -> Result<(), String> {
        validate_name("profile.name", &self.name)?;
        for alias in &self.aliases {
            validate_name("profile.alias", alias)
                .map_err(|error| format!("profile `{}`：{error}", self.name))?;
            if alias == &self.name {
                return Err(format!(
                    "profile `{}`：alias `{alias}` 与 profile 名相同",
                    self.name
                ));
            }
        }
        for (index, alias) in self.aliases.iter().enumerate() {
            if self.aliases[..index].contains(alias) {
                return Err(format!("profile `{}`：alias `{alias}` 重复", self.name));
            }
        }
        // The automatic default environment is what an ordinary load gets
        // without asking, so it may only require packs this project audited. A
        // profile selected explicitly may still declare a lower level.
        if self.default && self.trust != Trust::Official {
            return Err(format!(
                "profile `{}`：default = true 的 profile 必须要求 trust = \"official\"，当前是 `{}`",
                self.name, self.trust
            ));
        }
        if self.packs.is_empty() {
            return Err(format!("profile `{}` 至少要列出一个包", self.name));
        }
        let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
        for (index, pack) in self.packs.iter().enumerate() {
            validate_name("profile.packs.name", &pack.name)
                .map_err(|error| format!("profile `{}`：{error}", self.name))?;
            validate_version("profile.packs.version", &pack.version).map_err(|error| {
                format!("profile `{}` 的包 `{}`：{error}", self.name, pack.name)
            })?;
            if let Some(first) = seen.insert(&pack.name, index + 1) {
                return Err(format!(
                    "profile `{}` 的包 `{}` 在第 {} 条重复",
                    self.name, pack.name, first
                ));
            }
        }
        Ok(())
    }
}

/// Parse every profile below `registry_root/profiles`.
///
/// A missing `profiles/` directory means the registry has no profiles and is
/// not an error. Anything else is strict: a symlink, a non-directory, a file
/// that is not `.toml`, a subdirectory, bad TOML or a failed validation is
/// reported. Every error is returned, not only the first.
pub fn scan_profiles(registry_root: &Path) -> Result<Vec<Profile>, Vec<PackError>> {
    let dir = registry_root.join(PROFILES_DIR);
    let metadata = match fs::symlink_metadata(&dir) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => {
            return Err(vec![PackError::new(
                dir,
                format!("无法读取 profile 目录：{error}"),
            )]);
        }
    };
    if metadata.file_type().is_symlink() {
        return Err(vec![PackError::new(
            dir,
            "拒绝符号链接：profiles 不能是符号链接",
        )]);
    }
    if !metadata.is_dir() {
        return Err(vec![PackError::new(dir, "profiles 路径存在但不是普通目录")]);
    }

    let entries = fs::read_dir(&dir).map_err(|error| {
        vec![PackError::new(
            dir.clone(),
            format!("无法读取 profile 目录：{error}"),
        )]
    })?;
    let mut paths = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|error| {
            vec![PackError::new(
                dir.clone(),
                format!("无法读取目录项：{error}"),
            )]
        })?;
        paths.push(entry.path());
    }
    // Directory order is platform-dependent; sort it so errors and the
    // returned profile order are stable.
    paths.sort();

    let mut parsed: Vec<(PathBuf, Profile)> = Vec::new();
    let mut errors = Vec::new();
    for path in paths {
        let metadata = match fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(error) => {
                errors.push(PackError::new(
                    path,
                    format!("无法读取 profile 文件类型：{error}"),
                ));
                continue;
            }
        };
        let file_type = metadata.file_type();
        if file_type.is_symlink() {
            errors.push(PackError::new(
                path,
                "拒绝符号链接：profile 文件不能是符号链接",
            ));
            continue;
        }
        if file_type.is_dir() {
            errors.push(PackError::new(path, "profiles 里不能有子目录"));
            continue;
        }
        if !file_type.is_file() {
            errors.push(PackError::new(path, "profile 路径存在但不是普通文件"));
            continue;
        }
        let is_toml = path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.ends_with(".toml"));
        if !is_toml {
            errors.push(PackError::new(path, "profile 文件名必须以 .toml 结尾"));
            continue;
        }
        let text = match fs::read_to_string(&path) {
            Ok(text) => text,
            Err(error) => {
                errors.push(PackError::new(
                    path,
                    format!("无法读取 profile 文件：{error}"),
                ));
                continue;
            }
        };
        match Profile::parse(&text) {
            Ok(profile) => parsed.push((path, profile)),
            Err(error) => errors.push(PackError::new(path, error)),
        }
    }

    validate_unique(&parsed, &mut errors);
    if errors.is_empty() {
        Ok(parsed.into_iter().map(|(_, profile)| profile).collect())
    } else {
        Err(errors)
    }
}

/// Enforce uniqueness across every parsed profile.
fn validate_unique(parsed: &[(PathBuf, Profile)], errors: &mut Vec<PackError>) {
    let mut names: BTreeMap<&str, &Path> = BTreeMap::new();
    for (path, profile) in parsed {
        if let Some(first) = names.insert(&profile.name, path) {
            errors.push(PackError::new(
                path.clone(),
                format!("profile 名 `{}` 与 {} 重复", profile.name, first.display()),
            ));
        }
    }

    let defaults: Vec<&str> = parsed
        .iter()
        .filter(|(_, profile)| profile.default)
        .map(|(_, profile)| profile.name.as_str())
        .collect();
    if defaults.len() > 1 {
        for (path, profile) in parsed.iter().filter(|(_, profile)| profile.default) {
            errors.push(PackError::new(
                path.clone(),
                format!(
                    "profile `{}` 声明了 default = true，但只能有一个默认 profile（{}）",
                    profile.name,
                    defaults.join("、")
                ),
            ));
        }
    }

    let mut aliases: BTreeMap<&str, &Path> = BTreeMap::new();
    for (path, profile) in parsed {
        for alias in &profile.aliases {
            if let Some(name_path) = names.get(alias.as_str()) {
                errors.push(PackError::new(
                    path.clone(),
                    format!(
                        "profile `{}` 的 alias `{alias}` 与 {} 的 profile 名相同",
                        profile.name,
                        name_path.display()
                    ),
                ));
                continue;
            }
            if let Some(first) = aliases.insert(alias, path) {
                errors.push(PackError::new(
                    path.clone(),
                    format!(
                        "profile `{}` 的 alias `{alias}` 与 {} 重复",
                        profile.name,
                        first.display()
                    ),
                ));
            }
        }
    }
}

/// The automatic default profile, if any.
pub fn select_default(profiles: &[Profile]) -> Result<Option<&Profile>, String> {
    let defaults: Vec<&Profile> = profiles.iter().filter(|profile| profile.default).collect();
    match defaults.len() {
        0 => Ok(None),
        1 => Ok(Some(defaults[0])),
        _ => Err(format!(
            "多个 profile 声明了 default = true：{}",
            defaults
                .iter()
                .map(|profile| profile.name.as_str())
                .collect::<Vec<_>>()
                .join("、")
        )),
    }
}

/// Select a profile by exact name or alias.
pub fn select_named<'a>(profiles: &'a [Profile], query: &str) -> Result<&'a Profile, String> {
    if let Some(profile) = profiles
        .iter()
        .find(|profile| profile.name == query || profile.aliases.iter().any(|alias| alias == query))
    {
        return Ok(profile);
    }
    let available = if profiles.is_empty() {
        "（无）".to_owned()
    } else {
        profiles
            .iter()
            .map(|profile| {
                if profile.aliases.is_empty() {
                    profile.name.clone()
                } else {
                    format!("{}（别名 {}）", profile.name, profile.aliases.join("、"))
                }
            })
            .collect::<Vec<_>>()
            .join("；")
    };
    Err(format!(
        "找不到 profile `{query}`；可用 profile：{available}"
    ))
}

/// Whether `version` starts with every dot-separated segment of `constraint`.
///
/// Segments are compared as text, not as numbers: `0.1` matches `0.1.9` but
/// not `0.10.0`, and `0.1.0` matches neither `0.1.1` nor `0.1`.
pub fn version_matches(constraint: &str, version: &str) -> bool {
    if constraint.is_empty() {
        return false;
    }
    let mut constraint_segments = constraint.split('.');
    let mut version_segments = version.split('.');
    loop {
        match (constraint_segments.next(), version_segments.next()) {
            (None, _) => return true,
            (Some(constraint), Some(version)) if constraint == version => {}
            _ => return false,
        }
    }
}
