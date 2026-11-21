//! Discovering legal packs in a directory.

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::Manifest;

/// The file that marks a directory as a legal pack.
pub const MANIFEST_FILE: &str = "lawpack.toml";

/// A legal pack found on disk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoadedPack {
    /// The pack's directory.
    pub dir: PathBuf,
    /// Its validated manifest.
    pub manifest: Manifest,
}

/// A directory or manifest that could not be read or validated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackError {
    path: PathBuf,
    message: String,
}

impl PackError {
    pub(crate) fn new(path: PathBuf, message: impl Into<String>) -> Self {
        PackError {
            path,
            message: message.into(),
        }
    }

    /// The path the error belongs to.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// The error message, without the path.
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for PackError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}：{}", self.path.display(), self.message)
    }
}

impl std::error::Error for PackError {}

/// Everything one scan of a root directory found.
#[derive(Debug, Default)]
pub struct Scan {
    /// Packs whose manifests parsed and validated.
    pub packs: Vec<LoadedPack>,
    /// Directories or manifests that could not be read or validated.
    pub errors: Vec<PackError>,
}

/// Scan `root` for legal packs.
///
/// Only direct child directories are considered. A child directory is a pack
/// only when it contains a `lawpack.toml`; directories without one are not
/// packs and are ignored. A manifest that cannot be read or validated is
/// reported in [`Scan::errors`], never skipped.
///
/// Symbolic links are refused: a link among the root's direct entries or at a
/// manifest path is an error, so a dangling link cannot make a bad pack
/// disappear. A pack directory that resolves outside `root` (a Windows
/// junction, for example) is also an error. Only paths that really are inside
/// `root` are read.
///
/// The only fatal condition is that `root` itself cannot be read; an empty
/// root is a successful scan with no packs, not an error.
pub fn scan(root: &Path) -> Result<Scan, PackError> {
    let canonical_root = fs::canonicalize(root).map_err(|error| {
        PackError::new(root.to_path_buf(), format!("无法读取法律包目录：{error}"))
    })?;
    let entries = fs::read_dir(root).map_err(|error| {
        PackError::new(root.to_path_buf(), format!("无法读取法律包目录：{error}"))
    })?;

    let mut errors = Vec::new();
    let mut dirs = Vec::new();
    for entry in entries {
        let entry = match entry {
            Ok(entry) => entry,
            Err(error) => {
                errors.push(PackError::new(
                    root.to_path_buf(),
                    format!("无法读取目录项：{error}"),
                ));
                continue;
            }
        };
        let path = entry.path();
        let file_type = match entry.file_type() {
            Ok(file_type) => file_type,
            Err(error) => {
                errors.push(PackError::new(path, format!("无法读取目录项类型：{error}")));
                continue;
            }
        };
        if file_type.is_symlink() {
            errors.push(PackError::new(
                path,
                "拒绝符号链接：法律包根目录的直接子项不能是符号链接",
            ));
            continue;
        }
        if file_type.is_dir() {
            dirs.push(path);
        }
    }
    // Directory order is platform-dependent; sort it so output is stable.
    dirs.sort();

    let mut packs = Vec::new();
    for dir in dirs {
        let canonical_dir = match fs::canonicalize(&dir) {
            Ok(path) => path,
            Err(error) => {
                errors.push(PackError::new(dir, format!("无法解析法律包目录：{error}")));
                continue;
            }
        };
        if !canonical_dir.starts_with(&canonical_root) {
            errors.push(PackError::new(
                dir,
                "拒绝越界链接：法律包目录解析后不在根目录内",
            ));
            continue;
        }

        let manifest_path = dir.join(MANIFEST_FILE);
        let metadata = match fs::symlink_metadata(&manifest_path) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => {
                errors.push(PackError::new(
                    manifest_path,
                    format!("无法读取法律包清单：{error}"),
                ));
                continue;
            }
        };
        if metadata.file_type().is_symlink() {
            errors.push(PackError::new(
                manifest_path,
                "拒绝符号链接：法律包清单不能是符号链接",
            ));
            continue;
        }
        if !metadata.is_file() {
            errors.push(PackError::new(manifest_path, "清单路径存在但不是普通文件"));
            continue;
        }
        let text = match fs::read_to_string(&manifest_path) {
            Ok(text) => text,
            Err(error) => {
                errors.push(PackError::new(
                    manifest_path,
                    format!("无法读取法律包清单：{error}"),
                ));
                continue;
            }
        };
        match Manifest::parse(&text) {
            Ok(manifest) => packs.push(LoadedPack { dir, manifest }),
            Err(error) => errors.push(PackError::new(manifest_path, error.to_string())),
        }
    }

    Ok(Scan { packs, errors })
}

/// Load every legal pack under `root`.
///
/// This is all-or-nothing: if any manifest is invalid, the whole load is an
/// error and the valid packs are not returned. Use [`scan`] when valid packs
/// and invalid manifests must both be reported, as the CLI does.
pub fn load(root: &Path) -> Result<Vec<LoadedPack>, Vec<PackError>> {
    match scan(root) {
        Ok(found) if found.errors.is_empty() => Ok(found.packs),
        Ok(found) => Err(found.errors),
        Err(error) => Err(vec![error]),
    }
}
