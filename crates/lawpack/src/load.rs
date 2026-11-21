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
    fn new(path: PathBuf, message: impl Into<String>) -> Self {
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
/// The only fatal condition is that `root` itself cannot be read; an empty
/// root is a successful scan with no packs, not an error.
pub fn scan(root: &Path) -> Result<Scan, PackError> {
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
        match fs::metadata(&path) {
            Ok(metadata) if metadata.is_dir() => dirs.push(path),
            Ok(_) => {}
            Err(error) => errors.push(PackError::new(path, format!("无法读取目录项：{error}"))),
        }
    }
    // Directory order is platform-dependent; sort it so output is stable.
    dirs.sort();

    let mut packs = Vec::new();
    for dir in dirs {
        let manifest_path = dir.join(MANIFEST_FILE);
        match fs::metadata(&manifest_path) {
            Ok(metadata) if metadata.is_file() => {}
            Ok(_) => {
                errors.push(PackError::new(manifest_path, "清单路径存在但不是普通文件"));
                continue;
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => {
                errors.push(PackError::new(
                    manifest_path,
                    format!("无法读取法律包清单：{error}"),
                ));
                continue;
            }
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
