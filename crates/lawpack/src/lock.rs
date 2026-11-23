//! The registry lock file and pack content hashes.
//!
//! A registry is a directory of legal packs. [`build_lock`] hashes every pack
//! in it and returns the [`Lockfile`] that records the result; the CLI writes
//! that lock as `std.lock` next to the pack directories. [`verify_lock`] reads
//! the lock and checks the directory against it, so a changed, missing or
//! added pack is reported instead of being accepted.
//!
//! A pack hash covers every regular file below the pack directory, including
//! `lawpack.toml` and any nested `std.lock`; the registry lock itself lives
//! next to the pack directories, not inside them. Paths are relative to the
//! pack directory and always use `/` as the separator. In path order each file
//! contributes its path length as a little-endian `u64`, its path bytes, its
//! content length as a little-endian `u64`, and its content. The lengths make
//! the digest unambiguous even when a file contains a NUL byte. Before hashing,
//! `\r\n` in the content is replaced by `\n`: a Windows checkout and a Linux
//! checkout of the same files therefore hash the same, while any other byte
//! difference does not.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{hex, scan, LoadedPack, PackError};

/// The lock file name, written at the registry root.
pub const LOCK_FILE: &str = "std.lock";

/// The lock format version this crate writes and accepts.
pub const LOCK_VERSION: u32 = 1;

/// The parsed contents of a `std.lock`.
///
/// The file shape is:
///
/// ```toml
/// lock_version = 1
///
/// [[pack]]
/// name = "cn.constitution"
/// version = "0.1.0"
/// hash = "sha256:...."
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Lockfile {
    /// Lock format version; currently [`LOCK_VERSION`].
    pub lock_version: u32,
    /// One entry per pack, ordered by pack name in a lock this crate writes.
    ///
    /// An absent `pack` key means an empty registry, which is why it defaults
    /// to an empty list.
    #[serde(default)]
    pub pack: Vec<LockedPack>,
}

/// One `[[pack]]` entry: the pack's identity and the hash of its content.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LockedPack {
    /// Pack name as declared by the manifest.
    pub name: String,
    /// Manifest version the hash belongs to.
    pub version: String,
    /// `sha256:` followed by 64 lowercase hex digits.
    pub hash: String,
}

/// What a successful [`verify_lock`] established.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LockReport {
    /// How many packs the directory and the lock agree on.
    pub verified: usize,
}

impl Lockfile {
    /// Parse and validate a lock file's text.
    ///
    /// The text must be TOML with no unknown fields and a [`LOCK_VERSION`]
    /// this crate supports. Whether the recorded hashes match any directory
    /// is answered by [`verify_lock`], not here.
    pub fn parse(text: &str) -> Result<Lockfile, PackError> {
        parse_at(Path::new(LOCK_FILE), text)
    }

    /// Serialize to the lock file's TOML text.
    ///
    /// The value only contains an integer, strings and a list of tables, so
    /// serialization cannot fail.
    pub fn to_toml_string(&self) -> String {
        toml::to_string(self).expect("锁文件只含整数、字符串和字符串数组，序列化不会失败")
    }

    /// Read and parse a lock file.
    pub fn read(path: &Path) -> Result<Lockfile, PackError> {
        let text = fs::read_to_string(path).map_err(|error| {
            PackError::new(path.to_path_buf(), format!("无法读取锁文件：{error}"))
        })?;
        parse_at(path, &text)
    }

    /// Write the lock file's TOML text.
    ///
    /// A target that already exists as a symbolic link is refused instead of
    /// being followed, so writing cannot replace a file outside the registry.
    pub fn write(&self, path: &Path) -> Result<(), PackError> {
        match fs::symlink_metadata(path) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(PackError::new(
                    path.to_path_buf(),
                    "拒绝符号链接：std.lock 不能是符号链接",
                ));
            }
            Ok(_) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(PackError::new(
                    path.to_path_buf(),
                    format!("无法检查锁文件路径：{error}"),
                ));
            }
        }
        fs::write(path, self.to_toml_string())
            .map_err(|error| PackError::new(path.to_path_buf(), format!("无法写入锁文件：{error}")))
    }
}

fn parse_at(path: &Path, text: &str) -> Result<Lockfile, PackError> {
    let lockfile: Lockfile = toml::from_str(text)
        .map_err(|error| PackError::new(path.to_path_buf(), format!("锁文件解析失败：{error}")))?;
    if lockfile.lock_version != LOCK_VERSION {
        return Err(PackError::new(
            path.to_path_buf(),
            format!(
                "不支持的锁文件版本 {}：当前只支持 {LOCK_VERSION}",
                lockfile.lock_version
            ),
        ));
    }
    Ok(lockfile)
}

/// Hash the content of one pack directory.
///
/// Every regular file below `dir` is collected, including `lawpack.toml` and
/// any nested `std.lock`. Paths are relative to `dir` with `/` separators. In
/// path order each file contributes its path length (`u64` little-endian), its
/// path bytes, its content length (`u64` little-endian) and the content with
/// `\r\n` normalized to `\n`. The explicit lengths keep distinct file sets
/// distinct even when a file contains a NUL byte. Symbolic links and other
/// non-regular entries are errors: they are neither followed nor skipped. The
/// result is `sha256:` plus lowercase hex.
pub fn hash_pack(dir: &Path) -> Result<String, PackError> {
    let mut files: Vec<(String, PathBuf)> = Vec::new();
    collect_files(dir, dir, &mut files)?;
    files.sort_by(|(left, _), (right, _)| left.cmp(right));

    let mut hasher = Sha256::new();
    for (relative, path) in files {
        let bytes = fs::read(&path)
            .map_err(|error| PackError::new(path.clone(), format!("无法读取包文件：{error}")))?;
        let content = normalized(&bytes);
        hasher.update((relative.len() as u64).to_le_bytes());
        hasher.update(relative.as_bytes());
        hasher.update((content.len() as u64).to_le_bytes());
        hasher.update(&content);
    }
    Ok(format!("sha256:{}", hex::encode(&hasher.finalize())))
}

fn collect_files(
    root: &Path,
    dir: &Path,
    files: &mut Vec<(String, PathBuf)>,
) -> Result<(), PackError> {
    let entries = fs::read_dir(dir)
        .map_err(|error| PackError::new(dir.to_path_buf(), format!("无法读取包目录：{error}")))?;
    let mut paths = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|error| {
            PackError::new(dir.to_path_buf(), format!("无法读取目录项：{error}"))
        })?;
        paths.push(entry.path());
    }
    // Directory order is platform-dependent; sort it so the first error and
    // the collected order are stable.
    paths.sort();

    for path in paths {
        let metadata = fs::symlink_metadata(&path).map_err(|error| {
            PackError::new(path.clone(), format!("无法读取目录项类型：{error}"))
        })?;
        let file_type = metadata.file_type();
        if file_type.is_symlink() {
            return Err(PackError::new(
                path,
                "拒绝符号链接：法律包文件不能是符号链接",
            ));
        }
        if file_type.is_dir() {
            collect_files(root, &path, files)?;
            continue;
        }
        if !file_type.is_file() {
            return Err(PackError::new(
                path,
                "拒绝非普通文件：法律包只能包含普通文件和目录",
            ));
        }
        let relative = path.strip_prefix(root).map_err(|error| {
            PackError::new(path.clone(), format!("无法取得相对包目录的路径：{error}"))
        })?;
        files.push((slash_path(&path, relative)?, path));
    }
    Ok(())
}

/// Render a path relative to the pack directory with `/` separators.
fn slash_path(absolute: &Path, relative: &Path) -> Result<String, PackError> {
    let mut text = String::new();
    for component in relative.components() {
        let Component::Normal(part) = component else {
            return Err(PackError::new(
                absolute.to_path_buf(),
                "包内路径含非普通分量，无法计算哈希",
            ));
        };
        let part = part.to_str().ok_or_else(|| {
            PackError::new(
                absolute.to_path_buf(),
                "包内路径不是有效的 UTF-8，无法计算哈希",
            )
        })?;
        if !text.is_empty() {
            text.push('/');
        }
        text.push_str(part);
    }
    Ok(text)
}

/// Replace every `\r\n` with `\n`.
///
/// Shared with [`crate::corpus::hash_file`], so a single corpus file and a pack
/// containing it are both canonicalized the same way.
pub(crate) fn normalized(bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'\r' && bytes.get(i + 1) == Some(&b'\n') {
            out.push(b'\n');
            i += 2;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    out
}

/// Hash every pack under `root` and build the lock that describes them.
///
/// The packs are sorted by name. Nothing is written: the caller decides where
/// the lock goes. If any directory or manifest cannot be read, or any pack
/// contains a symbolic link or a file that cannot be read, every error is
/// returned and no lock is produced, so a partial lock cannot be written.
pub fn build_lock(root: &Path) -> Result<Lockfile, Vec<PackError>> {
    let found = match scan(root) {
        Ok(found) => found,
        Err(error) => return Err(vec![error]),
    };
    let mut errors = found.errors;
    let mut seen: BTreeMap<String, PathBuf> = BTreeMap::new();
    let mut packs = Vec::new();
    for pack in &found.packs {
        let name = pack.manifest.pack.name.clone();
        if let Some(first) = seen.insert(name.clone(), pack.dir.clone()) {
            errors.push(PackError::new(
                pack.dir.clone(),
                format!(
                    "包名 `{name}` 与 {} 重复，无法写入唯一的锁项",
                    first.display()
                ),
            ));
            continue;
        }
        match hash_pack(&pack.dir) {
            Ok(hash) => packs.push(LockedPack {
                name,
                version: pack.manifest.pack.version.clone(),
                hash,
            }),
            Err(error) => errors.push(error),
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    packs.sort_by(|left, right| left.name.cmp(&right.name));
    Ok(Lockfile {
        lock_version: LOCK_VERSION,
        pack: packs,
    })
}

/// Check `root` against `root/std.lock`.
///
/// The lock must exist, must be a regular file rather than a symbolic link, and
/// must be valid. Every pack in the directory is hashed again and must appear in
/// the lock with the same manifest version and the same hash; every locked pack
/// must exist. Symbolic links, unreadable directories, invalid manifests,
/// duplicate pack names, a version mismatch, a hash mismatch, a missing locked
/// pack and a directory pack that is not locked are all errors, and every one of
/// them is returned rather than the first. Pack order in the lock does not
/// matter.
pub fn verify_lock(root: &Path) -> Result<LockReport, Vec<PackError>> {
    let lock_path = root.join(LOCK_FILE);
    match fs::symlink_metadata(&lock_path) {
        Ok(metadata) if metadata.file_type().is_symlink() => {
            return Err(vec![PackError::new(
                lock_path,
                "拒绝符号链接：std.lock 不能是符号链接",
            )]);
        }
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Err(vec![PackError::new(lock_path, "没有 std.lock")]);
        }
        Err(error) => {
            return Err(vec![PackError::new(
                lock_path,
                format!("无法读取锁文件：{error}"),
            )]);
        }
    }
    let lockfile = Lockfile::read(&lock_path).map_err(|error| vec![error])?;

    let found = match scan(root) {
        Ok(found) => found,
        Err(error) => return Err(vec![error]),
    };
    let mut errors = found.errors;
    let mut by_name: BTreeMap<&str, &LoadedPack> = BTreeMap::new();
    for pack in &found.packs {
        let name = pack.manifest.pack.name.as_str();
        if let Some(first) = by_name.insert(name, pack) {
            errors.push(PackError::new(
                pack.dir.clone(),
                format!(
                    "包名 `{name}` 与 {} 重复，无法唯一对应锁项",
                    first.dir.display()
                ),
            ));
        }
    }

    let mut locked_names: BTreeSet<&str> = BTreeSet::new();
    let mut verified = 0;
    for entry in &lockfile.pack {
        if !locked_names.insert(entry.name.as_str()) {
            errors.push(PackError::new(
                lock_path.clone(),
                format!("std.lock 中包名 `{}` 重复", entry.name),
            ));
            continue;
        }
        let Some(pack) = by_name.get(entry.name.as_str()) else {
            errors.push(PackError::new(
                lock_path.clone(),
                format!("锁中的包 `{}` 在目录中不存在", entry.name),
            ));
            continue;
        };
        let version = &pack.manifest.pack.version;
        if version != &entry.version {
            errors.push(PackError::new(
                pack.dir.clone(),
                format!(
                    "包 `{}` 版本不符：锁中 {}，清单 {}",
                    entry.name, entry.version, version
                ),
            ));
        }
        match hash_pack(&pack.dir) {
            Ok(hash) if hash == entry.hash => verified += 1,
            Ok(hash) => errors.push(PackError::new(
                pack.dir.clone(),
                format!(
                    "包 `{}` 哈希不符：锁中 {}，实际 {}",
                    entry.name, entry.hash, hash
                ),
            )),
            Err(error) => errors.push(error),
        }
    }
    for pack in &found.packs {
        let name = pack.manifest.pack.name.as_str();
        if !locked_names.contains(name) {
            errors.push(PackError::new(
                pack.dir.clone(),
                format!("包 `{name}` 未锁定：目录中有该包，std.lock 中没有"),
            ));
        }
    }

    if errors.is_empty() {
        Ok(LockReport { verified })
    } else {
        Err(errors)
    }
}
