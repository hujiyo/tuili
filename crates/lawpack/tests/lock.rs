//! Tests for the registry lock file and pack content hashes.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use sha2::{Digest, Sha256};
use std_deduce_lawpack::{build_lock, hash_pack, verify_lock, LockedPack, Lockfile, LOCK_FILE};

fn manifest(name: &str, version: &str) -> String {
    format!(
        "[pack]\nname = \"{name}\"\nversion = \"{version}\"\njurisdiction = \"CN\"\nterritory = \"CN\"\n"
    )
}

fn lockfile(packs: &[(&str, &str, &str)]) -> Lockfile {
    Lockfile {
        lock_version: 1,
        pack: packs
            .iter()
            .map(|(name, version, hash)| LockedPack {
                name: (*name).to_owned(),
                version: (*version).to_owned(),
                hash: (*hash).to_owned(),
            })
            .collect(),
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[test]
fn lockfile_has_the_documented_toml_shape() {
    let text = lockfile(&[("cn.constitution", "0.1.0", "sha256:ab")]).to_toml_string();
    assert_eq!(
        text,
        "lock_version = 1\n\n[[pack]]\nname = \"cn.constitution\"\nversion = \"0.1.0\"\nhash = \"sha256:ab\"\n"
    );
}

#[test]
fn lockfile_round_trips_through_toml() {
    let original = lockfile(&[
        ("cn.civil-code", "2.0", "sha256:def"),
        ("cn.constitution", "0.1.0", "sha256:abc"),
    ]);
    let text = original.to_toml_string();
    assert_eq!(Lockfile::parse(&text).expect("the lock is valid"), original);
}

#[test]
fn lockfile_round_trips_through_a_file() {
    let temp = TempDir::new("lock-file");
    let path = temp.path().join(LOCK_FILE);
    let original = lockfile(&[("cn.constitution", "0.1.0", "sha256:abc")]);
    original.write(&path).expect("the lock is writable");
    assert_eq!(
        Lockfile::read(&path).expect("the lock is readable"),
        original
    );
}

#[test]
fn write_refuses_a_symlinked_target() {
    let temp = TempDir::new("write-link");
    let target = temp.path().join("outside-lock");
    fs::write(&target, "unchanged").unwrap();
    let link = temp.path().join(LOCK_FILE);
    if !create_file_symlink(&target, &link) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }

    let error = lockfile(&[("cn.constitution", "0.1.0", "sha256:abc")])
        .write(&link)
        .unwrap_err();
    assert_eq!(error.path(), link.as_path());
    assert!(error.message().contains("符号链接"), "{error}");
    assert_eq!(fs::read_to_string(&target).unwrap(), "unchanged");
}

#[test]
fn an_unsupported_lock_version_is_rejected() {
    let error = Lockfile::parse("lock_version = 2\n").unwrap_err();
    assert!(error.message().contains("版本 2"), "{error}");
    assert!(error.message().contains("当前只支持 1"), "{error}");
}

#[test]
fn unknown_lock_fields_are_rejected() {
    let error = Lockfile::parse("lock_version = 1\nextra = true\n").unwrap_err();
    assert!(error.message().contains("锁文件解析失败"), "{error}");
}

#[test]
fn hash_is_stable_and_shaped() {
    let temp = TempDir::new("stable");
    let dir = temp.pack("cn.constitution", &manifest("cn.constitution", "0.1.0"));

    let first = hash_pack(&dir).expect("the pack is hashable");
    let second = hash_pack(&dir).expect("the pack is hashable");
    assert_eq!(first, second);
    assert!(first.starts_with("sha256:"), "{first}");
    let hex_part = &first["sha256:".len()..];
    assert_eq!(hex_part.len(), 64, "{first}");
    assert!(
        hex_part
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase()),
        "{first}"
    );
}

#[test]
fn hash_covers_relative_paths_and_contents() {
    let temp = TempDir::new("expected");
    let text = manifest("cn.constitution", "0.1.0");
    let dir = temp.pack("cn.constitution", &text);
    fs::write(dir.join("content").join("a.txt"), "第一条\n").unwrap();

    let hash = hash_pack(&dir).expect("the pack is hashable");

    // Paths are relative to the pack directory and use '/'; each file
    // contributes its path length, path, content length and content, in path
    // order, with both lengths as little-endian u64.
    let mut expected = Sha256::new();
    for (path, content) in [
        ("content/a.txt", "第一条\n"),
        ("lawpack.toml", text.as_str()),
    ] {
        expected.update((path.len() as u64).to_le_bytes());
        expected.update(path.as_bytes());
        expected.update((content.len() as u64).to_le_bytes());
        expected.update(content.as_bytes());
    }
    assert_eq!(hash, format!("sha256:{}", hex(&expected.finalize())));
}

#[test]
fn hash_keeps_distinct_file_sets_distinct_when_content_contains_nul() {
    let temp = TempDir::new("nul");
    // The legacy `path\0content\0` stream would be identical for these two
    // packs; the explicit lengths keep them apart.
    let one = temp.path().join("one");
    fs::create_dir_all(&one).unwrap();
    fs::write(one.join("a.txt"), b"b\0c.txt\0").unwrap();
    let two = temp.path().join("two");
    fs::create_dir_all(&two).unwrap();
    fs::write(two.join("a.txt"), b"b").unwrap();
    fs::write(two.join("c.txt"), b"").unwrap();

    assert_ne!(
        hash_pack(&one).expect("the pack is hashable"),
        hash_pack(&two).expect("the pack is hashable")
    );
}

#[test]
fn hash_changes_when_one_byte_changes() {
    let temp = TempDir::new("byte-change");
    let dir = temp.pack("cn.constitution", &manifest("cn.constitution", "0.1.0"));
    let content = dir.join("content").join("a.txt");
    fs::write(&content, "abc").unwrap();
    let before = hash_pack(&dir).expect("the pack is hashable");

    fs::write(&content, "abd").unwrap();
    let after = hash_pack(&dir).expect("the pack is hashable");
    assert_ne!(before, after);
}

#[test]
fn crlf_and_lf_content_hash_the_same() {
    let temp = TempDir::new("crlf");
    let text = manifest("cn.constitution", "0.1.0");
    let lf = temp.pack("lf", &text);
    let crlf = temp.pack("crlf", &text.replace('\n', "\r\n"));
    fs::write(lf.join("body.txt"), "第一条\n第二条\n").unwrap();
    fs::write(crlf.join("body.txt"), "第一条\r\n第二条\r\n").unwrap();

    assert_eq!(
        hash_pack(&lf).expect("the pack is hashable"),
        hash_pack(&crlf).expect("the pack is hashable")
    );
}

#[test]
fn hash_of_a_missing_pack_directory_is_an_error() {
    let temp = TempDir::new("missing-pack");
    let missing = temp.path().join("does-not-exist");
    let error = hash_pack(&missing).unwrap_err();
    assert_eq!(error.path(), missing.as_path());
    assert!(error.message().contains("无法读取包目录"), "{error}");
}

#[test]
fn hash_rejects_a_symlink_inside_the_pack() {
    let temp = TempDir::new("symlink-pack");
    let dir = temp.pack("cn.constitution", &manifest("cn.constitution", "0.1.0"));
    let link = dir.join("content").join("linked.txt");
    if !create_file_symlink(&dir.join("lawpack.toml"), &link) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }

    let error = hash_pack(&dir).unwrap_err();
    assert_eq!(error.path(), link.as_path());
    assert!(error.message().contains("符号链接"), "{error}");
}

#[test]
fn a_lock_file_inside_the_pack_is_hashed() {
    let temp = TempDir::new("pack-lock");
    let dir = temp.pack("cn.constitution", &manifest("cn.constitution", "0.1.0"));
    fs::create_dir_all(dir.join("content")).unwrap();
    fs::write(dir.join("content").join("a.txt"), "abc").unwrap();
    let before = hash_pack(&dir).expect("the pack is hashable");

    fs::write(dir.join(LOCK_FILE), "lock_version = 1\n").unwrap();
    let after = hash_pack(&dir).expect("the pack is still hashable");
    assert_ne!(before, after);
}

#[test]
fn build_lock_sorts_packs_by_name() {
    let temp = TempDir::new("build-order");
    temp.pack("zeta-dir", &manifest("zeta.pack", "1.0"));
    temp.pack("alpha-dir", &manifest("alpha.pack", "2.0"));
    fs::write(temp.path().join("zeta-dir").join("a.txt"), "zeta").unwrap();
    fs::write(temp.path().join("alpha-dir").join("a.txt"), "alpha").unwrap();

    let lock = build_lock(temp.path()).expect("the registry is sound");
    let names: Vec<&str> = lock.pack.iter().map(|pack| pack.name.as_str()).collect();
    assert_eq!(names, ["alpha.pack", "zeta.pack"]);
    assert_eq!(lock.pack[0].version, "2.0");
    assert!(lock
        .pack
        .iter()
        .all(|pack| pack.hash.starts_with("sha256:")));
}

#[test]
fn build_lock_reports_every_bad_pack_and_returns_no_lock() {
    let temp = TempDir::new("build-bad");
    temp.pack("good", &manifest("good.pack", "1.0"));
    temp.pack("bad", "[pack]\nname = \"bad.pack\"\nversion = \"1.0\"\n");

    let errors = build_lock(temp.path()).unwrap_err();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].message().contains("jurisdiction"), "{errors:?}");
    assert!(
        !temp.path().join(LOCK_FILE).exists(),
        "build_lock must not write a lock"
    );
}

#[test]
fn build_lock_rejects_two_directories_with_the_same_pack_name() {
    let temp = TempDir::new("build-duplicate");
    temp.pack("first", &manifest("cn.constitution", "0.1.0"));
    temp.pack("second", &manifest("cn.constitution", "0.1.0"));

    let errors = build_lock(temp.path()).unwrap_err();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].message().contains("重复"), "{errors:?}");
}

#[test]
fn build_lock_of_an_empty_registry_has_no_packs() {
    let temp = TempDir::new("build-empty");
    let lock = build_lock(temp.path()).expect("an empty registry is sound");
    assert_eq!(lock, lockfile(&[]));
    lock.write(&temp.path().join(LOCK_FILE)).unwrap();
    let report = verify_lock(temp.path()).expect("the empty lock verifies");
    assert_eq!(report.verified, 0);
}

#[test]
fn verify_lock_needs_a_lock() {
    let temp = TempDir::new("verify-missing-lock");
    temp.pack("cn.constitution", &manifest("cn.constitution", "0.1.0"));

    let errors = verify_lock(temp.path()).unwrap_err();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].path(), temp.path().join(LOCK_FILE).as_path());
    assert!(errors[0].message().contains("没有 std.lock"), "{errors:?}");
}

#[test]
fn verify_lock_accepts_an_unchanged_registry() {
    let temp = TempDir::new("verify-ok");
    temp.pack("cn.constitution", &manifest("cn.constitution", "0.1.0"));
    temp.pack("cn.civil-code", &manifest("cn.civil-code", "2.0"));
    let lock = build_lock(temp.path()).expect("the registry is sound");
    lock.write(&temp.path().join(LOCK_FILE)).unwrap();

    let report = verify_lock(temp.path()).expect("the lock matches the registry");
    assert_eq!(report.verified, 2);
    // The report carries the lock that was just compared with the directory,
    // so callers never have to re-read a file that may have changed.
    assert_eq!(report.lockfile, lock);
}

#[test]
fn verify_lock_rejects_a_version_mismatch() {
    let temp = TempDir::new("verify-version");
    let dir = temp.pack("cn.constitution", &manifest("cn.constitution", "0.1.0"));
    let lock = build_lock(temp.path()).expect("the registry is sound");
    lock.write(&temp.path().join(LOCK_FILE)).unwrap();

    fs::write(
        dir.join("lawpack.toml"),
        manifest("cn.constitution", "0.2.0"),
    )
    .unwrap();
    let errors = verify_lock(temp.path()).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message().contains("版本不符")),
        "{errors:?}"
    );
}

#[test]
fn verify_lock_rejects_a_changed_file() {
    let temp = TempDir::new("verify-hash");
    let dir = temp.pack("cn.constitution", &manifest("cn.constitution", "0.1.0"));
    fs::write(dir.join("body.txt"), "第一条").unwrap();
    let lock = build_lock(temp.path()).expect("the registry is sound");
    lock.write(&temp.path().join(LOCK_FILE)).unwrap();

    fs::write(dir.join("body.txt"), "第二條").unwrap();
    let errors = verify_lock(temp.path()).unwrap_err();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].message().contains("哈希不符"), "{errors:?}");
    assert_eq!(errors[0].path(), dir.as_path());
}

#[test]
fn verify_lock_rejects_an_unlocked_pack() {
    let temp = TempDir::new("verify-extra");
    temp.pack("cn.constitution", &manifest("cn.constitution", "0.1.0"));
    let lock = build_lock(temp.path()).expect("the registry is sound");
    lock.write(&temp.path().join(LOCK_FILE)).unwrap();

    temp.pack("cn.civil-code", &manifest("cn.civil-code", "2.0"));
    let errors = verify_lock(temp.path()).unwrap_err();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].message().contains("未锁定"), "{errors:?}");
    assert!(errors[0].message().contains("cn.civil-code"), "{errors:?}");
}

#[test]
fn verify_lock_rejects_a_locked_pack_that_is_gone() {
    let temp = TempDir::new("verify-gone");
    temp.pack("cn.constitution", &manifest("cn.constitution", "0.1.0"));
    let gone = temp.pack("cn.civil-code", &manifest("cn.civil-code", "2.0"));
    let lock = build_lock(temp.path()).expect("the registry is sound");
    lock.write(&temp.path().join(LOCK_FILE)).unwrap();

    fs::remove_dir_all(&gone).unwrap();
    let errors = verify_lock(temp.path()).unwrap_err();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].message().contains("在目录中不存在"), "{errors:?}");
    assert!(errors[0].message().contains("cn.civil-code"), "{errors:?}");
}

#[test]
fn verify_lock_rejects_a_symlinked_lock() {
    let temp = TempDir::new("verify-link-lock");
    temp.pack("cn.constitution", &manifest("cn.constitution", "0.1.0"));
    let lock = build_lock(temp.path()).expect("the registry is sound");
    let target = temp.path().join("lock-target");
    lock.write(&target).unwrap();
    let link = temp.path().join(LOCK_FILE);
    if !create_file_symlink(&target, &link) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }

    let errors = verify_lock(temp.path()).unwrap_err();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].path(), link.as_path());
    assert!(errors[0].message().contains("符号链接"), "{errors:?}");
}

#[test]
fn verify_lock_reports_a_bad_manifest() {
    let temp = TempDir::new("verify-bad-manifest");
    temp.pack("cn.constitution", &manifest("cn.constitution", "0.1.0"));
    let lock = build_lock(temp.path()).expect("the registry is sound");
    lock.write(&temp.path().join(LOCK_FILE)).unwrap();

    temp.pack("broken", "not a manifest");
    let errors = verify_lock(temp.path()).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message().contains("锁文件") || error.message().contains("TOML")),
        "{errors:?}"
    );
}

#[test]
fn the_repository_lock_matches_the_repository_packs() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("lawpacks");
    let report = verify_lock(&root).expect("lawpacks/std.lock matches lawpacks");
    assert!(report.verified >= 1, "{report:?}");
    // The report exposes the verified lock's own entries.
    assert!(
        report
            .lockfile
            .pack
            .iter()
            .any(|pack| pack.name == "cn.constitution" && pack.version == "0.4.0"),
        "{report:?}"
    );
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-lawpack-lock-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    /// Write a pack directory with its manifest and return the directory.
    fn pack(&self, dir_name: &str, manifest: &str) -> PathBuf {
        let dir = self.path.join(dir_name);
        fs::create_dir_all(dir.join("content"))
            .unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
        fs::write(dir.join("lawpack.toml"), manifest)
            .unwrap_or_else(|error| panic!("write manifest: {error}"));
        dir
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[cfg(unix)]
fn create_file_symlink(target: &Path, link: &Path) -> bool {
    std::os::unix::fs::symlink(target, link).is_ok()
}

#[cfg(windows)]
fn create_file_symlink(target: &Path, link: &Path) -> bool {
    std::os::windows::fs::symlink_file(target, link).is_ok()
}

#[cfg(not(any(unix, windows)))]
fn create_file_symlink(_target: &Path, _link: &Path) -> bool {
    false
}
