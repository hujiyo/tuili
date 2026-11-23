//! Tests for the official-release whitelist.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_lawpack::{read_whitelist, Whitelist, WhitelistPack, OFFICIAL_FILE};

const HASH: &str = "sha256:7e69a4302d72ddb6e3387a1b4c068faaf0d12f17bf35867fd07d4b55d2395407";

fn entry(name: &str, version: &str, hash: &str) -> String {
    format!("[[pack]]\nname = \"{name}\"\nversion = \"{version}\"\nhash = \"{hash}\"\n")
}

fn read_error(root: &Path) -> Vec<std_deduce_lawpack::PackError> {
    match read_whitelist(root) {
        Ok(whitelist) => panic!("the whitelist should be rejected, got {whitelist:?}"),
        Err(errors) => errors,
    }
}

fn render_errors(errors: &[std_deduce_lawpack::PackError]) -> String {
    errors
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n")
}

fn whitelist(entries: &[(&str, &str)]) -> Whitelist {
    Whitelist {
        pack: entries
            .iter()
            .map(|(name, hash)| WhitelistPack {
                name: (*name).to_owned(),
                version: "0.4.0".to_owned(),
                hash: (*hash).to_owned(),
            })
            .collect(),
    }
}

#[test]
fn a_missing_whitelist_is_none() {
    let temp = TempDir::new("missing");
    assert_eq!(
        read_whitelist(temp.path()).expect("missing is not an error"),
        None
    );
}

#[test]
fn a_valid_whitelist_parses_every_field() {
    let temp = TempDir::new("valid");
    temp.write(entry("cn.constitution", "0.4.0", HASH).as_str());

    let parsed = read_whitelist(temp.path())
        .expect("the whitelist is valid")
        .expect("the file exists");
    assert_eq!(parsed.len(), 1);
    assert!(!parsed.is_empty());
    assert_eq!(
        parsed.pack,
        vec![WhitelistPack {
            name: "cn.constitution".to_owned(),
            version: "0.4.0".to_owned(),
            hash: HASH.to_owned(),
        }]
    );
}

#[test]
fn an_empty_whitelist_is_legal_and_covers_nothing() {
    for text in ["", "# 没有官方发行版\n", "pack = []\n"] {
        let temp = TempDir::new("empty");
        temp.write(text);
        let parsed = read_whitelist(temp.path())
            .unwrap_or_else(|errors| panic!("{text:?}: {}", render_errors(&errors)))
            .expect("the file exists");
        assert!(parsed.is_empty(), "{text:?}");
        assert_eq!(parsed.len(), 0, "{text:?}");
        assert!(!parsed.covers("cn.constitution", "0.4.0", HASH), "{text:?}");
    }
}

#[test]
fn covers_requires_name_version_and_hash_to_match_exactly() {
    let known = whitelist(&[("cn.constitution", HASH)]);
    assert!(known.covers("cn.constitution", "0.4.0", HASH));

    // A different name, version or hash is a different release.
    assert!(!known.covers("cn.other", "0.4.0", HASH));
    assert!(!known.covers("cn.constitution", "0.4.1", HASH));
    assert!(!known.covers("cn.constitution", "0.4.0", &HASH.replace('7', "8")));
    let short = &HASH[..HASH.len() - 1];
    assert!(!known.covers("cn.constitution", "0.4.0", short));
    assert!(!known.covers("cn.constitution", "0.4.0", &format!("{HASH}0")));

    assert!(!Whitelist::default().covers("cn.constitution", "0.4.0", HASH));
}

#[test]
fn duplicate_name_and_version_are_rejected() {
    let temp = TempDir::new("duplicate");
    temp.write(&format!(
        "{}{}",
        entry("cn.constitution", "0.4.0", HASH),
        entry("cn.constitution", "0.4.0", &HASH.replace('7', "8"))
    ));

    let errors = read_error(temp.path());
    let text = render_errors(&errors);
    assert!(text.contains("cn.constitution"), "{text}");
    assert!(text.contains("重复"), "{text}");
    assert!(text.contains("第 2 条"), "{text}");
    assert_eq!(
        errors[0].path(),
        temp.path().join(OFFICIAL_FILE).as_path(),
        "every error points at official.toml"
    );
}

#[test]
fn a_second_version_of_the_same_name_is_not_a_duplicate() {
    let temp = TempDir::new("second-version");
    temp.write(&format!(
        "{}{}",
        entry("cn.constitution", "0.4.0", HASH),
        entry("cn.constitution", "0.3.0", HASH)
    ));

    let parsed = read_whitelist(temp.path())
        .expect("two versions of one pack are two releases")
        .expect("the file exists");
    assert_eq!(parsed.len(), 2);
    assert!(parsed.covers("cn.constitution", "0.4.0", HASH));
    assert!(parsed.covers("cn.constitution", "0.3.0", HASH));
    assert!(!parsed.covers("cn.constitution", "0.2.0", HASH));
}

#[test]
fn bad_hashes_are_rejected() {
    for hash in [
        "7e69a4302d72ddb6e3387a1b4c068faaf0d12f17bf35867fd07d4b55d2395407",
        "SHA256:7e69a4302d72ddb6e3387a1b4c068faaf0d12f17bf35867fd07d4b55d2395407",
        "sha256:7E69A4302D72DDB6E3387A1B4C068FAAF0D12F17BF35867FD07D4B55D2395407",
        "sha256:",
        "sha256:7e69a4302d72ddb6e3387a1b4c068faaf0d12f17bf35867fd07d4b55d23954",
        "sha256:7e69a4302d72ddb6e3387a1b4c068faaf0d12f17bf35867fd07d4b55d23954070",
        "sha256:7e69a4302d72ddb6e3387a1b4c068faaf0d12f17bf35867fd07d4b55d239540g",
        "",
    ] {
        let temp = TempDir::new("bad-hash");
        temp.write(&entry("cn.constitution", "0.4.0", hash));
        let errors = read_error(temp.path());
        let text = render_errors(&errors);
        assert!(text.contains("hash"), "{hash:?}: {text}");
        assert!(text.contains("64 位小写十六进制"), "{hash:?}: {text}");
        assert_eq!(errors[0].path(), temp.path().join(OFFICIAL_FILE).as_path());
    }
}

#[test]
fn bad_names_and_versions_are_rejected() {
    for name in [
        "CN.Constitution",
        "cn constitution",
        ".cn",
        "cn.",
        "cn/宪法",
        "",
    ] {
        let temp = TempDir::new("bad-name");
        temp.write(&entry(name, "0.4.0", HASH));
        let errors = read_error(temp.path());
        let text = render_errors(&errors);
        assert!(text.contains("pack.name"), "{name:?}: {text}");
        assert_eq!(errors[0].path(), temp.path().join(OFFICIAL_FILE).as_path());
    }

    for version in ["1", "1.", "0.4.0-beta", "0.4.", ""] {
        let temp = TempDir::new("bad-version");
        temp.write(&entry("cn.constitution", version, HASH));
        let errors = read_error(temp.path());
        let text = render_errors(&errors);
        assert!(text.contains("pack.version"), "{version:?}: {text}");
        assert_eq!(errors[0].path(), temp.path().join(OFFICIAL_FILE).as_path());
    }

    let long = "a".repeat(129);
    let temp = TempDir::new("long-name");
    temp.write(&entry(&long, "0.4.0", HASH));
    let text = render_errors(&read_error(temp.path()));
    assert!(text.contains("长度不能超过 128"), "{text}");
}

#[test]
fn every_entry_error_is_reported() {
    let temp = TempDir::new("many-errors");
    temp.write(&format!(
        "{}{}",
        entry("CN.Bad", "1", "sha256:zz"),
        entry("cn.constitution", "0.4.0", HASH)
    ));

    let errors = read_error(temp.path());
    // The first entry fails on its name, version and hash; all three are
    // reported instead of stopping at the first.
    assert_eq!(errors.len(), 3, "{errors:?}");
    assert!(
        errors
            .iter()
            .all(|error| error.path() == temp.path().join(OFFICIAL_FILE).as_path()),
        "{errors:?}"
    );
}

#[test]
fn unknown_fields_are_rejected() {
    let temp = TempDir::new("unknown-top");
    temp.write(&format!(
        "unexpected = true\n{}",
        entry("cn.constitution", "0.4.0", HASH)
    ));
    let text = render_errors(&read_error(temp.path()));
    assert!(text.contains("unexpected"), "{text}");

    let temp = TempDir::new("unknown-entry");
    temp.write(&format!(
        "{}unexpected = true\n",
        entry("cn.constitution", "0.4.0", HASH)
    ));
    let text = render_errors(&read_error(temp.path()));
    assert!(text.contains("unexpected"), "{text}");
}

#[test]
fn bad_toml_is_reported_with_the_whitelist_path() {
    let temp = TempDir::new("bad-toml");
    temp.write("[[pack]\nname = \n");
    let errors = read_error(temp.path());
    let text = render_errors(&errors);
    assert!(text.contains("解析失败"), "{text}");
    assert_eq!(errors[0].path(), temp.path().join(OFFICIAL_FILE).as_path());
}

#[test]
fn a_whitelist_symlink_is_an_error() {
    let temp = TempDir::new("symlink");
    let real = temp.path().join("real.toml");
    fs::write(&real, entry("cn.constitution", "0.4.0", HASH)).unwrap();
    let link = temp.path().join(OFFICIAL_FILE);
    if !create_file_symlink(&real, &link) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }

    let errors = read_error(temp.path());
    assert_eq!(errors[0].path(), link.as_path());
    assert!(errors[0].message().contains("符号链接"), "{errors:?}");
}

#[test]
fn a_whitelist_that_is_not_a_regular_file_is_an_error() {
    let temp = TempDir::new("directory");
    fs::create_dir_all(temp.path().join(OFFICIAL_FILE)).unwrap();

    let errors = read_error(temp.path());
    assert_eq!(errors[0].path(), temp.path().join(OFFICIAL_FILE).as_path());
    assert!(errors[0].message().contains("不是普通文件"), "{errors:?}");
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-lawpack-whitelist-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn write(&self, text: &str) -> PathBuf {
        let path = self.path.join(OFFICIAL_FILE);
        fs::write(&path, text).unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path
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
