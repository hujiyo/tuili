//! Tests for manifest format validation and pack discovery.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_lawpack::{load, scan, Manifest};

const VALID: &str = r#"
[pack]
name = "cn.constitution"
version = "0.1.0"
jurisdiction = "CN"
territory = "CN"
namespace = "cn.constitution"
effective_from = "1982-12-04"
effective_to = "2018-03-11"
description = "示例"

[[files]]
path = "constitution.std"
kind = "theory"

[[files]]
path = "amendment.std"
"#;

const REQUIRED: &str = r#"
name = "cn.constitution"
version = "0.1.0"
jurisdiction = "CN"
territory = "CN"
"#;

fn manifest_with(extra: &str) -> String {
    format!("[pack]\n{REQUIRED}\n{extra}")
}

fn parse_error(text: &str) -> String {
    match Manifest::parse(text) {
        Ok(_) => panic!("manifest should be rejected:\n{text}"),
        Err(error) => error.to_string(),
    }
}

#[test]
fn valid_manifest_parses_all_fields() {
    let manifest = Manifest::parse(VALID).expect("the manifest is valid");
    let pack = &manifest.pack;
    assert_eq!(pack.name, "cn.constitution");
    assert_eq!(pack.version, "0.1.0");
    assert_eq!(pack.jurisdiction, "CN");
    assert_eq!(pack.territory, "CN");
    assert_eq!(pack.namespace.as_deref(), Some("cn.constitution"));
    assert_eq!(pack.effective_from.as_deref(), Some("1982-12-04"));
    assert_eq!(pack.effective_to.as_deref(), Some("2018-03-11"));
    assert_eq!(pack.description.as_deref(), Some("示例"));
    assert_eq!(manifest.files.len(), 2);
    assert_eq!(manifest.files[0].path.as_deref(), Some("constitution.std"));
    assert_eq!(manifest.files[0].kind.as_deref(), Some("theory"));
    assert_eq!(manifest.files[1].path.as_deref(), Some("amendment.std"));
    assert_eq!(manifest.files[1].kind, None);
}

#[test]
fn files_are_optional() {
    let manifest = Manifest::parse(&manifest_with("")).expect("files may be absent");
    assert!(manifest.files.is_empty());
}

#[test]
fn missing_required_field_is_rejected() {
    let error =
        parse_error("[pack]\nversion = \"0.1.0\"\njurisdiction = \"CN\"\nterritory = \"CN\"\n");
    assert!(error.contains("name"), "{error}");

    let error = parse_error(
        "[pack]\nname = \"cn.constitution\"\njurisdiction = \"CN\"\nterritory = \"CN\"\n",
    );
    assert!(error.contains("version"), "{error}");

    let error = parse_error("[pack]\nname = \"cn.constitution\"\nversion = \"0.1.0\"\n");
    assert!(error.contains("jurisdiction"), "{error}");

    let error = parse_error(
        "[pack]\nname = \"cn.constitution\"\nversion = \"0.1.0\"\njurisdiction = \"CN\"\n",
    );
    assert!(error.contains("territory"), "{error}");
}

#[test]
fn missing_pack_table_is_rejected() {
    let error = parse_error("files = []\n");
    assert!(error.contains("pack"), "{error}");
}

#[test]
fn empty_required_fields_are_rejected() {
    for (field, text) in [
        (
            "pack.name",
            manifest_with("").replace("cn.constitution", ""),
        ),
        ("pack.version", manifest_with("").replace("0.1.0", "")),
        (
            "pack.jurisdiction",
            manifest_with("").replace("jurisdiction = \"CN\"", "jurisdiction = \"\""),
        ),
        (
            "pack.territory",
            manifest_with("").replace("territory = \"CN\"", "territory = \"\""),
        ),
    ] {
        let error = parse_error(&text);
        assert!(error.contains(field), "{field}: {error}");
    }
}

#[test]
fn invalid_names_are_rejected() {
    for name in [
        "CN.Constitution",
        "cn constitution",
        "cn_constitution",
        "cn/宪法",
    ] {
        let text = manifest_with("").replace("cn.constitution", name);
        let error = parse_error(&text);
        assert!(error.contains("pack.name"), "{name}: {error}");
    }
}

#[test]
fn invalid_versions_are_rejected() {
    for version in ["1", "1.", ".1", "1..0", "1.x", "0.1.0-beta"] {
        let text = manifest_with("").replace("0.1.0", version);
        let error = parse_error(&text);
        assert!(error.contains("pack.version"), "{version}: {error}");
    }
}

#[test]
fn invalid_jurisdiction_and_territory_are_rejected() {
    for value in ["C N", "CN/", "中国", "C_N"] {
        for field in ["jurisdiction", "territory"] {
            let line = format!("{field} = \"{value}\"");
            let text = manifest_with("").replace(&format!("{field} = \"CN\""), &line);
            let error = parse_error(&text);
            assert!(error.contains(field), "{field} {value}: {error}");
        }
    }
}

#[test]
fn invalid_dates_are_rejected() {
    for date in [
        "1982-13-04",
        "1982-00-04",
        "1982-12-32",
        "1982-12-00",
        "1982-1-04",
        "82-12-04",
        "1982/12/04",
        "19821204",
        "",
    ] {
        let text = manifest_with(&format!("effective_from = \"{date}\""));
        let error = parse_error(&text);
        assert!(error.contains("pack.effective_from"), "{date}: {error}");
    }
}

#[test]
fn invalid_effective_to_is_rejected() {
    let text = manifest_with("effective_to = \"2020-02-30\"");
    let manifest = Manifest::parse(&text).expect("day 30 is in 1..31; content is not judged");
    assert_eq!(manifest.pack.effective_to.as_deref(), Some("2020-02-30"));

    let text = manifest_with("effective_to = \"2020-02-32\"");
    let error = parse_error(&text);
    assert!(error.contains("pack.effective_to"), "{error}");
}

#[test]
fn empty_effective_to_is_treated_as_unset() {
    let text = manifest_with("effective_from = \"1982-12-04\"\neffective_to = \"\"");
    let manifest = Manifest::parse(&text).expect("an empty effective_to means unset");
    assert_eq!(manifest.pack.effective_to, None);
}

#[test]
fn effective_to_before_effective_from_is_accepted() {
    // Ordering is legal semantics, deliberately left to a later step.
    let text = manifest_with("effective_from = \"2000-01-01\"\neffective_to = \"1990-01-01\"");
    let manifest = Manifest::parse(&text).expect("format validation does not order dates");
    assert_eq!(manifest.pack.effective_from.as_deref(), Some("2000-01-01"));
    assert_eq!(manifest.pack.effective_to.as_deref(), Some("1990-01-01"));
}

#[test]
fn unknown_fields_are_rejected() {
    let error = parse_error(&manifest_with("unexpected = true"));
    assert!(error.contains("unexpected"), "{error}");

    let text = format!("[pack]\n{REQUIRED}\n\n[[files]]\npath = \"x.std\"\nunexpected = true\n");
    let error = parse_error(&text);
    assert!(error.contains("unexpected"), "{error}");

    let text = format!("[pack]\n{REQUIRED}\nunexpected = true\n");
    let error = parse_error(&text);
    assert!(error.contains("unexpected"), "{error}");
}

#[test]
fn scan_reads_valid_packs_and_ignores_directories_without_a_manifest() {
    let temp = TempDir::new("scan-ok");
    temp.write_pack("cn.constitution", VALID);
    temp.empty_dir("not-a-pack");
    fs::write(temp.path().join("README.md"), "not a pack").unwrap();

    let packs = load(temp.path()).expect("valid packs load");
    assert_eq!(packs.len(), 1);
    assert_eq!(packs[0].manifest.pack.name, "cn.constitution");
    assert_eq!(packs[0].dir, temp.path().join("cn.constitution"));

    let found = scan(temp.path()).expect("the root is readable");
    assert!(found.errors.is_empty());
    assert_eq!(found.packs.len(), 1);
}

#[test]
fn load_reports_a_bad_manifest_instead_of_skipping_it() {
    let temp = TempDir::new("scan-bad");
    temp.write_pack("good", VALID);
    temp.write_pack("bad", "[pack]\nname = \"bad.pack\"\nversion = \"1.0\"\n");

    let errors = load(temp.path()).expect_err("one bad manifest fails the load");
    assert_eq!(errors.len(), 1);
    assert_eq!(
        errors[0].path(),
        temp.path().join("bad").join("lawpack.toml").as_path()
    );
    assert!(errors[0].message().contains("jurisdiction"), "{errors:?}");

    // The same scan still yields the good pack, which is what the CLI prints.
    let found = scan(temp.path()).expect("the root is readable");
    assert_eq!(found.packs.len(), 1);
    assert_eq!(found.packs[0].manifest.pack.name, "cn.constitution");
    assert_eq!(found.errors.len(), 1);
    assert_eq!(found.errors[0].path(), errors[0].path());
}

#[test]
fn scan_fails_when_the_root_does_not_exist() {
    let temp = TempDir::new("missing-root");
    let missing = temp.path().join("does-not-exist");

    let errors = load(&missing).expect_err("a missing root is an error");
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].path(), missing.as_path());

    let error = scan(&missing).expect_err("a missing root is an error");
    assert_eq!(error.path(), missing.as_path());
}

#[test]
fn empty_root_is_a_successful_scan_with_no_packs() {
    let temp = TempDir::new("empty-root");
    let packs = load(temp.path()).expect("an empty root is not an error");
    assert!(packs.is_empty());

    let found = scan(temp.path()).expect("the root is readable");
    assert!(found.packs.is_empty());
    assert!(found.errors.is_empty());
}

#[test]
fn a_manifest_path_that_is_not_a_file_is_reported() {
    let temp = TempDir::new("manifest-dir");
    let dir = temp.path().join("weird");
    fs::create_dir_all(dir.join("lawpack.toml")).unwrap();

    let found = scan(temp.path()).expect("the root is readable");
    assert!(found.packs.is_empty());
    assert_eq!(found.errors.len(), 1);
    assert_eq!(found.errors[0].path(), dir.join("lawpack.toml").as_path());
    assert!(
        found.errors[0].message().contains("不是普通文件"),
        "{found:?}"
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
            "std-deduce-lawpack-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn write_pack(&self, name: &str, manifest: &str) {
        let dir = self.path.join(name);
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
        fs::write(dir.join("lawpack.toml"), manifest)
            .unwrap_or_else(|error| panic!("write manifest: {error}"));
    }

    fn empty_dir(&self, name: &str) {
        let dir = self.path.join(name);
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
