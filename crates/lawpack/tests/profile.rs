//! Tests for environment profiles: parsing, validation and selection.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_lawpack::profile::{
    scan_profiles, select_default, select_named, version_matches, Profile, ProfilePack,
    PROFILES_DIR,
};
use std_deduce_lawpack::{PackError, Trust};

const BASIC: &str = r#"
name = "cn.default"
aliases = ["cn"]
default = true
description = "中国法默认环境：只含官方宪法包"
trust = "official"

[[packs]]
name = "cn.constitution"
version = "0.1"
"#;

fn profile_text(extra: &str) -> String {
    format!("name = \"p.default\"\n{extra}\n[[packs]]\nname = \"pkg.a\"\nversion = \"0.1\"\n")
}

fn scan_error(root: &Path) -> String {
    match scan_profiles(root) {
        Ok(profiles) => panic!("profiles should be rejected, got {profiles:?}"),
        Err(errors) => render_errors(&errors),
    }
}

fn render_errors(errors: &[PackError]) -> String {
    errors
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n")
}

fn profile(name: &str) -> Profile {
    Profile {
        name: name.to_owned(),
        aliases: Vec::new(),
        default: true,
        description: None,
        trust: Trust::Official,
        packs: vec![ProfilePack {
            name: "pkg.a".to_owned(),
            version: "0.1".to_owned(),
        }],
    }
}

#[test]
fn a_valid_profile_parses_all_fields() {
    let temp = TempDir::new("valid");
    temp.write_profile("cn.default.toml", BASIC);

    let profiles = scan_profiles(temp.path()).expect("the profile is valid");
    assert_eq!(profiles.len(), 1);
    let profile = &profiles[0];
    assert_eq!(profile.name, "cn.default");
    assert_eq!(profile.aliases, vec!["cn".to_owned()]);
    assert!(profile.default);
    assert_eq!(
        profile.description.as_deref(),
        Some("中国法默认环境：只含官方宪法包")
    );
    assert_eq!(profile.trust, Trust::Official);
    assert_eq!(
        profile.packs,
        vec![ProfilePack {
            name: "cn.constitution".to_owned(),
            version: "0.1".to_owned(),
        }]
    );
}

#[test]
fn optional_profile_fields_default_to_official_and_no_alias() {
    let temp = TempDir::new("defaults");
    temp.write_profile("p.default.toml", &profile_text(""));

    let profiles = scan_profiles(temp.path()).expect("the profile is valid");
    let profile = &profiles[0];
    assert!(profile.aliases.is_empty());
    assert!(!profile.default);
    assert_eq!(profile.description, None);
    // A profile's trust defaults to `official`, unlike a manifest's.
    assert_eq!(profile.trust, Trust::Official);
    assert_eq!(profile.packs.len(), 1);
}

#[test]
fn invalid_profile_names_are_rejected() {
    for name in [
        "CN.Default",
        "cn default",
        "cn_default",
        "cn/default",
        ".",
        "..",
        ".cn",
        "cn.",
        "-cn",
        "cn-",
    ] {
        let temp = TempDir::new("bad-name");
        temp.write_profile("p.toml", &profile_text("").replace("p.default", name));
        let error = scan_error(temp.path());
        assert!(error.contains("profile.name"), "{name}: {error}");
    }

    let long = "a".repeat(129);
    let temp = TempDir::new("long-name");
    temp.write_profile("p.toml", &profile_text("").replace("p.default", &long));
    let error = scan_error(temp.path());
    assert!(error.contains("长度不能超过 128"), "{error}");
}

#[test]
fn invalid_aliases_are_rejected() {
    for alias in ["CN", "cn alias", "cn_alias", "cn/alias", "-cn", "cn-"] {
        let temp = TempDir::new("bad-alias");
        temp.write_profile("p.toml", &profile_text(&format!("aliases = [\"{alias}\"]")));
        let error = scan_error(temp.path());
        assert!(error.contains("alias"), "{alias}: {error}");
    }
}

#[test]
fn duplicate_pack_entries_are_rejected() {
    let temp = TempDir::new("duplicate-pack");
    temp.write_profile(
        "p.toml",
        "name = \"p.default\"\n\
         [[packs]]\nname = \"pkg.a\"\nversion = \"0.1\"\n\
         [[packs]]\nname = \"pkg.a\"\nversion = \"0.2\"\n",
    );
    let error = scan_error(temp.path());
    assert!(error.contains("pkg.a"), "{error}");
    assert!(error.contains("重复"), "{error}");
}

#[test]
fn a_profile_must_list_at_least_one_pack() {
    let temp = TempDir::new("empty-packs");
    temp.write_profile("p.toml", "name = \"p.default\"\n");
    let error = scan_error(temp.path());
    assert!(error.contains("至少"), "{error}");
}

#[test]
fn bad_version_constraints_are_rejected() {
    for constraint in ["1", "1.", ".1", "1..0", "1.x", "0.1.0-beta", ""] {
        let temp = TempDir::new("bad-version");
        temp.write_profile(
            &format!("p-{}.toml", constraint.replace(['.', '-'], "_")),
            &profile_text("").replace("version = \"0.1\"", &format!("version = \"{constraint}\"")),
        );
        let error = scan_error(temp.path());
        assert!(error.contains("version"), "{constraint:?}: {error}");
    }

    let long = "1".repeat(65);
    let temp = TempDir::new("long-version");
    temp.write_profile(
        "p.toml",
        &profile_text("").replace("version = \"0.1\"", &format!("version = \"{long}\"")),
    );
    let error = scan_error(temp.path());
    assert!(error.contains("长度不能超过 64"), "{error}");
}

#[test]
fn unknown_profile_fields_are_rejected() {
    let temp = TempDir::new("unknown-top");
    temp.write_profile("top.toml", &profile_text("unexpected = true"));
    let error = scan_error(temp.path());
    assert!(error.contains("unexpected"), "{error}");

    let temp = TempDir::new("unknown-pack");
    temp.write_profile(
        "pack.toml",
        "name = \"p.default\"\n\
         [[packs]]\nname = \"pkg.a\"\nversion = \"0.1\"\nunexpected = true\n",
    );
    let error = scan_error(temp.path());
    assert!(error.contains("unexpected"), "{error}");
}

#[test]
fn multiple_default_profiles_are_rejected() {
    let temp = TempDir::new("two-defaults");
    temp.write_profile("a.toml", &profile_text("default = true"));
    temp.write_profile(
        "b.toml",
        &profile_text("default = true").replace("p.default", "p.other"),
    );
    let error = scan_error(temp.path());
    assert!(error.contains("default"), "{error}");
    assert!(error.contains("p.default"), "{error}");
    assert!(error.contains("p.other"), "{error}");
}

#[test]
fn duplicate_profile_names_are_rejected() {
    let temp = TempDir::new("duplicate-name");
    temp.write_profile("a.toml", &profile_text(""));
    temp.write_profile("b.toml", &profile_text(""));
    let error = scan_error(temp.path());
    assert!(error.contains("profile 名"), "{error}");
    assert!(error.contains("重复"), "{error}");
}

#[test]
fn duplicate_aliases_are_rejected() {
    let temp = TempDir::new("duplicate-alias");
    temp.write_profile("a.toml", &profile_text("aliases = [\"shared\"]"));
    temp.write_profile(
        "b.toml",
        &(profile_text("aliases = [\"shared\"]").replace("p.default", "p.other")),
    );
    let error = scan_error(temp.path());
    assert!(error.contains("alias"), "{error}");
    assert!(error.contains("shared"), "{error}");
}

#[test]
fn an_alias_may_not_take_another_profile_name() {
    let temp = TempDir::new("alias-name");
    temp.write_profile("a.toml", &profile_text(""));
    temp.write_profile(
        "b.toml",
        "name = \"p.other\"\naliases = [\"p.default\"]\n\
         [[packs]]\nname = \"pkg.a\"\nversion = \"0.1\"\n",
    );
    let error = scan_error(temp.path());
    assert!(error.contains("alias"), "{error}");
    assert!(error.contains("p.default"), "{error}");
}

#[test]
fn a_duplicate_alias_inside_one_profile_is_rejected() {
    let temp = TempDir::new("self-alias");
    temp.write_profile("a.toml", &profile_text("aliases = [\"same\", \"same\"]"));
    let error = scan_error(temp.path());
    assert!(error.contains("alias"), "{error}");
    assert!(error.contains("same"), "{error}");
}

#[test]
fn a_missing_profiles_directory_means_no_profiles() {
    let temp = TempDir::new("missing-profiles");
    let profiles = scan_profiles(temp.path()).expect("a missing profiles directory is empty");
    assert!(profiles.is_empty());

    let missing_root = temp.path().join("does-not-exist");
    let profiles = scan_profiles(&missing_root).expect("a missing registry root is empty");
    assert!(profiles.is_empty());
}

#[test]
fn a_profiles_directory_that_is_a_file_is_an_error() {
    let temp = TempDir::new("profiles-file");
    fs::write(temp.path().join(PROFILES_DIR), "not a directory").unwrap();
    let error = scan_error(temp.path());
    assert!(error.contains("profiles"), "{error}");
    assert!(
        error.contains("普通目录") || error.contains("不是目录"),
        "{error}"
    );
}

#[test]
fn non_toml_files_in_the_profiles_directory_are_errors() {
    let temp = TempDir::new("non-toml");
    temp.write_file("profiles/cn.default.tom", BASIC);
    let error = scan_error(temp.path());
    assert!(error.contains(".toml"), "{error}");
}

#[test]
fn subdirectories_in_the_profiles_directory_are_errors() {
    let temp = TempDir::new("subdir");
    fs::create_dir_all(temp.path().join(PROFILES_DIR).join("nested")).unwrap();
    let error = scan_error(temp.path());
    assert!(error.contains("子目录"), "{error}");
}

#[test]
fn bad_toml_is_reported_with_its_path() {
    let temp = TempDir::new("bad-toml");
    temp.write_profile("p.toml", "name = \n");
    let error = scan_error(temp.path());
    assert!(error.contains("p.toml"), "{error}");
    assert!(error.contains("TOML"), "{error}");
}

#[test]
fn every_profile_error_is_listed() {
    let temp = TempDir::new("many-errors");
    temp.write_profile("a.toml", "name = \"A\"\n");
    temp.write_profile(
        "b.toml",
        "name = \"b.default\"\n[[packs]]\nname = \"pkg.a\"\n",
    );
    let errors = scan_profiles(temp.path()).expect_err("both files are invalid");
    assert_eq!(errors.len(), 2, "{errors:?}");
}

#[test]
fn a_profiles_directory_symlink_is_an_error() {
    let temp = TempDir::new("profiles-symlink");
    let real = temp.path().join("real-profiles");
    fs::create_dir_all(&real).unwrap();
    fs::write(real.join("p.toml"), profile_text("")).unwrap();
    if !create_dir_symlink(&real, &temp.path().join(PROFILES_DIR)) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }
    let error = scan_error(temp.path());
    assert!(error.contains("符号链接"), "{error}");
}

#[test]
fn a_profile_file_symlink_is_an_error() {
    let temp = TempDir::new("profile-file-symlink");
    let real = temp.path().join("real.toml");
    fs::write(&real, profile_text("")).unwrap();
    let profiles = temp.path().join(PROFILES_DIR);
    fs::create_dir_all(&profiles).unwrap();
    if !create_file_symlink(&real, &profiles.join("p.toml")) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }
    let error = scan_error(temp.path());
    assert!(error.contains("符号链接"), "{error}");
}

#[test]
fn a_default_profile_must_require_official_trust() {
    for trust in ["experimental", "local", "community"] {
        let temp = TempDir::new("default-trust");
        temp.write_profile(
            "p.default.toml",
            &profile_text(&format!("default = true\ntrust = \"{trust}\"")),
        );
        let error = scan_error(temp.path());
        assert!(error.contains("default"), "{trust}: {error}");
        assert!(error.contains("official"), "{trust}: {error}");
    }
}

#[test]
fn a_named_profile_may_require_a_lower_trust_level() {
    for trust in ["experimental", "local", "community"] {
        let temp = TempDir::new("named-trust");
        temp.write_profile(
            "p.named.toml",
            &profile_text(&format!("default = false\ntrust = \"{trust}\"")),
        );
        let profiles = scan_profiles(temp.path())
            .unwrap_or_else(|errors| panic!("{trust}: {}", render_errors(&errors)));
        assert_eq!(profiles.len(), 1, "{trust}");
        assert!(!profiles[0].default, "{trust}");
        assert_eq!(profiles[0].trust.to_string(), trust);
    }
}

#[test]
fn version_matches_uses_segment_prefixes() {
    for (constraint, version, expected) in [
        ("0.1", "0.1", true),
        ("0.1", "0.1.0", true),
        ("0.1", "0.1.9", true),
        ("0.1", "0.1.0.1", true),
        ("0.1", "0.10.0", false),
        ("0.1", "0.2.0", false),
        ("0.1.0", "0.1.0", true),
        ("0.1.0", "0.1.1", false),
        ("01", "1.0", false),
        ("0.1", "0.1x", false),
    ] {
        assert_eq!(
            version_matches(constraint, version),
            expected,
            "{constraint} vs {version}"
        );
    }
    assert!(!version_matches("", "0.1.0"));
}

#[test]
fn select_default_and_named_profiles() {
    assert!(select_default(&[])
        .expect("no profiles is not an error")
        .is_none());

    let default = profile("p.default");
    assert_eq!(
        select_default(std::slice::from_ref(&default))
            .expect("one default is fine")
            .map(|profile| profile.name.as_str()),
        Some("p.default")
    );

    let mut other = profile("p.other");
    other.default = true;
    let error = select_default(&[default.clone(), other]).expect_err("two defaults are invalid");
    assert!(error.contains("p.default"), "{error}");
    assert!(error.contains("p.other"), "{error}");

    let mut named = profile("p.named");
    named.aliases = vec!["alias".to_owned()];
    let profiles = [default, named];
    assert_eq!(
        select_named(&profiles, "alias")
            .expect("an alias selects")
            .name,
        "p.named"
    );
    assert_eq!(
        select_named(&profiles, "p.default")
            .expect("a name selects")
            .name,
        "p.default"
    );
    let error = select_named(&profiles, "missing").expect_err("an unknown name is an error");
    assert!(error.contains("missing"), "{error}");
    assert!(error.contains("p.default"), "{error}");
    assert!(error.contains("p.named"), "{error}");
    assert!(error.contains("alias"), "{error}");
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-lawpack-profile-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn write_file(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.path.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
        }
        fs::write(&path, text).unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path
    }

    fn write_profile(&self, name: &str, text: &str) -> PathBuf {
        self.write_file(&format!("{PROFILES_DIR}/{name}"), text)
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

#[cfg(unix)]
fn create_dir_symlink(target: &Path, link: &Path) -> bool {
    std::os::unix::fs::symlink(target, link).is_ok()
}

#[cfg(windows)]
fn create_dir_symlink(target: &Path, link: &Path) -> bool {
    std::os::windows::fs::symlink_dir(target, link).is_ok()
}

#[cfg(not(any(unix, windows)))]
fn create_dir_symlink(_target: &Path, _link: &Path) -> bool {
    false
}
