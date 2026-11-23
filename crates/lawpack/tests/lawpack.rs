//! Tests for manifest format validation and pack discovery.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_lawpack::{load, scan, AuditStatus, Manifest, Trust};

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
corpus = "cn.constitution/2018"

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

/// The review record an `official` manifest must carry.
const REVIEWED: &str = r#"
trust = "official"
maintainers = ["维护组"]
audit_status = "reviewed"
audited_by = "官方包审核流程"
audited_at = "2026-11-23"
"#;

fn manifest_with(extra: &str) -> String {
    format!("[pack]\n{REQUIRED}\n{extra}")
}

fn reviewed_with(extra: &str) -> String {
    manifest_with(&format!("{REVIEWED}\n{extra}"))
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
    assert_eq!(pack.corpus.as_deref(), Some("cn.constitution/2018"));
    assert_eq!(pack.trust, Trust::Community);
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
fn corpus_links_are_optional_and_format_checked() {
    let manifest = Manifest::parse(&manifest_with("")).expect("corpus may be absent");
    assert_eq!(manifest.pack.corpus, None);

    let manifest =
        Manifest::parse(&manifest_with("corpus = \"cn.constitution/2018\"")).expect("valid link");
    assert_eq!(
        manifest.pack.corpus.as_deref(),
        Some("cn.constitution/2018")
    );

    let manifest = Manifest::parse(&manifest_with("corpus = \"\"")).expect("empty means absent");
    assert_eq!(manifest.pack.corpus, None);

    for (link, expected) in [
        ("cn.constitution", "格式无效"),
        ("cn.constitution/2018/extra", "路径分隔符"),
        ("cn.constitution/", "不能为空"),
        ("/2018", "law-id"),
        ("CN.constitution/2018", "law-id"),
        ("cn.constitution/..", "`..`"),
        ("cn.constitution/ 2018", "首尾空白"),
    ] {
        let error = parse_error(&manifest_with(&format!("corpus = \"{link}\"")));
        assert!(error.contains(expected), "`{link}`: {error}");
    }

    let error = parse_error(&manifest_with("corpus = \"cn.constitution/2018\\\\x\""));
    assert!(error.contains("路径分隔符"), "{error}");
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
        ".",
        "..",
        ".cn",
        "cn.",
        "-cn",
        "cn-",
    ] {
        let text = manifest_with("").replace("cn.constitution", name);
        let error = parse_error(&text);
        assert!(error.contains("pack.name"), "{name}: {error}");
    }

    let long = "a".repeat(129);
    let text = manifest_with("").replace("cn.constitution", &long);
    let error = parse_error(&text);
    assert!(error.contains("长度不能超过 128"), "{error}");
}

#[test]
fn invalid_versions_are_rejected() {
    for version in ["1", "1.", ".1", "1..0", "1.x", "0.1.0-beta"] {
        let text = manifest_with("").replace("0.1.0", version);
        let error = parse_error(&text);
        assert!(error.contains("pack.version"), "{version}: {error}");
    }

    let long = "1".repeat(65);
    let text = manifest_with("").replace("0.1.0", &long);
    let error = parse_error(&text);
    assert!(error.contains("长度不能超过 64"), "{error}");
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
        "2019-02-29",
        "1900-02-29",
        "2020-04-31",
    ] {
        let text = manifest_with(&format!("effective_from = \"{date}\""));
        let error = parse_error(&text);
        assert!(error.contains("pack.effective_from"), "{date}: {error}");
    }
}

#[test]
fn calendar_leap_days_are_accepted() {
    for date in ["2020-02-29", "2000-02-29", "1982-12-31"] {
        let text = manifest_with(&format!("effective_from = \"{date}\""));
        let manifest = Manifest::parse(&text)
            .unwrap_or_else(|error| panic!("{date} should be a real calendar date: {error}"));
        assert_eq!(manifest.pack.effective_from.as_deref(), Some(date));
    }
}

#[test]
fn invalid_effective_to_is_rejected() {
    let text = manifest_with("effective_to = \"2020-02-30\"");
    let error = parse_error(&text);
    assert!(error.contains("pack.effective_to"), "{error}");

    let text = manifest_with("effective_to = \"2020-02-32\"");
    let error = parse_error(&text);
    assert!(error.contains("pack.effective_to"), "{error}");
}

#[test]
fn empty_dates_are_treated_as_unset() {
    let text = manifest_with("effective_from = \"\"\neffective_to = \"\"");
    let manifest = Manifest::parse(&text).expect("empty dates mean unset");
    assert_eq!(manifest.pack.effective_from, None);
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
fn trust_defaults_to_community() {
    let manifest = Manifest::parse(&manifest_with("")).expect("trust is optional");
    assert_eq!(manifest.pack.trust, Trust::Community);
    assert_eq!(Trust::default(), Trust::Community);
}

#[test]
fn trust_parses_official_and_ranks_from_experimental_up() {
    let manifest = Manifest::parse(&reviewed_with("")).expect("the review record is complete");
    assert_eq!(manifest.pack.trust, Trust::Official);
    assert!(Trust::Official > Trust::Community);
    assert!(Trust::Community > Trust::Local);
    assert!(Trust::Local > Trust::Experimental);
    assert_eq!(Trust::Official.to_string(), "official");
    assert_eq!(Trust::Community.to_string(), "community");
}

#[test]
fn review_fields_default_to_unreviewed() {
    let manifest = Manifest::parse(&manifest_with("")).expect("review fields are optional");
    assert!(manifest.pack.maintainers.is_empty());
    assert_eq!(manifest.pack.audit_status, AuditStatus::Unreviewed);
    assert_eq!(AuditStatus::default(), AuditStatus::Unreviewed);
    assert_eq!(manifest.pack.audited_by, None);
    assert_eq!(manifest.pack.audited_at, None);
    assert_eq!(AuditStatus::Unreviewed.to_string(), "unreviewed");
    assert_eq!(AuditStatus::Reviewed.to_string(), "reviewed");
}

#[test]
fn review_fields_parse_when_present() {
    let manifest = Manifest::parse(&reviewed_with("")).expect("the review record is complete");
    assert_eq!(manifest.pack.maintainers, vec!["维护组".to_owned()]);
    assert_eq!(manifest.pack.audit_status, AuditStatus::Reviewed);
    assert_eq!(manifest.pack.audited_by.as_deref(), Some("官方包审核流程"));
    assert_eq!(manifest.pack.audited_at.as_deref(), Some("2026-11-23"));
}

#[test]
fn an_empty_review_field_means_absent() {
    let manifest = Manifest::parse(&manifest_with("audited_by = \"\"\naudited_at = \"\""))
        .expect("empty optional fields mean unset");
    assert_eq!(manifest.pack.audited_by, None);
    assert_eq!(manifest.pack.audited_at, None);
}

#[test]
fn official_requires_maintainers() {
    let text = manifest_with(
        "trust = \"official\"\n\
         audit_status = \"reviewed\"\n\
         audited_by = \"审核流程\"\n\
         audited_at = \"2026-11-23\"",
    );
    let error = parse_error(&text);
    assert!(error.contains("pack.maintainers"), "{error}");
    assert!(error.contains("official"), "{error}");
}

#[test]
fn official_requires_the_reviewed_status() {
    let text = manifest_with(
        "trust = \"official\"\n\
         maintainers = [\"维护组\"]\n\
         audited_by = \"审核流程\"\n\
         audited_at = \"2026-11-23\"",
    );
    let error = parse_error(&text);
    assert!(error.contains("pack.audit_status"), "{error}");
    assert!(error.contains("reviewed"), "{error}");
}

#[test]
fn official_requires_a_reviewer_and_a_review_date() {
    let without_reviewer = manifest_with(
        "trust = \"official\"\n\
         maintainers = [\"维护组\"]\n\
         audit_status = \"reviewed\"\n\
         audited_at = \"2026-11-23\"",
    );
    let error = parse_error(&without_reviewer);
    assert!(error.contains("pack.audited_by"), "{error}");

    let without_date = manifest_with(
        "trust = \"official\"\n\
         maintainers = [\"维护组\"]\n\
         audit_status = \"reviewed\"\n\
         audited_by = \"审核流程\"",
    );
    let error = parse_error(&without_date);
    assert!(error.contains("pack.audited_at"), "{error}");
}

#[test]
fn official_requires_a_real_review_date() {
    for date in ["2026-02-30", "2026-13-01", "26-11-23", "2026/11/23"] {
        let text = manifest_with(REVIEWED).replace(
            "audited_at = \"2026-11-23\"",
            &format!("audited_at = \"{date}\""),
        );
        let error = parse_error(&text);
        assert!(
            error.contains("pack.audited_at"),
            "{date:?} should be rejected: {error}"
        );
    }
}

#[test]
fn a_non_official_pack_may_not_carry_a_review_record() {
    let reviewed = manifest_with(
        "maintainers = [\"维护组\"]\n\
         audit_status = \"reviewed\"\n\
         audited_by = \"审核流程\"\n\
         audited_at = \"2026-11-23\"",
    );
    let error = parse_error(&reviewed);
    assert!(error.contains("只有 trust = \"official\""), "{error}");

    let reviewer_only = manifest_with("audited_by = \"审核流程\"");
    let error = parse_error(&reviewer_only);
    assert!(error.contains("只有 trust = \"official\""), "{error}");

    let date_only = manifest_with("trust = \"local\"\naudited_at = \"2026-11-23\"");
    let error = parse_error(&date_only);
    assert!(error.contains("只有 trust = \"official\""), "{error}");

    let experimental = manifest_with("trust = \"experimental\"\naudit_status = \"reviewed\"");
    let error = parse_error(&experimental);
    assert!(error.contains("只有 trust = \"official\""), "{error}");
}

#[test]
fn maintainer_text_rules_are_enforced() {
    let long = "维".repeat(129);
    for (entry, expected) in [
        ("", "不能为空"),
        (r"维护\n组", "控制字符"),
        (r"维护\t组", "控制字符"),
        (" 维护组", "首尾空白"),
        ("维护组 ", "首尾空白"),
        (long.as_str(), "长度不能超过 128"),
    ] {
        let text = manifest_with(&format!("maintainers = [\"{entry}\"]"));
        let error = parse_error(&text);
        assert!(
            error.contains("pack.maintainers") && error.contains(expected),
            "{entry:?}: {error}"
        );
    }
}

#[test]
fn duplicate_maintainers_are_rejected() {
    let text = manifest_with("maintainers = [\"维护组\", \"另一个组\", \"维护组\"]");
    let error = parse_error(&text);
    assert!(error.contains("pack.maintainers"), "{error}");
    assert!(error.contains("重复"), "{error}");
    assert!(error.contains("第 3 项"), "{error}");
}

#[test]
fn reviewer_text_rules_are_enforced() {
    for (toml_value, expected) in [
        (r"审核\n流程", "控制字符"),
        (r"审核\t流程", "控制字符"),
        (" 审核流程", "首尾空白"),
        ("审核流程 ", "首尾空白"),
    ] {
        let text = manifest_with(REVIEWED).replace(
            "audited_by = \"官方包审核流程\"",
            &format!("audited_by = \"{toml_value}\""),
        );
        let error = parse_error(&text);
        assert!(
            error.contains("pack.audited_by") && error.contains(expected),
            "{toml_value:?}: {error}"
        );
    }

    let long = "审".repeat(129);
    let text = manifest_with(REVIEWED).replace(
        "audited_by = \"官方包审核流程\"",
        &format!("audited_by = \"{long}\""),
    );
    let error = parse_error(&text);
    assert!(error.contains("pack.audited_by"), "{error}");
    assert!(error.contains("长度不能超过 128"), "{error}");
}

#[test]
fn an_unknown_audit_status_is_rejected() {
    for value in ["Reviewed", "pending", "reviewed ", "official"] {
        let text = manifest_with(REVIEWED).replace(
            "audit_status = \"reviewed\"",
            &format!("audit_status = \"{value}\""),
        );
        let error = parse_error(&text);
        assert!(error.contains("unknown variant"), "{value}: {error}");
    }
}

#[test]
fn an_unknown_trust_level_is_rejected() {
    for value in ["official ", "Official", "root", "trusted"] {
        let error = parse_error(&manifest_with(&format!("trust = \"{value}\"")));
        assert!(error.contains("unknown variant"), "{value}: {error}");
    }
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

#[test]
fn a_dangling_manifest_symlink_is_an_error() {
    let temp = TempDir::new("dangling-manifest");
    let dir = temp.path().join("pkg");
    fs::create_dir_all(&dir).unwrap();
    let link = dir.join("lawpack.toml");
    if !create_file_symlink(&temp.path().join("missing.toml"), &link) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }

    let found = scan(temp.path()).expect("the root is readable");
    assert!(found.packs.is_empty(), "{found:?}");
    assert_eq!(found.errors.len(), 1, "{found:?}");
    assert_eq!(found.errors[0].path(), link.as_path());
    assert!(found.errors[0].message().contains("符号链接"), "{found:?}");
    assert!(load(temp.path()).is_err(), "a dangling link is not a pack");
}

#[test]
fn a_manifest_symlink_to_an_external_file_is_rejected() {
    let temp = TempDir::new("external-manifest-file");
    let outside = TempDir::new("outside-manifest-file");
    let external = outside.path().join("external-lawpack.toml");
    fs::write(&external, VALID).unwrap();

    let dir = temp.path().join("pkg");
    fs::create_dir_all(&dir).unwrap();
    let link = dir.join("lawpack.toml");
    if !create_file_symlink(&external, &link) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }

    let found = scan(temp.path()).expect("the root is readable");
    assert!(found.packs.is_empty(), "{found:?}");
    assert_eq!(found.errors.len(), 1, "{found:?}");
    assert_eq!(found.errors[0].path(), link.as_path());
    assert!(found.errors[0].message().contains("符号链接"), "{found:?}");
}

#[test]
fn a_manifest_symlink_to_an_external_directory_is_rejected() {
    let temp = TempDir::new("external-manifest-dir");
    let outside = TempDir::new("outside-manifest-dir");
    let external = outside.path().join("external-dir");
    fs::create_dir_all(&external).unwrap();

    let dir = temp.path().join("pkg");
    fs::create_dir_all(&dir).unwrap();
    let link = dir.join("lawpack.toml");
    if !create_dir_symlink(&external, &link) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }

    let found = scan(temp.path()).expect("the root is readable");
    assert!(found.packs.is_empty(), "{found:?}");
    assert_eq!(found.errors.len(), 1, "{found:?}");
    assert_eq!(found.errors[0].path(), link.as_path());
    assert!(found.errors[0].message().contains("符号链接"), "{found:?}");
}

#[test]
fn a_symlinked_child_directory_is_rejected() {
    let temp = TempDir::new("linked-child");
    let outside = TempDir::new("outside-child");
    outside.write_pack("real", VALID);

    let link = temp.path().join("linked");
    if !create_dir_symlink(&outside.path().join("real"), &link) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }

    let found = scan(temp.path()).expect("the root is readable");
    assert!(found.packs.is_empty(), "{found:?}");
    assert_eq!(found.errors.len(), 1, "{found:?}");
    assert_eq!(found.errors[0].path(), link.as_path());
    assert!(found.errors[0].message().contains("符号链接"), "{found:?}");
}

#[cfg(windows)]
#[test]
fn a_junction_outside_the_root_is_rejected() {
    let temp = TempDir::new("junction-root");
    let outside = TempDir::new("junction-outside");
    outside.write_pack("real", VALID);

    let link = temp.path().join("linked");
    if !create_junction(&outside.path().join("real"), &link) {
        eprintln!("skipping: cannot create a junction");
        return;
    }

    let found = scan(temp.path()).expect("the root is readable");
    assert!(found.packs.is_empty(), "{found:?}");
    assert_eq!(found.errors.len(), 1, "{found:?}");
    let message = found.errors[0].message();
    assert!(
        message.contains("越界") || message.contains("符号链接"),
        "{found:?}"
    );
}

#[cfg(unix)]
fn create_file_symlink(target: &Path, link: &Path) -> bool {
    std::os::unix::fs::symlink(target, link).is_ok()
}

#[cfg(windows)]
fn create_file_symlink(target: &Path, link: &Path) -> bool {
    std::os::windows::fs::symlink_file(target, link).is_ok()
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
fn create_file_symlink(_target: &Path, _link: &Path) -> bool {
    false
}

#[cfg(not(any(unix, windows)))]
fn create_dir_symlink(_target: &Path, _link: &Path) -> bool {
    false
}

#[cfg(windows)]
fn create_junction(target: &Path, link: &Path) -> bool {
    std::process::Command::new("cmd")
        .args(["/C", "mklink", "/J"])
        .arg(link)
        .arg(target)
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false)
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
