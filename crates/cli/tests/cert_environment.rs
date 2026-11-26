//! End-to-end tests for the certificate environment identity.
//!
//! Every test builds a temporary root with its own `lawpacks` registry,
//! profile, corpus files and theory files, then runs the CLI with that root as
//! its current directory. No test depends on the repository's `lawpacks`
//! directory, the working directory the test runner was started from, or the
//! network.

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_cert::{Certificate, EnvironmentIdentity, ExplicitText, TrustLevel};
use std_deduce_lawpack::corpus::hash_file;
use std_deduce_lawpack::{build_lock, Lockfile, LOCK_FILE, OFFICIAL_FILE};

const PROVED: i32 = 0;
const ERROR: i32 = 2;
const PACK: &str = "test.law";
const VERSION: &str = "0.1.0";
const PROFILE: &str = "test.default";
const CORPUS_VERSION: &str = "2026";
const CASE: &str = "case.std";
const PLAIN: &str = "plain.std";
const GOAL: &str = "test.law.受侵犯 张三 甲宅";
const PLAIN_GOAL: &str = "好 张三";

const PLAIN_THEORY: &str = "sort 人\npred 好 : 人 → Prop\nobj 张三 : 人\n\
    axiom 事实 : 好 张三\n  source text \"案件\" locator \"一\"\n";

fn pack_theory() -> String {
    format!(
        r#"
namespace {PACK}
sort {PACK}.人
sort {PACK}.宅
pred {PACK}.侵占 : {PACK}.人 → {PACK}.宅 → Prop
pred {PACK}.受侵犯 : {PACK}.人 → {PACK}.宅 → Prop
rule {PACK}.侵占即侵犯 :
  params p : {PACK}.人, h : {PACK}.宅
  premise {PACK}.侵占 p h
  conclude {PACK}.受侵犯 p h
  source text "测试" locator "一"
"#
    )
}

fn case_theory() -> String {
    format!(
        "import {PACK}\nobj 张三 : {PACK}.人\nobj 甲宅 : {PACK}.宅\n\
         axiom 事实 : {PACK}.侵占 张三 甲宅\n  source text \"案件\" locator \"一\"\n"
    )
}

fn manifest_text(version: &str) -> String {
    format!(
        "[pack]\nname = \"{PACK}\"\nversion = \"{version}\"\n\
         jurisdiction = \"CN\"\nterritory = \"CN\"\nnamespace = \"{PACK}\"\n\
         trust = \"official\"\n\
         maintainers = [\"测试维护组\"]\n\
         audit_status = \"reviewed\"\n\
         audited_by = \"测试审核流程\"\n\
         audited_at = \"2026-11-23\"\n\
         corpus = \"{PACK}/{CORPUS_VERSION}\"\n\n\
         [[files]]\npath = \"theory.std\"\nkind = \"theory\"\n"
    )
}

fn profile_text(version: &str) -> String {
    let constraint = version.rsplit_once('.').map_or(version, |(head, _)| head);
    format!(
        "name = \"{PROFILE}\"\naliases = [\"test\"]\ndefault = true\ntrust = \"official\"\n\n\
         [[packs]]\nname = \"{PACK}\"\nversion = \"{constraint}\"\n"
    )
}

fn corpus_json(text: &str) -> String {
    format!(
        r#"{{
  "format": 2,
  "law": "{PACK}",
  "title": "测试法",
  "version": "{CORPUS_VERSION}",
  "jurisdiction": "CN",
  "articles": [
    {{ "number": "第一条", "text": "{text}" }}
  ]
}}"#
    )
}

fn commands(theory: &str, goal: &str) -> Vec<String> {
    vec![format!(":load {theory}"), format!(":cert {goal}")]
}

struct TempRoot {
    path: PathBuf,
}

impl TempRoot {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cert-environment-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempRoot { path }
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.path.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
        }
        fs::write(&path, text).unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path
    }

    fn corpus_relative(&self) -> String {
        format!("law/corpus/{PACK}/{CORPUS_VERSION}.json")
    }

    fn corpus_path(&self) -> PathBuf {
        self.path.join(self.corpus_relative())
    }

    fn pack_theory_path(&self) -> PathBuf {
        self.path.join(format!("lawpacks/{PACK}/theory.std"))
    }

    /// Install one official pack with a profile and a linked corpus, write the
    /// case file, and build the lock. The corpus is outside the lock.
    fn install_pack(&self, version: &str) {
        self.write(
            &format!("lawpacks/{PACK}/lawpack.toml"),
            &manifest_text(version),
        );
        self.write(&format!("lawpacks/{PACK}/theory.std"), &pack_theory());
        self.write(
            &format!("lawpacks/profiles/{PROFILE}.toml"),
            &profile_text(version),
        );
        self.write(&self.corpus_relative(), &corpus_json("测试条文。"));
        self.write(CASE, &case_theory());
        self.lock();
    }

    fn lock(&self) {
        let root = self.path.join("lawpacks");
        let lockfile = build_lock(&root).unwrap_or_else(|errors| {
            panic!(
                "build_lock failed: {}",
                errors
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("; ")
            )
        });
        lockfile
            .write(&root.join(LOCK_FILE))
            .unwrap_or_else(|error| panic!("write lock: {error}"));
        self.write_whitelist();
    }

    /// List every locked official pack in `official.toml`, using the hash the
    /// lock recorded, so the registry's `official` claim can be verified.
    fn write_whitelist(&self) {
        let root = self.path.join("lawpacks");
        let lockfile = Lockfile::read(&root.join(LOCK_FILE)).expect("the lock exists");
        let mut text = String::new();
        for entry in &lockfile.pack {
            text.push_str(&format!(
                "[[pack]]\nname = \"{}\"\nversion = \"{}\"\nhash = \"{}\"\n\n",
                entry.name, entry.version, entry.hash
            ));
        }
        self.write(&format!("lawpacks/{OFFICIAL_FILE}"), &text);
    }

    fn run(&self, arguments: &[String]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_std-deduce"))
            .current_dir(&self.path)
            .args(arguments)
            .output()
            .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
    }

    fn session(&self, options: &[&str], commands: &[String]) -> Output {
        let mut arguments: Vec<String> =
            options.iter().map(|option| (*option).to_owned()).collect();
        arguments.extend(commands.iter().cloned());
        self.run(&arguments)
    }

    /// Generate a certificate and require success.
    fn generate(&self, options: &[&str], theory: &str, goal: &str) -> Certificate {
        let generated = self.session(options, &commands(theory, goal));
        assert_exit(&generated, PROVED);
        certificate_json(&generated)
    }

    /// Write a certificate and verify it in a fresh process.
    fn verify(
        &self,
        options: &[&str],
        theory: &str,
        certificate: &Certificate,
        goal: Option<&str>,
    ) -> Output {
        let path = self.write("certificate.json", &pretty(certificate));
        let verify = match goal {
            Some(goal) => format!(":verify-cert {} {goal}", path.display()),
            None => format!(":verify-cert {}", path.display()),
        };
        self.session(options, &[format!(":load {theory}"), verify])
    }
}

impl Drop for TempRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn assert_exit(output: &Output, expected: i32) {
    let code = output.status.code();
    assert_eq!(
        code,
        Some(expected),
        "expected exit {expected}, got {code:?}\nstdout:\n{}\nstderr:\n{}",
        stdout(output),
        stderr(output)
    );
}

/// The certificate is the tail of stdout starting at the first `{`.
fn certificate_json(output: &Output) -> Certificate {
    let text = stdout(output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    Certificate::from_json(text[start..].trim_end())
        .unwrap_or_else(|error| panic!("invalid certificate JSON:\n{error}\nstdout:\n{text}"))
}

fn recorded(certificate: &Certificate) -> &std_deduce_cert::EnvironmentRecord {
    let EnvironmentIdentity::Recorded(record) = &certificate.environment else {
        panic!("an exported certificate must record its environment");
    };
    record
}

fn pretty(certificate: &Certificate) -> String {
    certificate
        .to_json_pretty()
        .expect("the certificate serializes")
}

/// Remove the top-level `environment` member from pretty certificate JSON.
///
/// The input is serde_json's pretty output: top-level members are indented by
/// two spaces, and the environment object's closing brace is `  },`.
fn remove_environment_member(json: &str) -> String {
    let start = json
        .find("\n  \"environment\": {")
        .expect("the certificate has an environment member");
    let closing = json[start..]
        .find("\n  },")
        .expect("the environment object closes at top-level indentation")
        + start;
    let mut text = String::with_capacity(json.len());
    text.push_str(&json[..start]);
    text.push_str(&json[closing + "\n  },".len()..]);
    text
}

/// Remove the first `profile` member of the environment object.
fn remove_profile_member(json: &str) -> String {
    let marker = format!("    \"profile\": \"{PROFILE}\",\n");
    assert!(
        json.contains(&marker),
        "the certificate does not have the expected profile member:\n{json}"
    );
    json.replacen(&marker, "", 1)
}

/// Verify one hand-edited certificate JSON document and assert it is rejected.
fn reject_certificate(root: &TempRoot, tag: &str, json: &str, stderr_needle: &str) -> Output {
    let path = root.write(&format!("certificate-{tag}.json"), json);
    let checked = root.session(
        &[],
        &[
            format!(":load {CASE}"),
            format!(":verify-cert {}", path.display()),
        ],
    );
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(out.contains("环境校验：未运行"), "{out}");
    assert!(
        !out.contains("逻辑校验：通过") && !out.contains("内核证明：通过"),
        "no proof layer may run when the certificate is unreadable:\n{out}"
    );
    let err = stderr(&checked);
    assert!(
        err.contains(stderr_needle),
        "stderr does not contain {stderr_needle:?}:\n{err}"
    );
    checked
}

#[test]
fn a_valid_v13_certificate_records_and_checks_the_same_environment() {
    let root = TempRoot::new("valid");
    root.install_pack(VERSION);

    let certificate = root.generate(&[], CASE, GOAL);
    let record = recorded(&certificate);
    assert_eq!(record.profile.as_deref(), Some(PROFILE));
    assert_eq!(record.packs.len(), 1);
    assert_eq!(record.packs[0].name, PACK);
    assert_eq!(record.packs[0].version, VERSION);
    assert_eq!(record.packs[0].trust, TrustLevel::Official);
    assert!(record.packs[0].hash.starts_with("sha256:"));
    assert_eq!(record.corpora.len(), 1);
    assert_eq!(record.corpora[0].law, PACK);
    assert_eq!(record.corpora[0].version, CORPUS_VERSION);
    assert_eq!(
        record.corpora[0].file_sha256,
        hash_file(&root.corpus_path()).expect("the corpus hashes"),
        "the recorded hash must be the corpus file hash, not an article hash"
    );
    assert!(record.as_of.is_none());
    assert!(record.jurisdiction.is_none());

    // A fresh process on the same environment accepts it.
    let checked = root.verify(&[], CASE, &certificate, None);
    assert_exit(&checked, PROVED);
    let out = stdout(&checked);
    assert!(
        out.contains(&format!(
            "环境校验：通过（profile {PROFILE}；包 1 个；语料 1 个；as_of 未指定；管辖 未指定）"
        )),
        "{out}"
    );
    assert!(out.contains("逻辑校验：通过"), "{out}");
    assert!(out.contains("内核证明：通过"), "{out}");
}

#[test]
fn a_session_without_a_default_environment_records_explicit_nulls() {
    let root = TempRoot::new("empty-environment");
    root.write(PLAIN, PLAIN_THEORY);

    let generated = root.session(&[], &commands(PLAIN, PLAIN_GOAL));
    assert_exit(&generated, PROVED);
    let text = stdout(&generated);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    let json_text = text[start..].trim_end();

    // The whole environment object is explicit: five keys, null (not missing)
    // for the absent profile/as_of/jurisdiction, and empty arrays for the rest.
    let expected_environment = concat!(
        "  \"environment\": {\n",
        "    \"profile\": null,\n",
        "    \"packs\": [],\n",
        "    \"corpora\": [],\n",
        "    \"as_of\": null,\n",
        "    \"jurisdiction\": null\n",
        "  },",
    );
    assert!(
        json_text.contains(expected_environment),
        "the environment object is not the explicit empty identity:\n{json_text}"
    );

    // Format order is part of the wire format.
    let format = json_text.find("\"format_version\"").unwrap();
    let environment_at = json_text.find("\"environment\"").unwrap();
    let assumptions = json_text.find("\"assumptions\"").unwrap();
    assert!(
        format < environment_at && environment_at < assumptions,
        "{json_text}"
    );
    let tail = &json_text[environment_at..];
    let mut last = 0;
    for field in ["profile", "packs", "corpora", "as_of", "jurisdiction"] {
        let at = tail
            .find(&format!("\"{field}\""))
            .unwrap_or_else(|| panic!("no environment field {field}:\n{json_text}"));
        assert!(
            at > last,
            "environment field {field} is out of order:\n{json_text}"
        );
        last = at;
    }

    let certificate = Certificate::from_json(json_text).expect("the JSON round-trips");
    assert!(recorded(&certificate).profile.is_none());
    let checked = root.verify(&[], PLAIN, &certificate, Some(PLAIN_GOAL));
    assert_exit(&checked, PROVED);
    let out = stdout(&checked);
    assert!(
        out.contains(
            "环境校验：通过（profile 未指定；包 0 个；语料 0 个；as_of 未指定；管辖 未指定）"
        ),
        "{out}"
    );
    assert!(out.contains("目标绑定：通过"), "{out}");
}

#[test]
fn a_v2_certificate_is_rejected_before_its_missing_environment() {
    let root = TempRoot::new("v2");
    root.install_pack(VERSION);
    let certificate = root.generate(&[], CASE, GOAL);

    let mut v2 = remove_environment_member(&pretty(&certificate));
    v2 = v2.replacen("\"format_version\": 13", "\"format_version\": 2", 1);

    let checked = reject_certificate(&root, "v2", &v2, "unsupported certificate format version 2");
    let err = stderr(&checked);
    assert!(err.contains("this build supports 13"), "{err}");
    assert!(
        !err.contains("missing field `environment`"),
        "the version error must win over the missing field:\n{err}"
    );
}

#[test]
fn a_missing_environment_or_profile_is_rejected() {
    let root = TempRoot::new("missing-fields");
    root.install_pack(VERSION);
    let certificate = root.generate(&[], CASE, GOAL);
    let base = pretty(&certificate);

    reject_certificate(
        &root,
        "missing-environment",
        &remove_environment_member(&base),
        "missing field `environment`",
    );
    reject_certificate(
        &root,
        "missing-profile",
        &remove_profile_member(&base),
        "missing field `profile`",
    );
}

/// Deleting the corpus after generation makes the *current* identity
/// unbuildable, so the environment check cannot run: `:verify-cert` rejects the
/// certificate before either proof layer instead of comparing the recorded
/// identity against a guessed empty one.
#[test]
fn a_deleted_corpus_fails_verify_without_running_a_proof_layer() {
    let root = TempRoot::new("deleted-corpus-verify");
    root.install_pack(VERSION);
    let certificate = root.generate(&[], CASE, GOAL);

    fs::remove_file(root.corpus_path()).expect("remove the corpus file");
    let checked = root.verify(&[], CASE, &certificate, None);
    assert_exit(&checked, ERROR);

    let out = stdout(&checked);
    let section = out
        .find("环境校验：")
        .map(|at| &out[at..])
        .unwrap_or_else(|| panic!("no environment line in stdout:\n{out}"));
    let lines: Vec<&str> = section.lines().take(5).collect();
    assert_eq!(lines.len(), 5, "the report has five lines:\n{out}");
    assert!(
        lines[0].starts_with("环境校验：未运行（无法构造当前环境身份："),
        "the five-line report must start with the environment line:\n{out}"
    );
    for (line, label) in
        lines
            .iter()
            .zip(["环境校验", "逻辑校验", "内核证明", "侧条件", "需人判断"])
    {
        assert!(
            line.starts_with(&format!("{label}：")),
            "the `{label}` section must not run:\n{out}"
        );
    }
    assert!(out.contains("逻辑校验：未运行"), "{out}");
    assert!(!out.contains("逻辑校验：通过"), "{out}");
    let err = stderr(&checked);
    assert!(err.contains("语料"), "{err}");
    assert!(err.contains("无法读取"), "{err}");
}

/// The corpus is not covered by `std.lock`: changing it must still reject the
/// certificate, which is the point of recording its file hash.
#[test]
fn a_changed_corpus_file_invalidates_an_exported_certificate() {
    let root = TempRoot::new("corpus-drift");
    root.install_pack(VERSION);
    let certificate = root.generate(&[], CASE, GOAL);

    // The lock still verifies: only the corpus file changed.
    root.write(&root.corpus_relative(), &corpus_json("改动后的条文。"));

    let checked = root.verify(&[], CASE, &certificate, None);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(out.contains("环境校验：失败"), "{out}");
    assert!(
        out.contains(&format!("语料 `{PACK}@{CORPUS_VERSION}` 文件哈希不一致")),
        "{out}"
    );
    assert!(out.contains("逻辑校验：未运行（环境校验失败）"), "{out}");
    assert!(!out.contains("逻辑校验：通过"), "{out}");
    let err = stderr(&checked);
    assert!(err.contains("环境校验失败"), "{err}");
}

#[test]
fn a_pack_version_drift_across_registries_is_rejected() {
    let first = TempRoot::new("version-a");
    first.install_pack(VERSION);
    let certificate = first.generate(&[], CASE, GOAL);

    let second = TempRoot::new("version-b");
    second.install_pack("0.2.0");
    let checked = second.verify(&[], CASE, &certificate, None);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains(&format!(
            "包 `{PACK}` 版本不一致：证书为 {VERSION}，当前为 0.2.0"
        )),
        "{out}"
    );
    assert!(!out.contains("逻辑校验：通过"), "{out}");
}

#[test]
fn a_pack_content_hash_drift_is_rejected() {
    let root = TempRoot::new("pack-hash-drift");
    root.install_pack(VERSION);
    let certificate = root.generate(&[], CASE, GOAL);

    let theory = root.pack_theory_path();
    let mut content = fs::read_to_string(&theory).expect("read the pack theory");
    content.push_str("\n-- 内容漂移：版本不变，锁哈希改变。\n");
    fs::write(&theory, content).expect("write the pack theory");
    root.lock();

    let checked = root.verify(&[], CASE, &certificate, None);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains(&format!("包 `{PACK}@{VERSION}` 哈希不一致")),
        "{out}"
    );
    assert!(out.contains("逻辑校验：未运行（环境校验失败）"), "{out}");
}

#[test]
fn a_pack_missing_from_the_current_environment_is_rejected() {
    let first = TempRoot::new("missing-pack-a");
    first.install_pack(VERSION);
    let certificate = first.generate(&[], CASE, GOAL);

    let second = TempRoot::new("missing-pack-b");
    second.write(PLAIN, PLAIN_THEORY);
    let checked = second.verify(&[], PLAIN, &certificate, None);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains(&format!("当前环境缺少证书记录的包 `{PACK}@{VERSION}`")),
        "{out}"
    );
}

#[test]
fn a_pack_extra_in_the_current_environment_is_rejected() {
    let root = TempRoot::new("extra-pack");
    root.install_pack(VERSION);
    root.write(PLAIN, PLAIN_THEORY);

    // No default environment: the certificate records nothing.
    let certificate = root.generate(&["--no-default-packs"], PLAIN, PLAIN_GOAL);
    assert_eq!(recorded(&certificate).packs, Vec::new());

    // The same theory now loads under the default profile.
    let checked = root.verify(
        &["--profile", PROFILE],
        PLAIN,
        &certificate,
        Some(PLAIN_GOAL),
    );
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains(&format!("当前环境多出证书未记录的包 `{PACK}@{VERSION}`")),
        "{out}"
    );
    assert!(out.contains("profile 不一致"), "{out}");
}

#[test]
fn a_profile_drift_with_the_same_packs_is_rejected() {
    let root = TempRoot::new("profile-drift");
    root.install_pack(VERSION);

    // Explicit import loads the pack without a profile.
    let certificate = root.generate(&["--no-default-packs"], CASE, GOAL);
    let record = recorded(&certificate);
    assert!(record.profile.is_none(), "{record:?}");
    assert_eq!(record.packs.len(), 1);
    assert_eq!(record.corpora.len(), 1);

    let checked = root.verify(&[], CASE, &certificate, None);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains(&format!("profile 不一致：证书为 null，当前为 `{PROFILE}`")),
        "{out}"
    );
    assert!(!out.contains("缺少证书记录的包"), "{out}");
    assert!(!out.contains("多出证书未记录的包"), "{out}");
    assert!(!out.contains("版本不一致"), "{out}");
    assert!(!out.contains("哈希不一致"), "{out}");
}

#[test]
fn a_profile_alias_records_the_canonical_name() {
    let root = TempRoot::new("profile-alias");
    root.install_pack(VERSION);

    let certificate = root.generate(&["--profile", "test"], CASE, GOAL);
    assert_eq!(recorded(&certificate).profile.as_deref(), Some(PROFILE));

    let checked = root.verify(&["--profile", PROFILE], CASE, &certificate, Some(GOAL));
    assert_exit(&checked, PROVED);
    let out = stdout(&checked);
    assert!(
        out.contains(&format!("环境校验：通过（profile {PROFILE}")),
        "{out}"
    );
    assert!(out.contains("目标绑定：通过"), "{out}");
}

#[test]
fn a_hand_edited_trust_level_is_rejected() {
    let root = TempRoot::new("trust-drift");
    root.install_pack(VERSION);
    let mut certificate = root.generate(&[], CASE, GOAL);
    let EnvironmentIdentity::Recorded(environment) = &mut certificate.environment else {
        panic!("the certificate records its environment");
    };
    environment.packs[0].trust = TrustLevel::Community;

    let checked = root.verify(&[], CASE, &certificate, None);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains(&format!(
            "包 `{PACK}@{VERSION}` 信任级别不一致：证书为 community，当前为 official"
        )),
        "{out}"
    );
}

#[test]
fn cert_requires_a_loaded_theory_and_writes_no_json() {
    let root = TempRoot::new("cert-not-loaded");
    root.install_pack(VERSION);

    let output = root.session(&[], &[format!(":cert {GOAL}")]);
    assert_exit(&output, ERROR);
    assert_eq!(
        stdout(&output),
        "",
        "the failed :cert must not write anything to stdout"
    );
    let err = stderr(&output);
    assert!(err.contains("尚未加载理论"), "{err}");
}

#[test]
fn an_unreadable_corpus_fails_cert_without_a_partial_json() {
    let root = TempRoot::new("unreadable-corpus");
    root.install_pack(VERSION);
    fs::remove_file(root.corpus_path()).expect("remove the corpus file");

    let output = root.session(&[], &commands(CASE, GOAL));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("已加载"), "the theory still loads:\n{out}");
    assert!(
        !out.contains('{'),
        "a failed :cert must not write half a JSON document:\n{out}"
    );
    let err = stderr(&output);
    assert!(err.contains("语料"), "{err}");
    assert!(err.contains("无法读取或哈希"), "{err}");
}

#[test]
fn as_of_and_jurisdiction_are_recorded_and_checked_with_the_same_values() {
    let root = TempRoot::new("as-of-jurisdiction");
    root.install_pack(VERSION);
    let options = ["--as-of", "2026-11-23", "--jurisdiction", "CN"];

    let certificate = root.generate(&options, CASE, GOAL);
    let record = recorded(&certificate);
    assert_eq!(record.as_of.as_deref(), Some("2026-11-23"));
    assert_eq!(record.jurisdiction.as_deref(), Some("CN"));

    // The wire format carries the values, not only the typed accessor.
    let json = pretty(&certificate);
    assert!(
        json.contains("    \"as_of\": \"2026-11-23\","),
        "the as-of value is not in the environment object:\n{json}"
    );
    assert!(
        json.contains("    \"jurisdiction\": \"CN\""),
        "the jurisdiction value is not in the environment object:\n{json}"
    );

    // A fresh process with the same options accepts it.
    let checked = root.verify(&options, CASE, &certificate, Some(GOAL));
    assert_exit(&checked, PROVED);
    let out = stdout(&checked);
    assert!(
        out.contains(&format!(
            "环境校验：通过（profile {PROFILE}；包 1 个；语料 1 个；as_of 2026-11-23；管辖 CN）"
        )),
        "{out}"
    );
    assert!(out.contains("目标绑定：通过"), "{out}");
    assert!(out.contains("逻辑校验：通过"), "{out}");
}

#[test]
fn certificate_identity_options_do_not_change_the_pack_or_corpus_identity() {
    let root = TempRoot::new("as-of-packs-unchanged");
    root.install_pack(VERSION);

    let plain = recorded(&root.generate(&[], CASE, GOAL)).clone();
    let dated = recorded(&root.generate(
        &["--as-of", "2026-11-23", "--jurisdiction", "CN"],
        CASE,
        GOAL,
    ))
    .clone();

    assert_eq!(plain.profile, dated.profile);
    assert_eq!(plain.packs, dated.packs);
    assert_eq!(plain.corpora, dated.corpora);
    assert_eq!(plain.as_of, ExplicitText::none());
    assert_eq!(plain.jurisdiction, ExplicitText::none());
    assert_eq!(dated.as_of, ExplicitText::some("2026-11-23"));
    assert_eq!(dated.jurisdiction, ExplicitText::some("CN"));
}

#[test]
fn changed_or_missing_as_of_and_jurisdiction_are_rejected() {
    let root = TempRoot::new("as-of-drift");
    root.install_pack(VERSION);
    let certificate = root.generate(
        &["--as-of", "2026-11-23", "--jurisdiction", "CN"],
        CASE,
        GOAL,
    );

    // Different values: both fields are compared exactly.
    let checked = root.verify(
        &["--as-of", "2026-11-24", "--jurisdiction", "US"],
        CASE,
        &certificate,
        None,
    );
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(out.contains("环境校验：失败（2 处差异）"), "{out}");
    assert!(
        out.contains("as_of 不一致：证书为 `2026-11-23`，当前为 `2026-11-24`"),
        "{out}"
    );
    assert!(
        out.contains("管辖不一致：证书为 `CN`，当前为 `US`"),
        "{out}"
    );
    assert!(out.contains("逻辑校验：未运行（环境校验失败）"), "{out}");
    assert!(!out.contains("逻辑校验：通过"), "{out}");

    // Omitted values: the current identity records an explicit null.
    let checked = root.verify(&[], CASE, &certificate, None);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(out.contains("环境校验：失败（2 处差异）"), "{out}");
    assert!(
        out.contains("as_of 不一致：证书为 `2026-11-23`，当前为 null"),
        "{out}"
    );
    assert!(
        out.contains("管辖不一致：证书为 `CN`，当前为 null"),
        "{out}"
    );
}

#[test]
fn a_certificate_that_recorded_nulls_rejects_session_values() {
    let root = TempRoot::new("as-of-reverse-drift");
    root.install_pack(VERSION);
    let certificate = root.generate(&[], CASE, GOAL);
    assert!(recorded(&certificate).as_of.is_none());
    assert!(recorded(&certificate).jurisdiction.is_none());

    let checked = root.verify(
        &["--as-of", "2026-11-23", "--jurisdiction", "CN"],
        CASE,
        &certificate,
        None,
    );
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains("as_of 不一致：证书为 null，当前为 `2026-11-23`"),
        "{out}"
    );
    assert!(
        out.contains("管辖不一致：证书为 null，当前为 `CN`"),
        "{out}"
    );
}

#[test]
fn certificate_identity_options_do_not_affect_packs_env_or_why() {
    let root = TempRoot::new("as-of-no-side-effects");
    root.install_pack(VERSION);
    let options = ["--as-of", "2026-11-23", "--jurisdiction", "CN"];

    // `:packs` and `env` only read the registry; the identity options are not
    // part of the environment they report.
    let plain = root.session(&[], &[":packs lawpacks".to_owned()]);
    let dated = root.session(&options, &[":packs lawpacks".to_owned()]);
    assert_exit(&plain, PROVED);
    assert_exit(&dated, PROVED);
    assert_eq!(stdout(&plain), stdout(&dated), "`:packs` must not change");

    let plain = root.session(&[], &["env".to_owned()]);
    let dated = root.session(&options, &["env".to_owned()]);
    assert_exit(&plain, PROVED);
    assert_exit(&dated, PROVED);
    assert_eq!(stdout(&plain), stdout(&dated), "`env` must not change");

    // An ordinary `:why` does not stamp a certificate identity, but the
    // session's as-of date and jurisdiction are inputs of the applicability
    // judgement: the derivation is the same, while the labelled applicability
    // state may differ (the pack rules inherit `jurisdiction = "CN"` and
    // `territory = "CN"` from the manifest, and the case records no place).
    let why = vec![format!(":load {CASE}"), format!(":why {GOAL}")];
    let plain = root.session(&[], &why);
    let dated = root.session(&options, &why);
    assert_exit(&plain, PROVED);
    assert_exit(&dated, PROVED);
    let derivation = |out: &str| {
        let start = out
            .find('▸')
            .unwrap_or_else(|| panic!("no derivation tree:\n{out}"));
        out[start..]
            .split("\n\n")
            .next()
            .unwrap_or_default()
            .to_owned()
    };
    // The inline applicability verdict is part of the line; strip it to compare
    // the derivation's own structure, which the identity options must not touch.
    let without_verdict = |block: String| {
        let mut stripped = String::new();
        for line in block.lines() {
            if let (Some(open), Some(close)) = (line.find('〔'), line.find('〕')) {
                if close > open {
                    stripped.push_str(&line[..open]);
                    stripped.push_str(&line[close + '〕'.len_utf8()..]);
                    stripped.push('\n');
                    continue;
                }
            }
            stripped.push_str(line);
            stripped.push('\n');
        }
        stripped
    };
    assert_eq!(
        without_verdict(derivation(&stdout(&plain))),
        without_verdict(derivation(&stdout(&dated))),
        "the identity options must not change the derivation itself"
    );
    let plain_out = stdout(&plain);
    let dated_out = stdout(&dated);
    assert!(
        plain_out.contains(
            "⟨test.law.侵占即侵犯⟩〔适用性未判定（规则声明了管辖，但会话未设置 :jurisdiction）〕"
        ),
        "{plain_out}"
    );
    assert!(
        dated_out.contains(
            "⟨test.law.侵占即侵犯⟩〔适用性未判定（规则声明了地域，但实例引用的前提事实都没有记录发生地点）〕"
        ),
        "{dated_out}"
    );
}

#[test]
fn environment_difference_output_escapes_certificate_text() {
    let root = TempRoot::new("escaped-differences");
    root.install_pack(VERSION);
    let mut certificate = root.generate(&[], CASE, GOAL);
    let EnvironmentIdentity::Recorded(environment) = &mut certificate.environment else {
        panic!("the certificate records its environment");
    };
    environment.profile = ExplicitText::some("evil\n环境校验：通过");
    environment.packs[0].name = "bad\u{001B}[31m".to_owned();

    let checked = root.verify(&[], CASE, &certificate, None);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(out.contains("环境校验：失败（3 处差异）"), "{out}");
    assert!(
        out.contains("evil\\n环境校验"),
        "the newline in the profile must be escaped:\n{out:?}"
    );
    assert!(
        out.contains("\\u{001B}[31m"),
        "the ESC in the pack name must be escaped:\n{out:?}"
    );
    assert!(!out.contains('\u{001B}'), "{out:?}");
    assert!(
        !out.contains("\n环境校验：通过"),
        "a newline must not forge an output line:\n{out:?}"
    );
    let difference_lines = out.lines().filter(|line| line.starts_with("  - ")).count();
    assert_eq!(difference_lines, 3, "one line per difference:\n{out}");
    assert!(out.contains("逻辑校验：未运行（环境校验失败）"), "{out}");
}
