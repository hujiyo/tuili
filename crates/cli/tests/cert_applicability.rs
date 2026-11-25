//! End-to-end tests for certificate v7 applicability: the generated record,
//! the independent recomputation of `:verify-cert`, and hand-edited
//! counterexamples that must be rejected.
//!
//! Every test writes its own theory into a temporary root and runs separate
//! CLI processes for generation and verification, so the checker only sees the
//! file and the loaded environment.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const GAP: i32 = 1;
const ERROR: i32 = 2;

fn run_in(current_dir: &Path, args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(current_dir)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn assert_exit(output: &Output, expected: i32) {
    assert_eq!(
        output.status.code(),
        Some(expected),
        "expected exit {expected}, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout(output),
        stderr(output)
    );
}

struct TempRoot {
    path: PathBuf,
}

impl TempRoot {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cert-applicability-{}-{tag}-{n}",
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

    fn session(&self, options: &[&str], commands: &[String]) -> Output {
        let mut arguments: Vec<String> =
            options.iter().map(|option| (*option).to_owned()).collect();
        arguments.extend(commands.iter().cloned());
        run_in(&self.path, &arguments)
    }
}

impl Drop for TempRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

/// The certificate JSON is the tail of stdout starting at the first `{`.
fn certificate_text(output: &Output) -> String {
    let out = stdout(output);
    let start = out
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{out}"));
    out[start..].trim_end().to_owned()
}

fn certificate_json(output: &Output) -> serde_json::Value {
    let text = certificate_text(output);
    serde_json::from_str(&text)
        .unwrap_or_else(|error| panic!("the certificate is not JSON: {error}\n{text}"))
}

/// The root node of a certificate, following the recorded root index.
fn root_node(value: &serde_json::Value) -> &serde_json::Value {
    let root = value["root"]
        .as_u64()
        .unwrap_or_else(|| panic!("no root index:\n{value}"));
    &value["nodes"][root as usize]
}

fn write_certificate(root: &TempRoot, tag: &str, value: &serde_json::Value) -> PathBuf {
    let text = serde_json::to_string_pretty(value).expect("the certificate serializes");
    root.write(&format!("certificate-{tag}.json"), &text)
}

/// Generate a certificate in one session and return it with its file path.
fn generate(
    root: &TempRoot,
    options: &[&str],
    theory: &Path,
    goal: &str,
) -> (serde_json::Value, PathBuf) {
    let output = root.session(
        options,
        &[
            format!(":load {}", theory.display()),
            format!(":cert {goal}"),
        ],
    );
    assert_exit(&output, PROVED);
    let value = certificate_json(&output);
    let path = write_certificate(root, "base", &value);
    (value, path)
}

/// Verify one certificate file in a fresh process.
fn verify(root: &TempRoot, options: &[&str], theory: &Path, path: &Path) -> Output {
    root.session(
        options,
        &[
            format!(":load {}", theory.display()),
            format!(":verify-cert {}", path.display()),
        ],
    )
}

/// Verify a hand-edited certificate and require a logical-check failure that
/// names the node and the mismatching field.
fn reject_edit(
    root: &TempRoot,
    options: &[&str],
    theory: &Path,
    value: &serde_json::Value,
) -> String {
    let path = write_certificate(root, "edited", value);
    let output = verify(root, options, theory, &path);
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(
        out.contains("环境校验：通过"),
        "the environment identity must still match:\n{out}"
    );
    assert!(
        out.contains("逻辑校验：失败"),
        "the applicability mismatch must fail the logical layer:\n{out}"
    );
    assert!(
        !out.contains("逻辑校验：通过") && !out.contains("内核证明：通过"),
        "no layer may pass after the applicability check failed:\n{out}"
    );
    let err = stderr(&output);
    assert!(err.contains("证书校验失败（逻辑层）"), "{err}");
    err
}

const EVENT_TIME_THEORY: &str = r#"
sort 人
pred 行为 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 事实 : 行为 甲
  source text "材料" locator "一"
  occurred_at 2019-05-01
  occurred_in CN-HN
rule 规则 :
  params x : 人
  premise 行为 x
  conclude 结论 x
  effective 1999-01-01
  repealed 2021-01-01
  jurisdiction CN
  territory CN-HN
  source text "旧法" locator "第一条"
"#;

const LATE_RULE_THEORY: &str = r#"
sort 人
pred 行为 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 事实 : 行为 甲
  source text "材料" locator "一"
  occurred_at 2019-05-01
rule 规则 :
  params x : 人
  premise 行为 x
  conclude 结论 x
  effective 2021-01-01
  source text "新法" locator "第一条"
"#;

const NO_EVENT_TIME_THEORY: &str = r#"
sort 人
pred 行为 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 事实 : 行为 甲
  source text "材料" locator "一"
rule 规则 :
  params x : 人
  premise 行为 x
  conclude 结论 x
  effective 2021-01-01
  source text "新法" locator "第一条"
"#;

const PARTIAL_COVERAGE_THEORY: &str = r#"
sort 人
pred 前期 : 人 → Prop
pred 后期 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 一 : 前期 甲
  source text "材料" locator "一"
  occurred_at 2019-05-01
axiom 二 : 后期 甲
  source text "材料" locator "二"
  occurred_at 2022-06-01
rule 跨期规则 :
  params x : 人
  premise 前期 x
  premise 后期 x
  conclude 结论 x
  effective 1999-01-01
  repealed 2021-01-01
  source text "旧法" locator "第一条"
"#;

/// An event-time-applicable rule with no `:asof` records the verdict, the
/// event time and place, the rule's scope, and the explicit "no fallback"
/// state. Verification passes.
#[test]
fn an_event_time_applicable_record_verifies() {
    let root = TempRoot::new("event-time");
    let theory = root.write("case.std", EVENT_TIME_THEORY);

    let options = ["--jurisdiction", "CN"];
    let output = root.session(
        &options,
        &[
            format!(":load {}", theory.display()),
            ":cert 结论 甲".to_owned(),
        ],
    );
    assert_exit(&output, PROVED);
    let text = certificate_text(&output);
    let certificate: serde_json::Value =
        serde_json::from_str(&text).expect("the certificate is JSON");
    let file = root.write("certificate-base.json", &text);
    let record = &certificate["nodes"][1]["applicability"];
    assert_eq!(record["verdict"], "applicable");
    assert!(record["reason"].is_null(), "{certificate}");
    assert_eq!(record["basis"]["dates"][0]["date"], "2019-05-01");
    assert_eq!(record["basis"]["dates"][0]["query_date_fallback"], false);
    assert_eq!(record["basis"]["dates"][0]["covered"], true);
    assert_eq!(record["basis"]["places"][0]["place"], "CN-HN");
    assert_eq!(record["basis"]["places"][0]["covered"], true);
    assert_eq!(record["basis"]["scope"]["effective_from"], "1999-01-01");
    assert_eq!(record["basis"]["scope"]["effective_to"], "2021-01-01");
    assert_eq!(record["basis"]["scope"]["jurisdiction"], "CN");
    assert_eq!(record["basis"]["scope"]["territory"], "CN-HN");
    assert_eq!(
        record["basis"]["scope"]["effective_from_origin"], "rule",
        "the declaration's per-field origin is recorded"
    );
    assert!(
        record["basis"]["session"]["as_of"].is_null(),
        "no :asof was used as a fallback:\n{certificate}"
    );
    assert_eq!(record["basis"]["session"]["jurisdiction"], "CN");

    let checked = verify(&root, &["--jurisdiction", "CN"], &theory, &file);
    assert_exit(&checked, PROVED);
    let out = stdout(&checked);
    assert!(out.contains("环境校验：通过"), "{out}");
    assert!(out.contains("逻辑校验：通过"), "{out}");
    assert!(out.contains("内核证明：通过"), "{out}");

    // The same case generated twice produces the same JSON bytes.
    let again = root.session(
        &options,
        &[
            format!(":load {}", theory.display()),
            ":cert 结论 甲".to_owned(),
        ],
    );
    assert_exit(&again, PROVED);
    assert_eq!(
        certificate_text(&again),
        text,
        "repeated :cert must be byte-identical"
    );
}

/// An inapplicable rule is recorded on the gap candidate with its reason;
/// verification passes the logical layer but the missing conclusion keeps the
/// gap exit code.
#[test]
fn an_inapplicable_gap_candidate_is_recorded_and_verifies_as_a_gap() {
    let root = TempRoot::new("inapplicable");
    let theory = root.write("case.std", LATE_RULE_THEORY);
    let output = root.session(
        &[],
        &[
            format!(":load {}", theory.display()),
            ":cert 结论 甲".to_owned(),
        ],
    );
    assert_exit(&output, GAP);
    let certificate = certificate_json(&output);
    assert!(
        certificate["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .all(|node| node["kind"] != "rule_application"),
        "an inapplicable rule must not produce a rule application node"
    );
    let candidate = &root_node(&certificate)["candidates"][0];
    assert_eq!(candidate["rule"], "规则");
    let record = &candidate["applicability"];
    assert_eq!(record["verdict"], "inapplicable");
    assert_eq!(record["reason"]["detail"]["kind"], "not_yet_in_force");
    assert_eq!(record["reason"]["detail"]["effective_from"], "2021-01-01");
    assert_eq!(record["reason"]["detail"]["dates"][0], "2019-05-01");
    assert!(
        record["reason"]["text"]
            .as_str()
            .unwrap()
            .contains("早于规则生效日 2021-01-01"),
        "{certificate}"
    );
    assert!(record["reason"].is_object());

    let file = write_certificate(&root, "base", &certificate);
    let checked = verify(&root, &[], &theory, &file);
    assert_exit(&checked, GAP);
    let out = stdout(&checked);
    assert!(out.contains("环境校验：通过"), "{out}");
    assert!(out.contains("逻辑校验：通过"), "{out}");
    assert!(out.contains("根未被证明"), "{out}");
}

/// With no event time the session `:asof` stands in for the behaviour time;
/// the record says so explicitly, and changing the session date rejects the old
/// certificate by environment identity while the new certificate's verdict
/// changes.
#[test]
fn a_session_asof_fallback_is_explicit_and_changing_it_changes_the_verdict() {
    let root = TempRoot::new("asof-fallback");
    let theory = root.write("case.std", NO_EVENT_TIME_THEORY);
    let dated = ["--as-of", "2022-01-01"];

    let (certificate, file) = generate(&root, &dated, &theory, "结论 甲");
    let record = &certificate["nodes"][1]["applicability"];
    assert_eq!(record["verdict"], "applicable");
    assert_eq!(record["basis"]["dates"][0]["date"], "2022-01-01");
    assert_eq!(record["basis"]["dates"][0]["query_date_fallback"], true);
    assert_eq!(record["basis"]["dates"][0]["covered"], true);
    assert_eq!(
        record["basis"]["session"]["as_of"], "2022-01-01",
        "the fallback date is marked as a substitute, not a fact:\n{certificate}"
    );

    let checked = verify(&root, &dated, &theory, &file);
    assert_exit(&checked, PROVED);
    let out = stdout(&checked);
    assert!(out.contains("逻辑校验：通过"), "{out}");

    // Changing the session date makes the recorded identity differ; the
    // environment check runs before any applicability recomputation.
    let other = ["--as-of", "2019-06-01"];
    let checked = verify(&root, &other, &theory, &file);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(out.contains("环境校验：失败"), "{out}");
    assert!(out.contains("as_of 不一致"), "{out}");
    assert!(out.contains("逻辑校验：未运行（环境校验失败）"), "{out}");

    // A new certificate for the earlier date is inapplicable and the goal is
    // a gap.
    let output = root.session(
        &other,
        &[
            format!(":load {}", theory.display()),
            ":cert 结论 甲".to_owned(),
        ],
    );
    assert_exit(&output, GAP);
    let certificate = certificate_json(&output);
    let record = &root_node(&certificate)["candidates"][0]["applicability"];
    assert_eq!(record["verdict"], "inapplicable");
    assert_eq!(record["basis"]["dates"][0]["date"], "2019-06-01");
    assert_eq!(record["basis"]["dates"][0]["query_date_fallback"], true);
    assert_eq!(record["basis"]["session"]["as_of"], "2019-06-01");
}

/// Partial event-time coverage is undecidable and records both sides; the
/// recomputation agrees and `:verify-cert` keeps the gap exit code.
#[test]
fn partial_coverage_is_undecidable_and_recomputes() {
    let root = TempRoot::new("partial");
    let theory = root.write("case.std", PARTIAL_COVERAGE_THEORY);
    let output = root.session(
        &[],
        &[
            format!(":load {}", theory.display()),
            ":cert 结论 甲".to_owned(),
        ],
    );
    assert_exit(&output, GAP);
    let certificate = certificate_json(&output);
    let record = &root_node(&certificate)["candidates"][0]["applicability"];
    assert_eq!(record["verdict"], "undecidable");
    assert_eq!(record["reason"]["detail"]["kind"], "partial_date_coverage");
    assert_eq!(record["reason"]["detail"]["covered"][0], "2019-05-01");
    assert_eq!(record["reason"]["detail"]["outside"][0], "2022-06-01");
    assert_eq!(record["reason"]["detail"]["effective_to"], "2021-01-01");
    assert!(
        record["reason"]["text"]
            .as_str()
            .unwrap()
            .contains("部分覆盖不能当作适用"),
        "{certificate}"
    );

    let file = write_certificate(&root, "base", &certificate);
    let checked = verify(&root, &[], &theory, &file);
    assert_exit(&checked, GAP);
    let out = stdout(&checked);
    assert!(out.contains("逻辑校验：通过"), "{out}");
}

/// Flipping a recorded verdict to another value is rejected.
#[test]
fn a_flipped_verdict_is_rejected() {
    let root = TempRoot::new("flip-verdict");
    let theory = root.write("case.std", EVENT_TIME_THEORY);
    let (mut certificate, _) = generate(&root, &["--jurisdiction", "CN"], &theory, "结论 甲");
    certificate["nodes"][1]["applicability"]["verdict"] = serde_json::Value::from("unchecked");
    let err = reject_edit(&root, &["--jurisdiction", "CN"], &theory, &certificate);
    assert!(err.contains("节点 1"), "{err}");
    assert!(err.contains("适用性记录"), "{err}");
    assert!(
        err.contains("unchecked") && err.contains("applicable"),
        "{err}"
    );

    // The opposite direction: an applicable verdict where the environment
    // says the rule is unknown is rejected the same way.
    let (mut certificate, _) = generate(&root, &["--jurisdiction", "CN"], &theory, "结论 甲");
    certificate["nodes"][1]["applicability"]["verdict"] = serde_json::Value::from("inapplicable");
    let err = reject_edit(&root, &["--jurisdiction", "CN"], &theory, &certificate);
    assert!(err.contains("节点 1"), "{err}");
}

/// An unchecked verdict on a rule application cannot be flipped to
/// `applicable`: the recomputation has no jurisdiction to compare.
#[test]
fn an_unchecked_verdict_cannot_be_flipped_to_applicable() {
    let root = TempRoot::new("flip-unchecked");
    let theory = root.write(
        "case.std",
        r#"
sort 人
pred 行为 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 事实 : 行为 甲
  source text "材料" locator "一"
rule 规则 :
  params x : 人
  premise 行为 x
  conclude 结论 x
  jurisdiction CN
  source text "测试法" locator "第一条"
"#,
    );
    let (mut certificate, _) = generate(&root, &[], &theory, "结论 甲");
    assert_eq!(
        certificate["nodes"][1]["applicability"]["verdict"], "unchecked",
        "{certificate}"
    );
    assert_eq!(
        certificate["nodes"][1]["applicability"]["reason"]["detail"]["kind"],
        "no_query_jurisdiction"
    );
    certificate["nodes"][1]["applicability"]["verdict"] = serde_json::Value::from("applicable");
    certificate["nodes"][1]["applicability"]["reason"] = serde_json::Value::Null;
    let err = reject_edit(&root, &[], &theory, &certificate);
    assert!(err.contains("节点 1"), "{err}");
    assert!(
        err.contains("unchecked") && err.contains("applicable"),
        "{err}"
    );
}

/// Changing one reference event time is rejected at the named basis field.
#[test]
fn a_changed_basis_date_is_rejected() {
    let root = TempRoot::new("change-date");
    let theory = root.write("case.std", EVENT_TIME_THEORY);
    let (mut certificate, _) = generate(&root, &["--jurisdiction", "CN"], &theory, "结论 甲");
    certificate["nodes"][1]["applicability"]["basis"]["dates"][0]["date"] =
        serde_json::Value::from("2019-05-02");
    let err = reject_edit(&root, &["--jurisdiction", "CN"], &theory, &certificate);
    assert!(err.contains("节点 1"), "{err}");
    assert!(
        err.contains("dates[0].date") && err.contains("2019-05-02"),
        "{err}"
    );
}

/// Deleting a rule application's applicability record is a missing format
/// field, not a defaulted "unchecked".
#[test]
fn a_deleted_applicability_record_is_rejected() {
    let root = TempRoot::new("delete-record");
    let theory = root.write("case.std", EVENT_TIME_THEORY);
    let (mut certificate, _) = generate(&root, &["--jurisdiction", "CN"], &theory, "结论 甲");
    certificate["nodes"][1]
        .as_object_mut()
        .unwrap()
        .remove("applicability");
    let path = write_certificate(&root, "deleted", &certificate);
    let output = verify(&root, &["--jurisdiction", "CN"], &theory, &path);
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("证书 JSON 无效"), "{out}");
    assert!(out.contains("环境校验：未运行"), "{out}");
    let err = stderr(&output);
    assert!(err.contains("missing field `applicability`"), "{err}");
}

/// An `as_of` cannot be inserted into a record that used the event time.
#[test]
fn an_invented_asof_on_an_event_time_record_is_rejected() {
    let root = TempRoot::new("invented-asof");
    let theory = root.write("case.std", EVENT_TIME_THEORY);
    let (mut certificate, _) = generate(&root, &["--jurisdiction", "CN"], &theory, "结论 甲");
    certificate["nodes"][1]["applicability"]["basis"]["session"]["as_of"] =
        serde_json::Value::from("2020-01-01");
    let err = reject_edit(&root, &["--jurisdiction", "CN"], &theory, &certificate);
    assert!(err.contains("节点 1"), "{err}");
    assert!(err.contains("as_of"), "{err}");
}

/// Changing the fallback date on the record (without changing the session)
/// is rejected.
#[test]
fn a_changed_fallback_date_is_rejected() {
    let root = TempRoot::new("change-fallback");
    let theory = root.write("case.std", NO_EVENT_TIME_THEORY);
    let options = ["--as-of", "2022-01-01"];
    let (mut certificate, _) = generate(&root, &options, &theory, "结论 甲");
    certificate["nodes"][1]["applicability"]["basis"]["dates"][0]["date"] =
        serde_json::Value::from("2022-02-02");
    certificate["nodes"][1]["applicability"]["basis"]["session"]["as_of"] =
        serde_json::Value::from("2022-02-02");
    let err = reject_edit(&root, &options, &theory, &certificate);
    assert!(err.contains("节点 1"), "{err}");
    assert!(err.contains("as_of"), "{err}");
}

/// Editing the rule's declared scope text in the record is rejected against
/// the environment's rule declaration.
#[test]
fn an_edited_scope_text_is_rejected() {
    let root = TempRoot::new("change-scope");
    let theory = root.write("case.std", EVENT_TIME_THEORY);
    let (mut certificate, _) = generate(&root, &["--jurisdiction", "CN"], &theory, "结论 甲");
    certificate["nodes"][1]["applicability"]["basis"]["scope"]["effective_from"] =
        serde_json::Value::from("2000-01-01");
    let err = reject_edit(&root, &["--jurisdiction", "CN"], &theory, &certificate);
    assert!(err.contains("节点 1"), "{err}");
    assert!(err.contains("effective_from"), "{err}");

    let (mut certificate, _) = generate(&root, &["--jurisdiction", "CN"], &theory, "结论 甲");
    certificate["nodes"][1]["applicability"]["basis"]["scope"]["territory"] =
        serde_json::Value::from("CN-BJ");
    let err = reject_edit(&root, &["--jurisdiction", "CN"], &theory, &certificate);
    assert!(err.contains("territory"), "{err}");
}
