//! End-to-end tests for the `open` concept marker.
//!
//! The marker is declared in a case, module or pack. These tests cover what is
//! visible to a reader (`:inspect`), the closed-environment gate, pack loading,
//! and the inference-layer obligation: a rule step that concludes an open
//! concept (or a root that is one) makes the derivation depend on a human
//! judgement, so `:why`, `:explain` and `:verify-cert` report it and exit
//! non-zero instead of presenting the conclusion as proved. An enabled
//! interpretation that licenses the concept releases the obligation instead
//! (the sourced interpretation is the explicit human reading), and the tests
//! also forge the certificate back to a non-licensed proof to show the
//! obligation reappears. Candidate enumeration and the `:branches` re-run are
//! covered by `branches.rs`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_cert::{
    Assumption, Certificate, FactIdentity, Node as CertNode, ObligationKind, OpenObligation,
};
use std_deduce_lawpack::{build_lock, LOCK_FILE};

const PROVED: i32 = 0;
const GAP: i32 = 1;
const LOAD_FAILED: i32 = 1;
const ERROR: i32 = 2;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn run(args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn run_in(current_dir: &Path, args: &[&str]) -> Output {
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
    let code = output.status.code();
    assert_eq!(
        code,
        Some(expected),
        "expected exit {expected}, got {code:?}\nstdout:\n{}\nstderr:\n{}",
        stdout(output),
        stderr(output)
    );
}

fn check(output: Output, expected: i32, needles: &[&str]) -> Output {
    assert_exit(&output, expected);
    let out = stdout(&output);
    let err = stderr(&output);
    for needle in needles {
        assert!(
            out.contains(needle),
            "stdout does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

fn check_stderr(output: Output, expected: i32, needles: &[&str]) -> Output {
    assert_exit(&output, expected);
    let out = stdout(&output);
    let err = stderr(&output);
    for needle in needles {
        assert!(
            err.contains(needle),
            "stderr does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-open-concept-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn root(&self) -> &Path {
        &self.path
    }

    fn write(&self, relative: &str, contents: &str) -> PathBuf {
        let path = self.path.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
        }
        fs::write(&path, contents)
            .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path
    }

    fn lawpacks(&self) -> PathBuf {
        self.path.join("lawpacks")
    }

    fn write_pack(&self, name: &str, manifest: &str, files: &[(&str, &str)]) {
        let dir = self.lawpacks().join(name);
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
        fs::write(dir.join("lawpack.toml"), manifest).expect("write manifest");
        for (relative, text) in files {
            let path = dir.join(relative);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent)
                    .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
            }
            fs::write(&path, text).expect("write pack theory");
        }
    }

    fn lock(&self) {
        let root = self.lawpacks();
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
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn pack_manifest(name: &str) -> String {
    format!(
        "[pack]\nname = \"{name}\"\nversion = \"0.1.0\"\n\
         jurisdiction = \"CN\"\nterritory = \"CN\"\nnamespace = \"{name}\"\n\n\
         [[files]]\npath = \"theory.std\"\nkind = \"theory\"\n"
    )
}

// ---------------------------------------------------------------------------
// `:inspect`
// ---------------------------------------------------------------------------

#[test]
fn inspect_marks_only_the_opened_predicate() {
    let temp = TempDir::new("inspect");
    let file = temp.write(
        "case.std",
        "sort 人\n\
         pred 损害 : 人 → Prop\n\
         pred 重大 : 人 → Prop\n\
         open 重大\n",
    );
    let output = check(
        run(&[file.display().to_string(), ":inspect".to_owned()]),
        PROVED,
        &["已加载"],
    );
    let out = stdout(&output);
    let pred = |name: &str| {
        out.lines()
            .find(|line| line.contains("pred") && line.contains(name))
            .unwrap_or_else(|| panic!("no predicate line for {name}:\n{out}"))
            .to_owned()
    };
    assert!(
        pred("重大").contains("〔开放概念〕"),
        "the opened predicate must carry the marker: {:?}",
        pred("重大")
    );
    assert!(
        !pred("损害").contains("〔开放概念〕"),
        "an unopened predicate must not carry the marker: {:?}",
        pred("损害")
    );
    assert!(
        out.lines().any(|line| {
            let line = line.trim_start();
            line.starts_with("open") && line.contains("重大 :")
        }),
        "the marker declaration must stay visible in the ledger, named after its target:\n{out}"
    );
    assert!(
        !out.contains("[案件扩展]"),
        "a plain session must not mark case extensions:\n{out}"
    );
}

#[test]
fn a_bad_open_target_is_reported_with_its_line() {
    let temp = TempDir::new("bad-line");
    let file = temp.write("case.std", "sort 人\npred 重大 : 人 → Prop\nopen 不存在\n");
    let output = check_stderr(
        run(&[file.display().to_string()]),
        LOAD_FAILED,
        &[":3:1: error:", "未知谓词", "`不存在`"],
    );
    assert!(
        !stdout(&output).contains("已加载"),
        "a rejected file must not load:\n{}",
        stdout(&output)
    );
}

// ---------------------------------------------------------------------------
// Closed environment
// ---------------------------------------------------------------------------

#[test]
fn closed_env_rejects_a_case_open_unless_case_rules_are_allowed() {
    let temp = TempDir::new("closed");
    let file = temp.write(
        "case.std",
        "import cn.constitution\nopen cn.constitution.非法搜查\n",
    );
    let path = file.display().to_string();

    let rejected = check_stderr(
        run(&["--closed-env".to_owned(), path.clone()]),
        LOAD_FAILED,
        &[
            "封闭环境",
            "open cn.constitution.非法搜查",
            "--allow-case-rules",
        ],
    );
    assert!(!stdout(&rejected).contains("已加载"));

    let allowed = check(
        run(&[
            "--closed-env".to_owned(),
            "--allow-case-rules".to_owned(),
            path,
            ":inspect".to_owned(),
        ]),
        PROVED,
        &["已加载"],
    );
    let out = stdout(&allowed);
    let pred_line = out
        .lines()
        .find(|line| line.contains("pred") && line.contains("cn.constitution.非法搜查 :"))
        .unwrap_or_else(|| panic!("no predicate line:\n{out}"));
    assert!(
        pred_line.contains("〔开放概念〕"),
        "the predicate must be marked: {pred_line:?}"
    );
    assert!(
        !pred_line.contains("[案件扩展]"),
        "the predicate itself comes from the pack: {pred_line:?}"
    );
    let marker_line = out
        .lines()
        .find(|line| {
            let line = line.trim_start();
            line.starts_with("open") && line.contains("非法搜查")
        })
        .unwrap_or_else(|| panic!("no marker declaration line:\n{out}"));
    assert!(
        marker_line.contains("[案件扩展]"),
        "the case's own marker must be a case extension: {marker_line:?}"
    );
}

#[test]
fn a_pack_may_declare_an_open_concept_and_closed_env_loads_it_normally() {
    let temp = TempDir::new("pack");
    temp.write_pack(
        "pkg.open",
        &pack_manifest("pkg.open"),
        &[(
            "theory.std",
            "namespace pkg.open\n\
             sort pkg.open.人\n\
             pred pkg.open.重大 : pkg.open.人 → Prop\n\
             open pkg.open.重大\n",
        )],
    );
    temp.lock();
    let case = temp.write("case.std", "import pkg.open\n");

    let output = check(
        run_in(
            temp.root(),
            &[
                "--closed-env",
                case.to_str().expect("utf-8 path"),
                ":inspect",
            ],
        ),
        PROVED,
        &["已加载", "导入 pkg.open"],
    );
    let out = stdout(&output);
    let pred_line = out
        .lines()
        .find(|line| line.contains("pred") && line.contains("pkg.open.重大"))
        .unwrap_or_else(|| panic!("no pack predicate line:\n{out}"));
    assert!(
        pred_line.contains("〔开放概念〕"),
        "the pack predicate must be marked: {pred_line:?}"
    );
    assert!(
        pred_line.contains("[pkg.open@0.1.0]"),
        "the pack predicate must show its pack suffix: {pred_line:?}"
    );
    assert!(
        !out.contains("[案件扩展]"),
        "a pack's own marker is not a case extension:\n{out}"
    );
}

// ---------------------------------------------------------------------------
// Open concepts are obligations
// ---------------------------------------------------------------------------

/// The open-concept fixture. A rule derives the open concept `重大` from a
/// closed premise; another rule concludes the closed predicate `轻伤` from the
/// same premise; a third consumes `重大` and concludes the closed predicate
/// `从重处罚`. Nothing supplies `重大` as a fact, so only a rule can state it.
const OPEN_CONCEPT_CASE: &str = r#"sort 人
pred 损害 : 人 → Prop
pred 重大 : 人 → Prop
pred 轻伤 : 人 → Prop
pred 从重处罚 : 人 → Prop
obj 甲 : 人
open 重大
axiom 损害事实 : 损害 甲
  source text "案件" locator "一"
rule 重大推定 :
  params x : 人
  premise 损害 x
  conclude 重大 x
  source text "测试" locator "二"
rule 轻伤结论 :
  params x : 人
  premise 损害 x
  conclude 轻伤 x
  source text "测试" locator "三"
rule 从重 :
  params x : 人
  premise 重大 x
  conclude 从重处罚 x
  source text "测试" locator "五"
"#;

/// `OPEN_CONCEPT_CASE` with the open concept supplied as a user fact instead:
/// the rule `从重` then consumes evidence, not a decision the derivation made.
fn open_concept_case_with_the_fact() -> String {
    format!("{OPEN_CONCEPT_CASE}axiom 重大事实 : 重大 甲\n  source text \"案情\" locator \"四\"\n")
}

/// The certificate JSON of a `:cert` run, parsed.
fn certificate_json(output: &Output) -> Certificate {
    let text = stdout(output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    Certificate::from_json(text[start..].trim_end())
        .unwrap_or_else(|error| panic!("invalid certificate JSON: {error}\n{text}"))
}

/// The certificate part of a `:cert` run, byte for byte.
fn certificate_text(output: &Output) -> String {
    let text = stdout(output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    text[start..].to_owned()
}

/// A rule that concludes an open concept depends on a human judgement: the
/// certificate records the obligation, and neither `:why` nor `:explain` may
/// present the conclusion as an unconditional proof.
#[test]
fn a_rule_that_concludes_an_open_concept_records_the_obligation() {
    let temp = TempDir::new("rule-obligation");
    let theory = temp.write("case.std", OPEN_CONCEPT_CASE);
    let path = theory.display().to_string();

    let why = check(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":why 重大 甲".to_owned(),
        ]),
        GAP,
        &["▸ 重大 甲", "此处需人判断：`重大`", "仍有未决义务"],
    );
    assert!(
        !stdout(&why).contains("推导已通过独立校验。"),
        "an open concept must not be rendered as an unconditional proof:\n{}",
        stdout(&why)
    );

    // The certificate can still be exported — the root is proved — but it
    // carries the obligation, and a rule application concluded the concept.
    let exported = check(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":cert 重大 甲".to_owned(),
        ]),
        PROVED,
        &["open-concept"],
    );
    let certificate = certificate_json(&exported);
    let root = certificate.root.expect("the root is recorded");
    assert_eq!(
        certificate.open_obligations.len(),
        1,
        "{:?}",
        certificate.open_obligations
    );
    let obligation = &certificate.open_obligations[0];
    assert_eq!(obligation.kind, ObligationKind::OpenConcept);
    assert_eq!(obligation.id, "open-concept");
    assert_eq!(
        obligation.description, "开放概念 `重大` 需要人判断，不得当作已证明",
        "the description must name the concept"
    );
    assert_eq!(
        obligation.nodes,
        vec![root],
        "the rule step concluding 「重大」 is the dependency node"
    );

    let explain = check(
        run(&[
            "--no-default-packs".to_owned(),
            path,
            ":explain 重大 甲".to_owned(),
        ]),
        GAP,
        &["此处需人判断：`重大`", "【未决义务】", "开放概念"],
    );
    assert!(
        !stdout(&explain).contains("推导已通过独立校验。"),
        "the narrative must not call an open-concept conclusion independently checked:\n{}",
        stdout(&explain)
    );
}

/// The dependency travels up the proof graph: the root may be a closed
/// conclusion, while the node that states the open concept is listed. The
/// obligation names only the direct dependency node, never every node on the
/// path.
#[test]
fn an_open_concept_dependency_propagates_to_the_root() {
    let temp = TempDir::new("propagation");
    let theory = temp.write("case.std", OPEN_CONCEPT_CASE);
    let path = theory.display().to_string();

    let why = check(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":why 从重处罚 甲".to_owned(),
        ]),
        GAP,
        &["▸ 从重处罚 甲", "此处需人判断：`重大`"],
    );

    let exported = check(
        run(&[
            "--no-default-packs".to_owned(),
            path,
            ":cert 从重处罚 甲".to_owned(),
        ]),
        PROVED,
        &["open-concept"],
    );
    let certificate = certificate_json(&exported);
    let root = certificate.root.expect("the closed conclusion is proved");
    let obligation = certificate
        .open_obligations
        .iter()
        .find(|obligation| obligation.kind == ObligationKind::OpenConcept)
        .unwrap_or_else(|| panic!("no open-concept obligation: {certificate:?}"));
    let dependency = certificate
        .nodes
        .iter()
        .position(
            |node| matches!(node, CertNode::RuleApplication { rule, .. } if rule == "重大推定"),
        )
        .expect("the rule concluding 「重大」 is a proof node");
    assert_eq!(
        obligation.nodes,
        vec![dependency],
        "only the node that states the open concept is listed"
    );
    assert_ne!(
        dependency, root,
        "the closed root conclusion is not itself a dependency"
    );
    assert!(
        !stdout(&why).contains("推导已通过独立校验。"),
        "a closed root over a decided open concept is not unconditional"
    );
}

/// The judgement reads the kernel term, not the printed head: a rule that
/// concludes a `def` alias of the open predicate (`重大情节` = `重大 x`) still
/// depends on 「重大」, although its written conclusion head is not the marked
/// name.
const OPEN_CONCEPT_ALIAS_CASE: &str = r#"sort 人
pred 损害 : 人 → Prop
pred 重大 : 人 → Prop
def 重大情节 : 人 → Prop := λ (x : 人) := 重大 x
obj 甲 : 人
open 重大
axiom 损害事实 : 损害 甲
  source text "案件" locator "一"
rule 别名推定 :
  params x : 人
  premise 损害 x
  conclude 重大情节 x
  source text "测试" locator "二"
"#;

/// A closed conclusion reached through a `def` alias of an open predicate is
/// still a decided open concept: the head is compared after kernel
/// normalization, so text that merely differs is not compared.
#[test]
fn a_def_alias_of_an_open_concept_is_still_the_concept() {
    let temp = TempDir::new("alias");
    let theory = temp.write("case.std", OPEN_CONCEPT_ALIAS_CASE);
    let path = theory.display().to_string();

    let why = check(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":why 重大情节 甲".to_owned(),
        ]),
        GAP,
        &["▸ 重大情节 甲", "此处需人判断：`重大`"],
    );
    assert!(
        !stdout(&why).contains("推导已通过独立校验。"),
        "the alias conclusion must not be an unconditional proof:\n{}",
        stdout(&why)
    );
    let exported = check(
        run(&[
            "--no-default-packs".to_owned(),
            path,
            ":cert 重大情节 甲".to_owned(),
        ]),
        PROVED,
        &["open-concept"],
    );
    let certificate = certificate_json(&exported);
    let obligation = certificate
        .open_obligations
        .iter()
        .find(|obligation| obligation.kind == ObligationKind::OpenConcept)
        .unwrap_or_else(|| panic!("no open-concept obligation: {certificate:?}"));
    assert_eq!(
        obligation.description, "开放概念 `重大` 需要人判断，不得当作已证明",
        "the concept is the normalized head, not the alias name"
    );
}

/// An open concept derived on a branch the root does not use leaves the root
/// untouched: the judgement follows the root's proof graph, it does not scan
/// every node or the whole environment.
#[test]
fn a_closed_goal_is_not_affected_by_an_open_concept_on_an_unrelated_branch() {
    let temp = TempDir::new("unrelated");
    let theory = temp.write("case.std", OPEN_CONCEPT_CASE);
    let path = theory.display().to_string();

    let why = check(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":why 轻伤 甲".to_owned(),
        ]),
        PROVED,
        &["推导已通过独立校验。"],
    );
    assert!(
        !stdout(&why).contains("此处需人判断"),
        "the unrelated open concept must not reach the root:\n{}",
        stdout(&why)
    );

    let exported = check(
        run(&[
            "--no-default-packs".to_owned(),
            path,
            ":cert 轻伤 甲".to_owned(),
        ]),
        PROVED,
        &[],
    );
    let certificate = certificate_json(&exported);
    assert!(
        certificate.open_obligations.is_empty(),
        "the closed root records no open-concept obligation: {:?}",
        certificate.open_obligations
    );
    // The unrelated rule step is still part of the derivation graph; the
    // absence of the obligation is about the root, not about the graph.
    assert!(
        certificate.nodes.iter().any(
            |node| matches!(node, CertNode::RuleApplication { rule, .. } if rule == "重大推定")
        ),
        "the fixture must derive 「重大」 on the unrelated branch: {:?}",
        certificate.nodes
    );
}

/// A fact the user supplied is evidence, not a decision of the concept: a rule
/// that consumes `重大 甲` as an assumed fact does not make its closed
/// conclusion depend on an open concept.
#[test]
fn an_open_concept_supplied_as_a_fact_is_not_a_dependency() {
    let temp = TempDir::new("fact-premise");
    let theory = temp.write("case.std", &open_concept_case_with_the_fact());
    let path = theory.display().to_string();

    let why = check(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":why 从重处罚 甲".to_owned(),
        ]),
        PROVED,
        &["推导已通过独立校验。"],
    );
    assert!(
        !stdout(&why).contains("此处需人判断"),
        "a supplied open-concept fact is not a booleanized concept:\n{}",
        stdout(&why)
    );

    let exported = check(
        run(&[
            "--no-default-packs".to_owned(),
            path,
            ":cert 从重处罚 甲".to_owned(),
        ]),
        PROVED,
        &[],
    );
    let certificate = certificate_json(&exported);
    assert!(
        certificate.open_obligations.is_empty(),
        "a premise fact states the concept; it does not decide it: {:?}",
        certificate.open_obligations
    );
}

/// Two processes generating the certificate for the same case must produce
/// byte-identical JSON: the obligation id, its description and the node order
/// are deterministic.
#[test]
fn regenerating_the_certificate_is_byte_identical_across_processes() {
    let temp = TempDir::new("deterministic");
    let theory = temp.write("case.std", OPEN_CONCEPT_CASE);
    let path = theory.display().to_string();

    let first = check(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":cert 从重处罚 甲".to_owned(),
        ]),
        PROVED,
        &["open-concept"],
    );
    let second = check(
        run(&[
            "--no-default-packs".to_owned(),
            path,
            ":cert 从重处罚 甲".to_owned(),
        ]),
        PROVED,
        &["open-concept"],
    );
    assert_eq!(
        certificate_text(&first),
        certificate_text(&second),
        "the certificate (including the obligation) must not depend on the process"
    );
    assert_eq!(
        certificate_json(&first).open_obligations,
        certificate_json(&second).open_obligations
    );
}

/// `:verify-cert` reports the obligation and exits `1`; a certificate that
/// drops the obligation would make an open concept look proved, so the checker
/// recomputes it from the environment and rejects the file (`2`).
#[test]
fn verify_cert_reports_the_obligation_and_rejects_a_certificate_that_drops_it() {
    let temp = TempDir::new("verify-open");
    let theory = temp.write("case.std", OPEN_CONCEPT_CASE);
    let path = theory.display().to_string();
    let exported = check(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":cert 重大 甲".to_owned(),
        ]),
        PROVED,
        &["open-concept"],
    );
    let certificate = certificate_json(&exported);
    let file = temp.write("certificate.json", &certificate.to_json_pretty().unwrap());
    let verify = check(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            format!(":verify-cert {}", file.display()),
        ]),
        GAP,
        &[
            "环境校验：通过",
            "逻辑校验：通过",
            "需人判断：是（open_obligations 1 项：开放概念 1 项）",
            "此处需人判断：`重大`",
        ],
    );
    assert!(
        !stdout(&verify).contains("推导已通过独立校验。"),
        ":verify-cert must not report an open-concept root as an unconditional proof"
    );

    // Dropping the obligation is the forgery the check exists for.
    let mut dropped = certificate.clone();
    dropped
        .open_obligations
        .retain(|obligation| obligation.kind != ObligationKind::OpenConcept);
    let dropped_file = temp.write("dropped.json", &dropped.to_json_pretty().unwrap());
    let rejected = check(
        run(&[
            "--no-default-packs".to_owned(),
            path,
            format!(":verify-cert {}", dropped_file.display()),
        ]),
        ERROR,
        &["逻辑校验：失败", "开放概念", "没有记录开放概念义务"],
    );
    assert!(
        stderr(&rejected).contains("开放概念"),
        "the error must name what is missing:\n{}",
        stderr(&rejected)
    );
}

/// A certificate that records an open-concept obligation its proof does not
/// support is rejected too: the obligation is derived data, not a note the
/// writer may add.
#[test]
fn a_certificate_with_an_invented_obligation_is_rejected() {
    let temp = TempDir::new("invented-open");
    let theory = temp.write("case.std", OPEN_CONCEPT_CASE);
    let path = theory.display().to_string();
    let exported = check(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":cert 轻伤 甲".to_owned(),
        ]),
        PROVED,
        &[],
    );
    let mut certificate = certificate_json(&exported);
    assert!(certificate.open_obligations.is_empty());

    certificate.open_obligations.push(OpenObligation {
        id: "open-concept".to_owned(),
        kind: ObligationKind::OpenConcept,
        description: "开放概念 `重大` 需要人判断，不得当作已证明".to_owned(),
        nodes: Vec::new(),
    });
    let file = temp.write("invented.json", &certificate.to_json_pretty().unwrap());
    check(
        run(&[
            "--no-default-packs".to_owned(),
            path,
            format!(":verify-cert {}", file.display()),
        ]),
        ERROR,
        &["逻辑校验：失败", "开放概念", "不能手工添加"],
    );
}

/// A marker occupies a ledger slot, so a session fact must not be numbered by
/// the ledger length: otherwise adding `open` would rename `:given` facts and
/// change `:why` output for reasons that have nothing to do with the marker.
///
/// The queried root is the open concept itself, so the query now exits `1` with
/// the "needs human judgement" notice (M2-9b). The naming assertion is what
/// this test is about and is unchanged.
#[test]
fn a_given_fact_name_does_not_shift_when_a_marker_is_added() {
    let temp = TempDir::new("given-name");
    let base = "sort 人\n\
                pred 损害 : 人 → Prop\n\
                obj 甲 : 人\n";
    let marked = format!("{base}open 损害\n");
    let _plain = temp.write("plain-given.std", base);
    let opened = temp.write("opened-given.std", &marked);

    let opened_out = check(
        run(&[
            "--no-default-packs".to_owned(),
            opened.display().to_string(),
            ":given 损害 甲".to_owned(),
            ":why 损害 甲".to_owned(),
        ]),
        GAP,
        &["已加载", "+ open 损害", "此处需人判断：`损害`"],
    );
    let text = stdout(&opened_out);
    assert!(
        text.contains("[已知1]"),
        "the first session fact must stay `已知1` with the marker present:\n{text}"
    );
    assert!(
        !text.contains("[已知2]"),
        "the marker must not consume a session-fact name:\n{text}"
    );
}

/// `:issues` instantiates rules over declared constants. An `open` marker is a
/// metadata declaration of type `Type`, not a term a parameter can take:
/// without the skip in the constant enumeration it would surface as
/// `概念 open:<predicate>` inside a `Type`-parameter rule.
#[test]
fn issues_does_not_enumerate_open_markers_as_constants() {
    let temp = TempDir::new("issues-open");
    let source = "sort 人\n\
                  pred 重大 : 人 → Prop\n\
                  open 重大\n\
                  pred 集合 : Type → Prop\n\
                  obj 甲 : 人\n\
                  rule 全体 :\n\
                    params T : Type\n\
                    premise 集合 T\n\
                    conclude 集合 T\n\
                    source text \"测试\" locator \"一\"\n";
    let theory = temp.write("issues-open.std", source);
    let output = check(
        run(&[
            "--no-default-packs".to_owned(),
            theory.display().to_string(),
            ":issues".to_owned(),
        ]),
        GAP,
        &["已加载"],
    );
    let text = stdout(&output);
    assert!(
        !text.contains("open:"),
        "the marker must not be enumerated as a constant:\n{text}"
    );
}

// ---------------------------------------------------------------------------
// Interpretation applications, several concepts, a nullary predicate
// ---------------------------------------------------------------------------

/// The open concept is licensed by an enabled interpretation, not by a rule:
/// the proof step that states it is an `interpretation_application`.
const OPEN_CONCEPT_INTERPRETATION_CASE: &str = r#"sort 人
pred 损害 : 人 → Prop
pred 重大 : 人 → Prop
obj 甲 : 人
open 重大
axiom 损害事实 : 损害 甲
  source text "案件" locator "一"
interpret 重大解释 : 损害 甲 → 重大 甲
  direction literal
  source text "解释文本" locator "二" version "2020"
"#;

/// An interpretation that licenses an open concept **is** the human reading:
/// the certificate records no obligation for its application node, the query
/// passes both layers, and the trust label is `依赖假设`. Without the enabled
/// interpretation the same goal is a gap and exits `1`; a rule-proved variant
/// of the same concept, which no interpretation licenses, keeps the notice and
/// the obligation.
///
/// The last part removes the interpretation step by hand and re-points the root
/// at an asserted fact stating the concept: the obligation reappears, so the
/// release depends on the evidence on the proof graph, not on a flag.
#[test]
fn an_interpretation_that_licenses_an_open_concept_releases_the_obligation() {
    let temp = TempDir::new("interpretation");
    let theory = temp.write("case.std", OPEN_CONCEPT_INTERPRETATION_CASE);
    let path = theory.display().to_string();
    let query = |command: &str| {
        run(&[
            "--no-default-packs".to_owned(),
            "--interpret".to_owned(),
            "重大解释".to_owned(),
            path.clone(),
            command.to_owned(),
        ])
    };

    // Without the interpretation the concept was never proved: gap, exit 1.
    let without = check(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":why 重大 甲".to_owned(),
        ]),
        GAP,
        &["证书有效，但根为缺口，结论未被证明。"],
    );
    assert!(
        !stdout(&without).contains("此处需人判断"),
        "a gap root has no open-concept dependency to report:\n{}",
        stdout(&without)
    );

    // A rule-proved open concept that no interpretation licenses is still a
    // pending human judgement: the notice and the obligation remain.
    let rule_case = temp.write("rule.std", OPEN_CONCEPT_CASE);
    let still_pending = check(
        run(&[
            "--no-default-packs".to_owned(),
            rule_case.display().to_string(),
            ":why 重大 甲".to_owned(),
        ]),
        GAP,
        &["此处需人判断：`重大`", "仍有未决义务"],
    );
    assert!(
        !stdout(&still_pending).contains("推导已通过独立校验。"),
        "a rule still states the concept and needs a human:\n{}",
        stdout(&still_pending)
    );

    // Enabling a sourced interpretation is the human reading: no obligation.
    let why = check(
        query(":why 重大 甲"),
        PROVED,
        &[
            "▸ 重大 甲  〈解释 重大解释（literal）〉",
            "推导已通过独立校验。",
            "信任：依赖假设",
        ],
    );
    assert!(
        !stdout(&why).contains("此处需人判断"),
        "a licensed open concept is no longer a pending human judgement:\n{}",
        stdout(&why)
    );
    let explain = check(
        query(":explain 重大 甲"),
        PROVED,
        &["根据解释「重大解释」", "依赖假设"],
    );
    assert!(
        !stdout(&explain).contains("此处需人判断"),
        "the narrative must not print the notice after the release:\n{}",
        stdout(&explain)
    );

    let exported = check(query(":cert 重大 甲"), PROVED, &[]);
    let certificate = certificate_json(&exported);
    assert!(
        certificate.open_obligations.is_empty(),
        "an interpretation-licensed open concept records no obligation: {:?}",
        certificate.open_obligations
    );
    let interpreted = certificate
        .nodes
        .iter()
        .position(|node| matches!(node, CertNode::InterpretationApplication { .. }))
        .expect("the interpretation step is a proof node");
    assert_eq!(
        certificate.root,
        Some(interpreted),
        "the released concept is licensed by the interpretation application"
    );

    let file = temp.write("certificate.json", &certificate.to_json_pretty().unwrap());
    let verify = check(
        run(&[
            "--no-default-packs".to_owned(),
            "--interpret".to_owned(),
            "重大解释".to_owned(),
            path.clone(),
            format!(":verify-cert {}", file.display()),
        ]),
        PROVED,
        &[
            "环境校验：通过",
            "逻辑校验：通过",
            "需人判断：否（无未决义务）",
        ],
    );
    assert!(
        !stdout(&verify).contains("此处需人判断"),
        "the released certificate must not report a pending concept:\n{}",
        stdout(&verify)
    );

    // Removing the interpretation step means the concept is no longer licensed
    // by a sourced reading: the checker requires the obligation again.
    let mut forged = certificate.clone();
    forged.assumptions.push(Assumption {
        proposition: cert_expr(&["重大", "甲"]),
        identity: FactIdentity::UserAsserted,
        sources: Vec::new(),
        label: None,
        occurred_at: std_deduce_cert::Explicit::none(),
        occurred_in: std_deduce_cert::Explicit::none(),
    });
    forged.nodes = vec![CertNode::Assumption {
        assumption: forged.assumptions.len() - 1,
    }];
    forged.interpretations.clear();
    forged.root = Some(0);
    forged.alternatives.clear();
    forged.conflicts.clear();
    forged.open_obligations.clear();
    let forged_file = temp.write("forged.json", &forged.to_json_pretty().unwrap());
    let rejected = check(
        run(&[
            "--no-default-packs".to_owned(),
            "--interpret".to_owned(),
            "重大解释".to_owned(),
            path,
            format!(":verify-cert {}", forged_file.display()),
        ]),
        ERROR,
        &["逻辑校验：失败", "没有记录开放概念义务"],
    );
    assert!(
        stderr(&rejected).contains("开放概念"),
        "the error must name what the missing obligation is about:\n{}",
        stderr(&rejected)
    );
}

/// An application item such as `重大 甲`, as a certificate expression.
fn cert_expr(parts: &[&str]) -> std_deduce_cert::CertExpr {
    let mut expression = std_deduce_kernel::Expr::constant(parts[0]);
    for part in &parts[1..] {
        expression =
            std_deduce_kernel::Expr::app(expression, std_deduce_kernel::Expr::constant(part));
    }
    std_deduce_cert::CertExpr::try_from(expression).expect("the expression is encodable")
}

/// Two open concepts on one root derivation: one obligation, both concepts
/// joined with `、` and sorted by name, so the description does not depend on
/// node order.
const OPEN_CONCEPT_MULTI_CASE: &str = r#"sort 人
pred 损害 : 人 → Prop
pred 重大 : 人 → Prop
pred 情节严重 : 人 → Prop
pred 从重处罚 : 人 → Prop
obj 甲 : 人
open 重大
open 情节严重
axiom 损害事实 : 损害 甲
  source text "案件" locator "一"
rule 重大推定 :
  params x : 人
  premise 损害 x
  conclude 重大 x
  source text "测试" locator "二"
rule 严重推定 :
  params x : 人
  premise 损害 x
  conclude 情节严重 x
  source text "测试" locator "三"
rule 从重 :
  params x : 人
  premise 重大 x
  premise 情节严重 x
  conclude 从重处罚 x
  source text "测试" locator "四"
"#;

#[test]
fn one_obligation_names_every_open_concept_in_name_order() {
    let temp = TempDir::new("multi");
    let theory = temp.write("case.std", OPEN_CONCEPT_MULTI_CASE);
    let exported = check(
        run(&[
            "--no-default-packs".to_owned(),
            theory.display().to_string(),
            ":cert 从重处罚 甲".to_owned(),
        ]),
        PROVED,
        &["open-concept"],
    );
    let certificate = certificate_json(&exported);
    assert_eq!(certificate.open_obligations.len(), 1);
    let obligation = &certificate.open_obligations[0];
    assert_eq!(
        obligation.description, "开放概念 `情节严重`、`重大` 需要人判断，不得当作已证明",
        "concepts are joined with 、 in name order, independent of node order"
    );
    let mut expected = [
        certificate
            .nodes
            .iter()
            .position(
                |node| matches!(node, CertNode::RuleApplication { rule, .. } if rule == "严重推定"),
            )
            .expect("the 「情节严重」 step is a proof node"),
        certificate
            .nodes
            .iter()
            .position(
                |node| matches!(node, CertNode::RuleApplication { rule, .. } if rule == "重大推定"),
            )
            .expect("the 「重大」 step is a proof node"),
    ];
    expected.sort_unstable();
    assert_eq!(
        obligation.nodes, expected,
        "both dependency nodes are listed in ascending node order"
    );
}

/// A nullary open predicate (`pred P : Prop`) takes the same path: the head of
/// `P` is the constant itself, and the certificate/verification round trip
/// reports the obligation.
const OPEN_CONCEPT_ZERO_CASE: &str = r#"pred P : Prop
open P
rule 推出P :
  conclude P
  source text "测试" locator "一"
"#;

#[test]
fn a_nullary_open_predicate_round_trips_through_cert_and_verify() {
    let temp = TempDir::new("nullary");
    let theory = temp.write("case.std", OPEN_CONCEPT_ZERO_CASE);
    let path = theory.display().to_string();
    let exported = check(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":cert P".to_owned(),
        ]),
        PROVED,
        &["open-concept"],
    );
    let certificate = certificate_json(&exported);
    let root = certificate.root.expect("the root is recorded");
    assert_eq!(certificate.open_obligations.len(), 1);
    assert_eq!(certificate.open_obligations[0].nodes, vec![root]);
    assert_eq!(
        certificate.open_obligations[0].description,
        "开放概念 `P` 需要人判断，不得当作已证明"
    );

    let file = temp.write("certificate.json", &certificate.to_json_pretty().unwrap());
    check(
        run(&[
            "--no-default-packs".to_owned(),
            path,
            format!(":verify-cert {}", file.display()),
        ]),
        GAP,
        &["逻辑校验：通过", "此处需人判断：`P`"],
    );
}

// ---------------------------------------------------------------------------
// A tampered obligation must be recomputed, not trusted
// ---------------------------------------------------------------------------

/// Export the open-concept fixture's certificate for `重大 甲` and write it
/// next to the theory. The obligation is assumed to be the generated one.
fn exported_open_certificate(temp: &TempDir, theory: &Path) -> (PathBuf, Certificate) {
    let exported = check(
        run(&[
            "--no-default-packs".to_owned(),
            theory.display().to_string(),
            ":cert 重大 甲".to_owned(),
        ]),
        PROVED,
        &["open-concept"],
    );
    let certificate = certificate_json(&exported);
    let file = temp.write("certificate.json", &certificate.to_json_pretty().unwrap());
    (file, certificate)
}

/// Verify one certificate file against the loaded theory.
fn verify_certificate(theory: &Path, file: &Path) -> Output {
    run(&[
        "--no-default-packs".to_owned(),
        theory.display().to_string(),
        format!(":verify-cert {}", file.display()),
    ])
}

/// Assert that a `:verify-cert` run failed the logical layer (exit `2`) and,
/// on stderr, names what could be located from the certificate.
fn assert_verify_rejected(output: Output, needles: &[&str]) {
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    let err = stderr(&output);
    assert!(
        out.contains("逻辑校验：失败"),
        "expected a logical failure:\n{out}\n{err}"
    );
    for needle in needles {
        assert!(err.contains(needle), "stderr lacks {needle:?}:\n{err}");
    }
}

#[test]
fn an_open_concept_obligation_with_a_different_id_is_rejected() {
    let temp = TempDir::new("forged-id");
    let theory = temp.write("case.std", OPEN_CONCEPT_CASE);
    let (_, mut certificate) = exported_open_certificate(&temp, &theory);
    certificate.open_obligations[0].id = "open-concept-forged".to_owned();
    let file = temp.write("forged.json", &certificate.to_json_pretty().unwrap());
    assert_verify_rejected(
        verify_certificate(&theory, &file),
        &["不一致", "open-concept-forged"],
    );
}

#[test]
fn an_open_concept_obligation_with_an_edited_description_is_rejected() {
    let temp = TempDir::new("forged-description");
    let theory = temp.write("case.std", OPEN_CONCEPT_CASE);
    let (_, mut certificate) = exported_open_certificate(&temp, &theory);
    certificate.open_obligations[0].description =
        "开放概念 `重大` 需要人判断\n伪造：推导已通过独立校验。\u{1B}[31m".to_owned();
    let file = temp.write("forged.json", &certificate.to_json_pretty().unwrap());
    let output = verify_certificate(&theory, &file);
    let err = stderr(&output);
    assert_verify_rejected(output, &["不一致"]);
    assert!(
        !err.contains("\n伪造：推导已通过独立校验。"),
        "an injected newline in the description must not become its own line:\n{err}"
    );
    assert!(
        err.contains("\\n"),
        "the description must be escaped in the error message:\n{err}"
    );
}

#[test]
fn an_open_concept_obligation_with_different_nodes_is_rejected() {
    let temp = TempDir::new("forged-nodes");
    let theory = temp.write("case.std", OPEN_CONCEPT_CASE);
    let (_, mut certificate) = exported_open_certificate(&temp, &theory);
    certificate.open_obligations[0].nodes.clear();
    let file = temp.write("forged.json", &certificate.to_json_pretty().unwrap());
    assert_verify_rejected(verify_certificate(&theory, &file), &["不一致", "节点"]);
}

#[test]
fn two_open_concept_obligations_are_rejected() {
    let temp = TempDir::new("duplicate");
    let theory = temp.write("case.std", OPEN_CONCEPT_CASE);
    let (_, mut certificate) = exported_open_certificate(&temp, &theory);
    let duplicate = certificate.open_obligations[0].clone();
    certificate.open_obligations.push(duplicate);
    let file = temp.write("forged.json", &certificate.to_json_pretty().unwrap());
    assert_verify_rejected(verify_certificate(&theory, &file), &["只能记录一条"]);
}
