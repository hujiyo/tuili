//! End-to-end tests for rule guards (certificate v11).
//!
//! A guard is an instance condition: a comparison over the values a rule
//! instance binds that must hold for the rule to fire. These tests exercise the
//! syntax, the trigger semantics (`true` fires, `false` does not, all guards of
//! one rule conjunctive), the load-time rejections, the recorded certificate
//! evidence, the checker's independent recomputation, and the coexistence with
//! `unless`, applicability, `def` aliases, computed conclusions, multiple
//! witnesses and open concepts.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_cert::Certificate;

const PROVED: i32 = 0;
const GAP: i32 = 1;
const ERROR: i32 = 2;

fn examples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}

fn example(name: &str) -> PathBuf {
    let path = examples_dir().join(name);
    assert!(path.is_file(), "missing example file: {}", path.display());
    path
}

/// Run the CLI with leading options (`--jurisdiction` and friends must come
/// before the session commands).
fn run_with(options: &[&str], commands: Vec<String>) -> Output {
    let mut all: Vec<String> = options.iter().map(|option| option.to_string()).collect();
    all.extend(commands);
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .args(all)
        .output()
        .unwrap_or_else(|e| panic!("failed to run the CLI: {e}"))
}

fn run(commands: Vec<String>) -> Output {
    run_with(&[], commands)
}

fn session(name: &str, commands: &[String]) -> Output {
    let mut all = vec![format!(":load {}", example(name).display())];
    all.extend_from_slice(commands);
    run(all)
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

/// `:cert` prints its explanation lines first, so the certificate is the tail
/// starting at the first `{`.
fn certificate_text(output: &Output) -> String {
    let text = stdout(output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    text[start..].trim_end().to_owned()
}

fn certificate_json(output: &Output) -> Certificate {
    let text = certificate_text(output);
    Certificate::from_json(&text)
        .unwrap_or_else(|e| panic!("invalid certificate JSON:\n{e}\nstdout:\n{text}"))
}

fn temp_path(tag: &str, extension: &str) -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "std-deduce-guards-{}-{tag}-{n}.{extension}",
        std::process::id()
    ))
}

/// A file removed when the test ends (including on panic).
struct TempFile {
    path: PathBuf,
}

impl TempFile {
    fn new(tag: &str, extension: &str, contents: &str) -> Self {
        let path = temp_path(tag, extension);
        fs::write(&path, contents).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        TempFile { path }
    }

    fn path_text(&self) -> String {
        self.path.display().to_string()
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn session_with(file: &TempFile, commands: &[String]) -> Output {
    session_with_options(&[], file, commands)
}

fn session_with_options(options: &[&str], file: &TempFile, commands: &[String]) -> Output {
    let mut all = vec![format!(":load {}", file.path_text())];
    all.extend_from_slice(commands);
    run_with(options, all)
}

/// Rewrite a generated certificate and check it in a fresh process.
fn tamper(
    theory: &TempFile,
    options: &[&str],
    goal: &str,
    edit: impl FnOnce(&mut serde_json::Value),
) -> Output {
    let generated = session_with_options(options, theory, &[format!(":cert {goal}")]);
    assert_exit(&generated, PROVED);
    let mut value: serde_json::Value =
        serde_json::from_str(&certificate_text(&generated)).expect("the certificate is JSON");
    edit(&mut value);
    let text = serde_json::to_string_pretty(&value).expect("the edited certificate serializes");
    let file = TempFile::new("tampered", "json", &text);
    session_with_options(
        options,
        theory,
        &[format!(":verify-cert {} {goal}", file.path_text())],
    )
}

/// A guard held in the tree, printed from the certificate.
const GUARD_THEORY: &str = r#"
def 金额 : Type := Int
sort 人
obj 甲 : 人
obj 乙 : 人
pred 医疗费 : 人 → 金额 → Prop
pred 重大 : 人 → 金额 → Prop
axiom 甲医疗费 : 医疗费 甲 9000
  source text "测试" locator "甲"
axiom 乙医疗费 : 医疗费 乙 3000
  source text "测试" locator "乙"
rule 重大认定 :
  params p : 人, a : 金额
  premise 医疗费 p a
  guard (le 100 a)
  guard (le a 5000)
  conclude 重大 p a
  source text "测试" locator "两条守卫"
"#;

/// Closed guards and a guard whose `def` alias operand is unfolded.
const CLOSED_GUARD_THEORY: &str = r#"
def 金额 : Type := Int
def 门槛 : 金额 := 5000
sort 人
obj 甲 : 人
pred 已立案 : 人 → Prop
pred 须移送 : 人 → Prop
pred 不得移送 : 人 → Prop
axiom 甲立案 : 已立案 甲
  source text "测试" locator "立案"
rule 常真 :
  params p : 人
  premise 已立案 p
  guard (le 3000 门槛)
  conclude 须移送 p
  source text "测试" locator "常真"
rule 常假 :
  params p : 人
  premise 已立案 p
  guard (le 5000 3000)
  conclude 不得移送 p
  source text "测试" locator "常假"
"#;

/// Guard plus `unless`, applicability, a `def` alias, a computed conclusion,
/// multiple witnesses and an open concept.
const CROSS_FEATURE_THEORY: &str = r#"
def 金额 : Type := Int
def 门槛 : 金额 := 5000
sort 人
obj 甲 : 人
pred 医疗费 : 人 → 金额 → Prop
pred 误工费 : 人 → 金额 → Prop
pred 排除 : 人 → Prop
pred 合计 : 人 → 金额 → Prop
pred 须复核 : 人 → Prop
axiom 医疗费事实 : 医疗费 甲 6000
  identity verified
  occurred_at 2024-05-01
  source text "测试卷宗" locator "医疗费" version "2024"
axiom 误工费事实 : 误工费 甲 2000
  identity verified
  occurred_at 2024-05-01
  source text "测试卷宗" locator "误工费" version "2024"
rule 复核规则 :
  params p : 人, a : 金额, b : 金额
  premise 医疗费 p a
  premise 误工费 p b
  guard (le 门槛 (a + b))
  unless 排除 p
  effective 2020-01-01
  repealed 2025-01-01
  jurisdiction CN
  conclude 须复核 p
  source text "测试法" locator "复核"
rule 合计规则 :
  params p : 人, a : 金额, b : 金额
  premise 医疗费 p a
  premise 误工费 p b
  guard (le 门槛 (a + b))
  conclude 合计 p (a + b)
  source text "测试法" locator "合计"
rule 合计别名 :
  params p : 人, a : 金额, b : 金额
  premise 医疗费 p a
  premise 误工费 p b
  conclude 合计 p (b + a)
  source text "测试法" locator "括号交换"
"#;

// ---------------------------------------------------------------- examples

#[test]
fn the_example_shows_a_guard_that_holds_and_one_that_does_not() {
    // 甲 9000: `(le 5000 9000)` holds, so the rule fires and the form tree
    // prints the judgement after the rule line.
    let proved = session("守卫-重大金额.std", &[":why 重大 甲 9000".into()]);
    assert_exit(&proved, PROVED);
    let out = stdout(&proved);
    assert!(
        out.contains("守卫：`(le 5000 9000)` = true"),
        "the held guard must be printed: {out}"
    );
    assert!(out.contains("推导已通过独立校验。"), "{out}");
    // The tree is otherwise unchanged: no other guard line and the ordinary
    // instance line is still there.
    assert_eq!(out.matches("守卫：").count(), 1, "{out}");

    // 乙 3000: the guard is false, so the goal is a gap and the gap says why.
    let gap = session("守卫-重大金额.std", &[":gap 重大 乙 3000".into()]);
    assert_exit(&gap, GAP);
    let out = stdout(&gap);
    assert!(
        out.contains("守卫：`(le 5000 3000)` 不成立，故本规则不触发"),
        "a false guard must be named as the reason: {out}"
    );
}

#[test]
fn a_failed_guard_is_the_reason_a_dependent_goal_is_a_gap() {
    // 从重处理 depends on 重大; 重大认定's guard is false for 3000, so the
    // nested gap names the guard instead of only saying "no derivation".
    let gap = session("守卫-金额不足-缺口.std", &[":gap 从重处理 甲 3000".into()]);
    assert_exit(&gap, GAP);
    let out = stdout(&gap);
    assert!(out.contains("缺 ⟨重大 甲 3000⟩"), "{out}");
    assert!(
        out.contains("守卫：`(le 5000 3000)` 不成立，故本规则不触发"),
        "the nested gap must name the failed guard: {out}"
    );
}

#[test]
fn issues_names_the_guard_as_the_reason_too() {
    // `:issues` renders the same gap tree, so the guard's failure appears in
    // the scan as well and the candidate does not silently disappear. A closed
    // guard is used because `:issues` never enumerates numeric parameters (a
    // documented boundary), while an object parameter can be enumerated from
    // the declared constants.
    let theory = TempFile::new("issues-guard", "std", CLOSED_GUARD_THEORY);
    let scan = session_with(&theory, &[":issues".into()]);
    assert_exit(&scan, GAP);
    let out = stdout(&scan);
    assert!(out.contains("争点 ⟨不得移送 甲⟩"), "{out}");
    assert!(
        out.contains("守卫：`(le 5000 3000)` 不成立，故本规则不触发"),
        "the issue scan must print the failed guard: {out}"
    );
}

// ------------------------------------------------------- trigger semantics

#[test]
fn all_guards_of_one_rule_must_hold() {
    let theory = TempFile::new("multi-guard", "std", GUARD_THEORY);
    // 3000 satisfies both guards.
    let proved = session_with(&theory, &[":why 重大 乙 3000".into()]);
    assert_exit(&proved, PROVED);
    let out = stdout(&proved);
    assert!(out.contains("守卫：`(le 100 3000)` = true"), "{out}");
    assert!(out.contains("守卫：`(le 3000 5000)` = true"), "{out}");
    assert!(out.contains("推导已通过独立校验。"), "{out}");

    // 9000 satisfies the first guard only: the conjunction fails, so the rule
    // does not fire and the gap names the failing guard.
    let gap = session_with(&theory, &[":gap 重大 甲 9000".into()]);
    assert_exit(&gap, GAP);
    let out = stdout(&gap);
    assert!(out.contains("守卫：`(le 9000 5000)` 不成立"), "{out}");
}

#[test]
fn a_closed_guard_holds_regardless_of_the_bindings() {
    let theory = TempFile::new("closed-guard", "std", CLOSED_GUARD_THEORY);
    // `guard (le 3000 门槛)` mentions no parameter: `门槛` is a `def` alias of
    // 5000, unfolded when the comparison is evaluated.
    let proved = session_with(&theory, &[":why 须移送 甲".into()]);
    assert_exit(&proved, PROVED);
    let out = stdout(&proved);
    assert!(out.contains("守卫：`(le 3000 门槛)` = true"), "{out}");

    // A closed guard that is false never lets the rule fire.
    let gap = session_with(&theory, &[":gap 不得移送 甲".into()]);
    assert_exit(&gap, GAP);
    let out = stdout(&gap);
    assert!(out.contains("守卫：`(le 5000 3000)` 不成立"), "{out}");
}

#[test]
fn a_parameter_guard_is_judged_per_instance() {
    // The same rule fires for one binding and not for another: the guard is
    // judged per instance, never once per rule.
    let theory = TempFile::new("per-instance", "std", GUARD_THEORY);
    let first = session_with(&theory, &[":why 重大 乙 3000".into()]);
    assert_exit(&first, PROVED);
    let second = session_with(&theory, &[":gap 重大 甲 9000".into()]);
    assert_exit(&second, GAP);
    // Both instances exist; only the guard decides which one fires.
    let both = session_with(&theory, &[":cert 重大 乙 3000".into()]);
    assert_exit(&both, PROVED);
}

// --------------------------------------------------------- load rejections

#[test]
fn an_unbound_free_variable_in_a_guard_is_rejected_at_load() {
    let theory = TempFile::new(
        "guard-free-name",
        "std",
        r#"
def 金额 : Type := Int
sort 人
pred 医疗费 : 人 → 金额 → Prop
pred 重大 : 人 → 金额 → Prop
rule 重大认定 :
  params p : 人, a : 金额
  premise 医疗费 p a
  guard (le b 5000)
  conclude 重大 p a
  source text "测试" locator "规则"
"#,
    );
    let output = session_with(&theory, &[]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(
        err.contains(":9:3: error:"),
        "the position must be named: {err}"
    );
    assert!(err.contains("`rule 重大认定`"), "{err}");
    assert!(err.contains("未绑定的自由变量 `b`"), "{err}");
}

#[test]
fn a_guard_that_is_not_a_comparison_is_rejected_at_load() {
    let theory = TempFile::new(
        "guard-not-comparison",
        "std",
        r#"
def 金额 : Type := Int
sort 人
pred 医疗费 : 人 → 金额 → Prop
pred 重大 : 人 → 金额 → Prop
rule 重大认定 :
  params p : 人, a : 金额
  premise 医疗费 p a
  guard 3000
  conclude 重大 p a
  source text "测试" locator "规则"
"#,
    );
    let output = session_with(&theory, &[]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(
        err.contains(":9:3: error:"),
        "the position must be named: {err}"
    );
    assert!(err.contains("`rule 重大认定`"), "{err}");
    assert!(err.contains("守卫必须以比较 `less` / `le` 打头"), "{err}");
}

#[test]
fn a_guard_may_not_judge_a_premise_proof() {
    let theory = TempFile::new(
        "guard-premise-binder",
        "std",
        r#"
def 金额 : Type := Int
sort 人
pred 医疗费 : 人 → 金额 → Prop
pred 重大 : 人 → 金额 → Prop
rule 重大认定 :
  params p : 人, a : 金额
  premise h : 医疗费 p a
  guard (le h 5000)
  conclude 重大 p a
  source text "测试" locator "规则"
"#,
    );
    let output = session_with(&theory, &[]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("`rule 重大认定`"), "{err}");
    assert!(err.contains("守卫引用了前提绑定 `h`"), "{err}");
}

#[test]
fn a_guard_parameter_that_no_premise_fixes_is_rejected_at_load() {
    let theory = TempFile::new(
        "guard-unbound-param",
        "std",
        r#"
def 金额 : Type := Int
sort 人
pred 医疗费 : 人 → 金额 → Prop
pred 重大 : 人 → 金额 → Prop
rule 重大认定 :
  params p : 人, a : 金额, b : 金额
  premise 医疗费 p a
  guard (le b 5000)
  conclude 重大 p a
  source text "测试" locator "规则"
"#,
    );
    let output = session_with(&theory, &[]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("`rule 重大认定`"), "{err}");
    assert!(err.contains("参数 `b` 出现在守卫里"), "{err}");
}

#[test]
fn a_guard_must_start_its_own_line() {
    // A guard crammed onto the rule header's line is refused instead of being
    // read as part of the previous clause.
    let theory = TempFile::new(
        "guard-same-line",
        "std",
        r#"
def 金额 : Type := Int
sort 人
pred 医疗费 : 人 → 金额 → Prop
pred 重大 : 人 → 金额 → Prop
rule 重大认定 : guard (le a 5000)
  params p : 人, a : 金额
  premise 医疗费 p a
  conclude 重大 p a
  source text "测试" locator "规则"
"#,
    );
    let output = session_with(&theory, &[]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("`rule 重大认定`"), "{err}");
    assert!(err.contains("`guard` 子句必须另起一行"), "{err}");
}

// ------------------------------------------------------- explicit arithmetic

#[test]
fn an_overflowing_guard_is_an_error_not_false() {
    let theory = TempFile::new(
        "guard-overflow",
        "std",
        r#"
def 金额 : Type := Int
sort 人
obj 甲 : 人
pred 医疗费 : 人 → 金额 → Prop
pred 重大 : 人 → 金额 → Prop
axiom 甲医疗费 : 医疗费 甲 3000
  source text "测试" locator "事实"
rule 重大认定 :
  params p : 人, a : 金额
  premise 医疗费 p a
  guard (le a 5000)
  guard (less (add 9223372036854775807 1) a)
  conclude 重大 p a
  source text "测试" locator "规则"
"#,
    );
    // The second guard overflows whatever `a` is. It must abort the reasoning
    // with an explicit error naming the rule and the guard, never be read as
    // "does not hold".
    let output = session_with(&theory, &[":why 重大 甲 3000".into()]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("规则 `重大认定` 的第 2 条守卫"), "{err}");
    assert!(err.contains("整数运算溢出"), "{err}");
    assert!(err.contains("守卫求值失败不当作 false"), "{err}");
}

// --------------------------------------------------------- certificate v11

#[test]
fn the_certificate_is_v11_and_records_each_guard() {
    let theory = TempFile::new("guard-cert", "std", GUARD_THEORY);
    let output = session_with(&theory, &[":cert 重大 乙 3000".into()]);
    assert_exit(&output, PROVED);
    let certificate = certificate_json(&output);
    assert_eq!(certificate.format_version.get(), 11);
    let step = certificate
        .nodes
        .iter()
        .find_map(|node| match node {
            std_deduce_cert::Node::RuleApplication { guards, .. } => Some(guards.clone()),
            _ => None,
        })
        .expect("the rule step is recorded");
    assert_eq!(step.len(), 2, "both guards must be recorded");
    for (index, record) in step.iter().enumerate() {
        assert_eq!(record.index, index);
        // The declared form keeps the parameter as a `?name` placeholder.
        let expression = format!("{:?}", record.expression);
        assert!(expression.contains("?a"), "{expression}");
        assert_eq!(record.holds.as_ref().copied(), Some(true));
    }
    // The second guard's substituted form is the guarded amount.
    assert!(
        format!("{:?}", step[1].instance).contains("3000"),
        "{:?}",
        step[1].instance
    );

    // The exported JSON is independently re-checked by a second process.
    let file = TempFile::new("guard-cert-file", "json", &certificate_text(&output));
    let verified = session_with(&theory, &[format!(":verify-cert {}", file.path_text())]);
    assert_exit(&verified, PROVED);
    let out = stdout(&verified);
    assert!(out.contains("逻辑校验：通过"), "{out}");
}

#[test]
fn a_v10_certificate_is_rejected_by_the_version_probe() {
    let theory = TempFile::new("guard-version", "std", GUARD_THEORY);
    let output = session_with(&theory, &[":cert 重大 乙 3000".into()]);
    assert_exit(&output, PROVED);
    let json = certificate_text(&output);
    let old = json.replace("\"format_version\": 11", "\"format_version\": 10");
    assert_ne!(old, json, "the fixture must record the version");
    let file = TempFile::new("version-ten", "json", &old);
    let verify = session_with(&theory, &[format!(":verify-cert {}", file.path_text())]);
    assert_exit(&verify, ERROR);
    assert!(
        stderr(&verify).contains("supports 11"),
        "{}",
        stderr(&verify)
    );
}

// --------------------------------------------------------------- tampering

#[test]
fn flipping_a_recorded_guard_to_false_is_rejected() {
    let theory = TempFile::new("tamper-flip", "std", GUARD_THEORY);
    let output = tamper(&theory, &[], "重大 乙 3000", |value| {
        let step = value["nodes"]
            .as_array_mut()
            .expect("nodes")
            .iter_mut()
            .find(|node| node["kind"] == "rule_application")
            .expect("rule step");
        step["guards"][0]["holds"] = serde_json::Value::from(false);
    });
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("节点 2"), "{out}");
    assert!(out.contains("第 1 条守卫"), "{out}");
    assert!(out.contains("记录的是 不成立（false）"), "{out}");
    assert!(out.contains("重算结果是 成立（true）"), "{out}");
}

#[test]
fn editing_a_recorded_guard_expression_is_rejected() {
    let theory = TempFile::new("tamper-expression", "std", GUARD_THEORY);
    let output = tamper(&theory, &[], "重大 乙 3000", |value| {
        let step = value["nodes"]
            .as_array_mut()
            .expect("nodes")
            .iter_mut()
            .find(|node| node["kind"] == "rule_application")
            .expect("rule step");
        // `le` -> `less`: the operator is part of the recorded judgement.
        step["guards"][1]["expression"]["func"]["func"]["name"] = serde_json::Value::from("less");
    });
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("节点 2"), "{out}");
    assert!(out.contains("第 2 条守卫的声明形式"), "{out}");
}

#[test]
fn editing_the_substituted_guard_form_is_rejected() {
    let theory = TempFile::new("tamper-instance", "std", GUARD_THEORY);
    let output = tamper(&theory, &[], "重大 乙 3000", |value| {
        let step = value["nodes"]
            .as_array_mut()
            .expect("nodes")
            .iter_mut()
            .find(|node| node["kind"] == "rule_application")
            .expect("rule step");
        step["guards"][1]["instance"]["func"]["arg"]["value"] = serde_json::Value::from(1000);
    });
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("节点 2"), "{out}");
    assert!(out.contains("第 2 条守卫按绑定得到的形态"), "{out}");
    assert!(out.contains("1000"), "{out}");
}

#[test]
fn removing_a_guard_record_is_rejected() {
    let theory = TempFile::new("tamper-drop", "std", GUARD_THEORY);
    let output = tamper(&theory, &[], "重大 乙 3000", |value| {
        let step = value["nodes"]
            .as_array_mut()
            .expect("nodes")
            .iter_mut()
            .find(|node| node["kind"] == "rule_application")
            .expect("rule step");
        step["guards"].as_array_mut().expect("guards").pop();
    });
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("节点 2"), "{out}");
    assert!(out.contains("声明了 2 条守卫，证书记录了 1 条"), "{out}");
}

#[test]
fn removing_the_whole_guard_table_is_rejected() {
    let theory = TempFile::new("tamper-drop-all", "std", GUARD_THEORY);
    let output = tamper(&theory, &[], "重大 乙 3000", |value| {
        let step = value["nodes"]
            .as_array_mut()
            .expect("nodes")
            .iter_mut()
            .find(|node| node["kind"] == "rule_application")
            .expect("rule step");
        step.as_object_mut().expect("node").remove("guards");
    });
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("节点 2"), "{out}");
    assert!(out.contains("声明了 2 条守卫，证书记录了 0 条"), "{out}");
}

#[test]
fn inventing_an_extra_guard_record_is_rejected() {
    let theory = TempFile::new("tamper-add", "std", GUARD_THEORY);
    let output = tamper(&theory, &[], "重大 乙 3000", |value| {
        let step = value["nodes"]
            .as_array_mut()
            .expect("nodes")
            .iter_mut()
            .find(|node| node["kind"] == "rule_application")
            .expect("rule step");
        let mut extra = step["guards"][1].clone();
        extra["index"] = serde_json::Value::from(2);
        step["guards"].as_array_mut().expect("guards").push(extra);
    });
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("节点 2"), "{out}");
    assert!(out.contains("声明了 2 条守卫，证书记录了 3 条"), "{out}");
}

#[test]
fn reordering_guard_records_is_rejected() {
    let theory = TempFile::new("tamper-order", "std", GUARD_THEORY);
    let output = tamper(&theory, &[], "重大 乙 3000", |value| {
        let step = value["nodes"]
            .as_array_mut()
            .expect("nodes")
            .iter_mut()
            .find(|node| node["kind"] == "rule_application")
            .expect("rule step");
        let guards = step["guards"].as_array_mut().expect("guards");
        guards.swap(0, 1);
        guards[0]["index"] = serde_json::Value::from(0);
        guards[1]["index"] = serde_json::Value::from(1);
    });
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("节点 2"), "{out}");
    assert!(out.contains("第 1 条守卫的声明形式"), "{out}");
}

#[test]
fn a_gap_candidates_false_guard_cannot_be_flipped_to_true() {
    let theory = TempFile::new("tamper-candidate", "std", GUARD_THEORY);
    // The candidate records `(le 9000 5000)` as false; the checker recomputes
    // it from the candidate's own bindings and refuses the flipped value.
    let generated = session_with(&theory, &[":cert 重大 甲 9000".into()]);
    let mut value: serde_json::Value =
        serde_json::from_str(&certificate_text(&generated)).expect("JSON");
    let gap = value["nodes"]
        .as_array_mut()
        .expect("nodes")
        .iter_mut()
        .find(|node| node["kind"] == "gap")
        .expect("gap root");
    let candidate = gap["candidates"].as_array_mut().expect("candidates");
    candidate[0]["guards"][1]["holds"] = serde_json::Value::from(true);
    let text = serde_json::to_string_pretty(&value).expect("serialize");
    let file = TempFile::new("flipped-candidate", "json", &text);
    let verify = session_with(&theory, &[format!(":verify-cert {}", file.path_text())]);
    assert_exit(&verify, ERROR);
    let out = stdout(&verify);
    // The gap certificate has no proved root, so the checker's failure (rather
    // than the ordinary unproved-root exit) is what must appear.
    assert!(out.contains("逻辑校验：失败"), "{out}");
    assert!(out.contains("第 2 条守卫"), "{out}");
}

// ---------------------------------------------------------- cross features

#[test]
fn a_guard_coexists_with_unless_applicability_aliases_computed_and_witnesses() {
    let theory = TempFile::new("cross-feature", "std", CROSS_FEATURE_THEORY);

    // Guard + `def` alias (`门槛`) + computed conclusion (`a + b`). The main
    // path is `合计别名` (sorted first by rule name); the guarded rule is the
    // recorded second witness, so the guard's own line is printed by the
    // `须复核` query below, where the guarded rule is the main path.
    let proved = session_with_options(
        &["--jurisdiction", "CN"],
        &theory,
        &[":why 合计 甲 8000".into()],
    );
    assert_exit(&proved, PROVED);
    let out = stdout(&proved);
    assert!(
        out.contains("计算：合计 甲 (add 2000 6000) = 合计 甲 8000"),
        "{out}"
    );
    // Two rules conclude the same total, so both witnesses are kept.
    assert!(out.contains("另有 1 条独立推导"), "{out}");
    assert!(out.contains("推导已通过独立校验。"), "{out}");

    // Guard + `unless` + applicability on the same rule: the guard holds and
    // the rule fires under the case's event time, with the guard's judgement
    // printed on the main path.
    let review = session_with_options(
        &["--jurisdiction", "CN"],
        &theory,
        &[":why 须复核 甲".into()],
    );
    assert_exit(&review, PROVED);
    let out = stdout(&review);
    assert!(
        out.contains("守卫：`(le 门槛 (add 6000 2000))` = true"),
        "{out}"
    );
    assert!(out.contains("适用（事件时间 2024-05-01"), "{out}");

    // The same certificate is independently re-checked with the same session
    // values, so a guard verdict cannot be hidden behind the in-memory tree.
    // The total has two witnesses; the certificate carries both rule steps.
    let cert = session_with_options(
        &["--jurisdiction", "CN"],
        &theory,
        &[":cert 合计 甲 8000".into()],
    );
    assert_exit(&cert, PROVED);
    let value: serde_json::Value =
        serde_json::from_str(&certificate_text(&cert)).expect("the certificate is JSON");
    let guarded = value["nodes"]
        .as_array()
        .expect("nodes")
        .iter()
        .find(|node| node["kind"] == "rule_application" && node["rule"] == "合计规则")
        .expect("the guarded witness is recorded");
    assert!(guarded["computed"].is_object(), "{guarded}");
    assert_eq!(
        guarded["guards"].as_array().expect("guards").len(),
        1,
        "{guarded}"
    );
    let file = TempFile::new("cross-feature-cert", "json", &certificate_text(&cert));
    let verified = session_with_options(
        &["--jurisdiction", "CN"],
        &theory,
        &[format!(":verify-cert {} 合计 甲 8000", file.path_text())],
    );
    assert_exit(&verified, PROVED);
    let out = stdout(&verified);
    assert!(out.contains("逻辑校验：通过"), "{out}");
    assert!(out.contains("内核证明：通过"), "{out}");

    // An `unless` that holds blocks the rule even though its guard would hold
    // once the premises bind the amounts: the goal binds only `p`, so the
    // guard is recorded as undecided (never as false) and the blocker is
    // printed as the explicit reason.
    let blocked = session_with_options(
        &["--jurisdiction", "CN"],
        &theory,
        &[":given 排除 甲".into(), ":gap 须复核 甲".into()],
    );
    assert_exit(&blocked, GAP);
    let out = stdout(&blocked);
    assert!(
        out.contains("被阻断：「排除 甲」〔用户陈述〕已成立"),
        "{out}"
    );
    assert!(
        out.contains("无法判定（守卫参数没有全部绑定"),
        "an undecided guard must not be reported as false: {out}"
    );
}

#[test]
fn a_guarded_rule_still_carries_its_open_concept_obligation() {
    let theory = TempFile::new(
        "guard-open-concept",
        "std",
        r#"
def 金额 : Type := Int
sort 人
obj 甲 : 人
pred 医疗费 : 人 → 金额 → Prop
pred 重大 : 人 → 金额 → Prop
open 重大
axiom 甲医疗费 : 医疗费 甲 9000
  source text "测试" locator "事实"
rule 重大认定 :
  params p : 人, a : 金额
  premise 医疗费 p a
  guard (le 5000 a)
  conclude 重大 p a
  source text "测试" locator "规则"
"#,
    );
    // The guard holds, so the rule fires; the conclusion is an open concept,
    // so the obligation is still generated and the query is not a clean proof.
    let output = session_with(&theory, &[":why 重大 甲 9000".into()]);
    assert_exit(&output, GAP);
    let out = stdout(&output);
    assert!(out.contains("守卫：`(le 5000 9000)` = true"), "{out}");
    assert!(out.contains("此处需人判断：`重大`"), "{out}");
    assert!(out.contains("开放概念"), "{out}");

    let cert = session_with(&theory, &[":cert 重大 甲 9000".into()]);
    let certificate = certificate_json(&cert);
    assert_eq!(certificate.open_obligations.len(), 1);
    assert!(
        certificate.open_obligations[0].description.contains("重大"),
        "{:?}",
        certificate.open_obligations
    );
    let file = TempFile::new("guard-open-cert", "json", &certificate_text(&cert));
    let verified = session_with(&theory, &[format!(":verify-cert {}", file.path_text())]);
    assert_exit(&verified, GAP);
    let out = stdout(&verified);
    assert!(out.contains("逻辑校验：通过"), "{out}");
    assert!(out.contains("需人判断：是"), "{out}");
}
