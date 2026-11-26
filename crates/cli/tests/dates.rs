//! End-to-end tests for calendar dates and date arithmetic (certificate v13).
//!
//! A `Date` is a term: `d"YYYY-MM-DD"`, the built-in sort `Date`, and four
//! operations evaluated by the kernel (`daysBetween`, `addDays`, `addMonths`,
//! `addYears`). These tests drive the real CLI binary: they pin the literal
//! syntax and its error positions, the calendar-aware month/year alignment,
//! the comparison overload, the limitation-period example, the v13 record and
//! the tamper rejections.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const GAP: i32 = 1;
/// A batch file that fails to load exits `1`; an in-session command error and a
/// failed certificate check exit `2`.
const LOAD_ERROR: i32 = 1;
const ERROR: i32 = 2;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn examples_dir() -> PathBuf {
    repo_root().join("examples")
}

fn example(name: &str) -> String {
    let path = examples_dir().join(name);
    assert!(path.is_file(), "missing example file: {}", path.display());
    path.to_string_lossy().into_owned()
}

/// Run the CLI from the repository root, so the default environment resolves.
fn run(commands: Vec<String>) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(commands)
        .output()
        .unwrap_or_else(|e| panic!("failed to run the CLI: {e}"))
}

fn session(name: &str, commands: &[String]) -> Output {
    let mut all = vec![format!(":load {}", example(name))];
    all.extend_from_slice(commands);
    run(all)
}

/// A theory file outside the repository, removed when the test ends.
struct TempTheory {
    path: PathBuf,
}

impl TempTheory {
    fn new(tag: &str, source: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-dates-{}-{tag}-{n}.std",
            std::process::id()
        ));
        fs::write(&path, source).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        TempTheory { path }
    }

    fn path_text(&self) -> String {
        self.path.display().to_string()
    }
}

impl Drop for TempTheory {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

/// A file removed when the test ends (including on panic).
struct TempFile {
    path: PathBuf,
}

impl TempFile {
    fn new(tag: &str, contents: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-dates-{}-{tag}-{n}.json",
            std::process::id()
        ));
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

fn exit_code(output: &Output) -> Option<i32> {
    output.status.code()
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// Assert the exit code and that stdout contains every needle.
fn check(output: Output, expected: i32, needles: &[&str]) -> Output {
    let code = exit_code(&output);
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(
        code,
        Some(expected),
        "expected exit {expected}, got {code:?}\nstdout:\n{out}\nstderr:\n{err}"
    );
    for needle in needles {
        assert!(
            out.contains(needle),
            "stdout does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

/// Assert the exit code and that stderr contains every needle.
fn check_stderr(output: Output, expected: i32, needles: &[&str]) -> Output {
    let code = exit_code(&output);
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(
        code,
        Some(expected),
        "expected exit {expected}, got {code:?}\nstdout:\n{out}\nstderr:\n{err}"
    );
    for needle in needles {
        assert!(
            err.contains(needle),
            "stderr does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

/// The certificate JSON of a `:cert` session, from the first `{` onward.
fn certificate_text(output: &Output) -> String {
    let text = stdout(output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    text[start..].trim_end().to_owned()
}

/// A theory that only evaluates closed date terms with `#check`.
fn checks(source: &str) -> Output {
    let theory = TempTheory::new("checks", source);
    let loaded = run(vec![theory.path_text()]);
    let out = stdout(&loaded);
    let err = stderr(&loaded);
    match exit_code(&loaded) {
        Some(0) | Some(2) => {}
        other => panic!("unexpected exit {other:?}\nstdout:\n{out}\nstderr:\n{err}"),
    }
    loaded
}

#[test]
fn the_four_date_operations_evaluate_on_literals() {
    let loaded = checks(
        r#"
#check (addYears d"2020-02-29" 1)
#check (addYears d"2020-02-29" 4)
#check (addMonths d"2020-01-31" 1)
#check (addMonths d"2021-01-31" 1)
#check (addDays d"2020-01-31" 1)
#check (daysBetween d"2020-01-01" d"2021-01-01")
#check (daysBetween d"2021-01-01" d"2020-01-01")
#check (less d"2020-01-01" d"2020-06-01")
"#,
    );
    check(
        loaded,
        PROVED,
        &[
            // A leap day stepped into a common year lands on 2 月's last day.
            r#"addYears d"2020-02-29" 1 : Date（求值：d"2021-02-28"）"#,
            // Four years later the day exists again.
            r#"addYears d"2020-02-29" 4 : Date（求值：d"2024-02-29"）"#,
            // 1 月 31 日 + 1 个月 = 该月最后一天（闰年 2 月 29 日 / 平年 2 月 28 日）。
            r#"addMonths d"2020-01-31" 1 : Date（求值：d"2020-02-29"）"#,
            r#"addMonths d"2021-01-31" 1 : Date（求值：d"2021-02-28"）"#,
            r#"addDays d"2020-01-31" 1 : Date（求值：d"2020-02-01"）"#,
            // 2020 是闰年：一整年是 366 天；反方向是 -366。
            r#"daysBetween d"2020-01-01" d"2021-01-01" : Int（求值：366）"#,
            r#"daysBetween d"2021-01-01" d"2020-01-01" : Int（求值：-366）"#,
            r#"less d"2020-01-01" d"2020-06-01" : Prop（求值：True）"#,
        ],
    );
}

/// Every impossible literal is a lexical error at the literal's own position.
///
/// The probe writes `#check <literal>` on line 1, so the literal starts at
/// column 8 and every diagnostic must carry that position.
#[test]
fn an_impossible_date_literal_is_rejected_with_its_position() {
    for (literal, needle) in [
        (r#"d"2020-02-30""#, "超出 1..29"),
        (r#"d"2020-13-01""#, "超出 1..12"),
        (r#"d"2021-02-29""#, "超出 1..28"),
        (r#"d"1899-12-31""#, "超出范围 1900-01-01..=9999-12-31"),
        (r#"d"2020-5-6""#, "不是 YYYY-MM-DD 格式"),
    ] {
        let theory = TempTheory::new("bad-literal", &format!("#check {literal}"));
        let loaded = run(vec![theory.path_text()]);
        let out = stdout(&loaded);
        let err = stderr(&loaded);
        assert_eq!(
            exit_code(&loaded),
            Some(LOAD_ERROR),
            "`{literal}` must not load\nstdout:\n{out}\nstderr:\n{err}"
        );
        assert!(
            err.contains(":1:8: error:"),
            "`{literal}` must be refused at line 1 column 8: {err}"
        );
        assert!(
            err.contains(needle),
            "`{literal}` must explain {needle:?}: {err}"
        );
        assert!(
            err.contains("日期字面量"),
            "`{literal}` must name the literal: {err}"
        );
    }
}

#[test]
fn a_string_or_integer_is_never_read_as_a_date() {
    // A quoted string is not a term at all, and a bare integer has type `Int`:
    // neither is converted into a `Date`. The type error names both types.
    let theory = TempTheory::new(
        "no-implicit",
        r#"
sort 人
pred 发生 : Date → Prop
axiom 发生事实 : 发生 d"2020-05-06"
  identity verified
  source text "示例卷宗" locator "发生日" version "2024" quote "示例发生日"
#check 发生 20200506
"#,
    );
    let loaded = run(vec![theory.path_text()]);
    let err = stderr(&loaded);
    check_stderr(loaded, LOAD_ERROR, &["期望 Date，实际 Int"]);
    assert!(
        err.contains("期望 Date，实际 Int"),
        "the mismatch must name both types: {err}"
    );
}

#[test]
fn a_mixed_comparison_is_refused_and_a_guard_records_dates() {
    // `less` compares two `Int`s or two `Date`s; a mixed pair is not converted.
    let theory = TempTheory::new(
        "mixed-comparison",
        r#"
sort 人
pred 出生 : 人 → Date → Prop
obj 甲 : 人
axiom 甲出生 : 出生 甲 d"2020-05-06"
  identity verified
  source text "示例卷宗" locator "出生日" version "2024" quote "甲于 2020 年 5 月 6 日出生"
rule 出生早于整数 :
  params p : 人, d : Date
  premise 出生 p d
  guard (less d 3000)
  conclude 出生 p d
  source text "示例法" locator "示例条款" version "2024" quote "示例条文"
"#,
    );
    let loaded = run(vec![theory.path_text()]);
    check_stderr(loaded, LOAD_ERROR, &["同为 Int 或同为 Date"]);
}

#[test]
fn date_arithmetic_past_the_range_is_an_explicit_error() {
    let theory = TempTheory::new("overflow", r#"#check (addYears d"9999-12-31" 1)"#);
    let loaded = run(vec![theory.path_text()]);
    check_stderr(
        loaded,
        LOAD_ERROR,
        &[
            "日期运算溢出",
            r#"addYears d"9999-12-31" 1"#,
            "1900-01-01..=9999-12-31",
        ],
    );
}

#[test]
fn the_limitation_example_proves_the_deadline_and_both_outcomes() {
    let deadline = session(
        "日期-诉讼时效.std",
        &[r#":why 时效届满日 甲 d"2023-05-06""#.to_string()],
    );
    check(
        deadline,
        PROVED,
        &[
            r#"▸ 时效届满日 甲 d"2023-05-06""#,
            r#"计算：时效届满日 甲 (addYears d"2020-05-06" 3) = 时效届满日 甲 d"2023-05-06""#,
            r#"实例：p ↦ 甲，d ↦ d"2020-05-06""#,
            "推导已通过独立校验。",
        ],
    );

    // 甲 already passed the deadline: the date comparison in the guard fired.
    let passed = session("日期-诉讼时效.std", &[":why 可能逾期 甲".to_string()]);
    check(
        passed,
        PROVED,
        &[r#"守卫：`(less (addYears d"2020-05-06" 3) d"2024-01-02")` = true"#],
    );

    // 乙 has not: the other date comparison fired for the same fact set.
    let pending = session("日期-诉讼时效.std", &[":why 可主张 乙".to_string()]);
    check(
        pending,
        PROVED,
        &[r#"守卫：`(le d"2024-01-02" (addYears d"2022-03-01" 3))` = true"#],
    );

    // The opposite goal for 甲 is a gap: no guard fired for it.
    let gap = session("日期-诉讼时效.std", &[":why 可主张 甲".to_string()]);
    check(gap, GAP, &["守卫：", "无法判定"]);
}

#[test]
fn the_certificate_is_v13_and_records_the_date_step() {
    let output = session(
        "日期-诉讼时效.std",
        &[r#":cert 时效届满日 甲 d"2023-05-06""#.to_string()],
    );
    let certificate = check(output, PROVED, &[]);
    let text = certificate_text(&certificate);
    let parsed: serde_json::Value = serde_json::from_str(&text).expect("the certificate is JSON");
    assert_eq!(parsed["format_version"], 13, "{text}");
    // A date literal has its own node kind, and the arithmetic step keeps both
    // forms: the rule's own conclusion and the evaluated day.
    assert!(text.contains("\"kind\": \"date\""), "{text}");
    assert!(text.contains("\"value\": \"2023-05-06\""), "{text}");
    assert!(text.contains("\"computed\""), "{text}");
    assert!(text.contains("\"name\": \"addYears\""), "{text}");

    let file = TempFile::new("generated", &text);
    let verify = session(
        "日期-诉讼时效.std",
        &[format!(":verify-cert {}", file.path_text())],
    );
    check(
        verify,
        PROVED,
        &["逻辑校验：通过", "内核证明：通过", "适用性重算"],
    );
}

#[test]
fn a_tampered_date_value_is_rejected() {
    let output = session(
        "日期-诉讼时效.std",
        &[r#":cert 时效届满日 甲 d"2023-05-06""#.to_string()],
    );
    let json = certificate_text(&output);
    // The recorded conclusion is the evaluated day; the checker recomputes it
    // from the rule and the bindings, so a changed day no longer matches.
    let tampered = json.replace("\"value\": \"2023-05-06\"", "\"value\": \"2023-05-07\"");
    assert_ne!(tampered, json, "the conclusion's date must be recorded");
    let file = TempFile::new("tampered-date", &tampered);
    let verify = session(
        "日期-诉讼时效.std",
        &[format!(":verify-cert {}", file.path_text())],
    );
    check(verify, ERROR, &["逻辑校验：失败", "2023-05-07", "addYears"]);
}

/// Rewrite one recorded rule step of a certificate.
///
/// `edit` receives that step's node and must report whether it changed
/// anything. Rewriting through the parsed JSON keeps the test focused on the
/// recorded field: a textual replace could also hit an assumption's
/// proposition, and the environment check would then fail before the arithmetic
/// or guard check ever runs.
fn edit_rule_step(json: &str, rule: &str, edit: impl Fn(&mut serde_json::Value) -> bool) -> String {
    let mut value: serde_json::Value = serde_json::from_str(json).expect("the certificate is JSON");
    let nodes = value["nodes"].as_array_mut().expect("nodes is an array");
    let mut edited = false;
    for node in nodes.iter_mut() {
        if node["kind"] == "rule_application" && node["rule"] == rule && edit(node) {
            edited = true;
        }
    }
    assert!(edited, "the step `{rule}` must be recorded");
    serde_json::to_string_pretty(&value).expect("the edited certificate serializes")
}

/// Replace every date literal value `from` inside `tree`.
fn replace_date(tree: &mut serde_json::Value, from: &str, to: &str) -> bool {
    match tree {
        serde_json::Value::Object(fields) => {
            let mut changed = false;
            if fields.get("kind") == Some(&serde_json::Value::String("date".into())) {
                if let Some(serde_json::Value::String(value)) = fields.get_mut("value") {
                    if value == from {
                        *value = to.to_owned();
                        changed = true;
                    }
                }
            }
            for (_, child) in fields.iter_mut() {
                changed |= replace_date(child, from, to);
            }
            changed
        }
        serde_json::Value::Array(items) => {
            let mut changed = false;
            for item in items.iter_mut() {
                changed |= replace_date(item, from, to);
            }
            changed
        }
        _ => false,
    }
}

/// Replace every constant node named `from` inside `tree`.
fn replace_constant(tree: &mut serde_json::Value, from: &str, to: &str) -> bool {
    match tree {
        serde_json::Value::Object(fields) => {
            let mut changed = false;
            if fields.get("kind") == Some(&serde_json::Value::String("const".into())) {
                if let Some(serde_json::Value::String(name)) = fields.get_mut("name") {
                    if name == from {
                        *name = to.to_owned();
                        changed = true;
                    }
                }
            }
            for (_, child) in fields.iter_mut() {
                changed |= replace_constant(child, from, to);
            }
            changed
        }
        serde_json::Value::Array(items) => {
            let mut changed = false;
            for item in items.iter_mut() {
                changed |= replace_constant(item, from, to);
            }
            changed
        }
        _ => false,
    }
}

#[test]
fn a_tampered_date_operand_or_operation_is_rejected() {
    let output = session(
        "日期-诉讼时效.std",
        &[r#":cert 时效届满日 甲 d"2023-05-06""#.to_string()],
    );
    let json = certificate_text(&output);

    // The `computed` form is the rule's own conclusion under the recorded
    // bindings: editing the date operand breaks the structural comparison.
    let operand = edit_rule_step(&json, "时效届满", |node| {
        replace_date(&mut node["computed"], "2020-05-06", "2020-05-07")
    });
    let file = TempFile::new("tampered-operand", &operand);
    let verify = session(
        "日期-诉讼时效.std",
        &[format!(":verify-cert {}", file.path_text())],
    );
    check(verify, ERROR, &["逻辑校验：失败", "算术步骤与规则不一致"]);

    // Swapping the operation is caught by the same structural comparison.
    let operation = edit_rule_step(&json, "时效届满", |node| {
        replace_constant(&mut node["computed"], "addYears", "addDays")
    });
    let file = TempFile::new("tampered-operation", &operation);
    let verify = session(
        "日期-诉讼时效.std",
        &[format!(":verify-cert {}", file.path_text())],
    );
    check(verify, ERROR, &["逻辑校验：失败", "addDays", "addYears"]);
}

#[test]
fn a_tampered_guard_date_is_rejected() {
    // Export the guarded rule (`可能逾期 甲`) and change the guard's recorded
    // instance: the checker re-evaluates the comparison itself, so an edited
    // date operand must be caught and the guard must be named.
    let output = session("日期-诉讼时效.std", &[":cert 可能逾期 甲".to_string()]);
    let json = certificate_text(&output);
    let tampered = edit_rule_step(&json, "已过截止日", |node| {
        let guards = node["guards"].as_array_mut().expect("guards are recorded");
        let mut changed = false;
        for guard in guards.iter_mut() {
            changed |= replace_date(&mut guard["instance"], "2024-01-02", "2023-01-02");
        }
        changed
    });
    let file = TempFile::new("tampered-guard", &tampered);
    let verify = session(
        "日期-诉讼时效.std",
        &[format!(":verify-cert {}", file.path_text())],
    );
    let checked = check(verify, ERROR, &["逻辑校验：失败", "守卫"]);
    assert!(
        stdout(&checked).contains("按绑定得到的形态"),
        "the guard record itself must be named: {}",
        stdout(&checked)
    );
}

#[test]
fn a_certificate_that_is_earlier_than_v13_is_refused() {
    let output = session(
        "日期-诉讼时效.std",
        &[r#":cert 时效届满日 甲 d"2023-05-06""#.to_string()],
    );
    let json = certificate_text(&output);
    for version in ["12", "11", "9", "1"] {
        let old = json.replace(
            "\"format_version\": 13",
            &format!("\"format_version\": {version}"),
        );
        assert_ne!(old, json, "the fixture must record the version");
        let file = TempFile::new("old-version", &old);
        let verify = session(
            "日期-诉讼时效.std",
            &[format!(":verify-cert {}", file.path_text())],
        );
        check_stderr(verify, ERROR, &["supports 13"]);
    }
}

#[test]
fn a_date_in_a_certificate_must_be_a_real_day() {
    let output = session(
        "日期-诉讼时效.std",
        &[r#":cert 时效届满日 甲 d"2023-05-06""#.to_string()],
    );
    let json = certificate_text(&output);
    // A date node with an impossible day, a loose shape or an out-of-range year
    // cannot be read back: the certificate format validates the day, so a
    // hand-written document cannot smuggle in a date the kernel would refuse.
    for value in ["2020-02-30", "2020-5-6", "1899-12-31", "今日"] {
        let tampered = json.replace(
            "\"value\": \"2023-05-06\"",
            &format!("\"value\": \"{value}\""),
        );
        assert_ne!(tampered, json, "the fixture must record the day");
        let file = TempFile::new("bad-day", &tampered);
        let verify = session(
            "日期-诉讼时效.std",
            &[format!(":verify-cert {}", file.path_text())],
        );
        let out = stdout(&verify);
        assert_eq!(exit_code(&verify), Some(ERROR), "{out}");
        assert!(
            out.contains("不是有效的证书 JSON") || out.contains("日期"),
            "an invalid day must be refused at parse time: {out}"
        );
    }
}
