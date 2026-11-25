//! The declaration layer and the report layer for burden of proof and
//! standards of proof, end to end.
//!
//! `:inspect` shows what was declared (and only what was declared). Declaring
//! anything changes neither the derivation nor the certificate. The report
//! layer annotates `:gap`, `:issues` and `:explain` with the rule's declared
//! burden/standard, writes an undeclared value out as `未声明举证责任` /
//! `未声明证明标准`, and never defaults a value or attaches a number to the
//! standard. `:why` stays byte-identical.
//!
//! The reasoning/certificate comparison is byte for byte on purpose: these
//! fields are declarations for the report, not premises of the calculus.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const GAP: i32 = 1;
const PROVED: i32 = 0;
const COMMAND_ERROR: i32 = 2;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Run the CLI from the repository root. `--no-default-packs` keeps the
/// session to the file under test: no registry, no profile, no official pack.
fn run(args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .arg("--no-default-packs")
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("failed to run the CLI: {e}"))
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
            "std-deduce-cli-burden-{}-{tag}-{n}.std",
            std::process::id()
        ));
        fs::write(&path, source).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        TempTheory { path }
    }
}

impl Drop for TempTheory {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn load_and(theory: &TempTheory, command: &str) -> Output {
    run(&[
        format!(":load {}", theory.path.display()),
        command.to_owned(),
    ])
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn check(output: Output, expected: i32, needles: &[&str]) -> Output {
    let code = output.status.code();
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

/// The line `:inspect` prints for the rule called `name`.
fn rule_line(out: &str, name: &str) -> String {
    let prefix = format!("rule  {name} :");
    out.lines()
        .find(|line| line.contains(&prefix))
        .unwrap_or_else(|| panic!("no `:inspect` line for rule {name}:\n{out}"))
        .to_owned()
}

const INSPECT_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 免责 : 公民 → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "事实"

rule 有声明 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  burden claimant
  standard preponderance
  exception_burden respondent
  exception_standard clear_and_convincing
  source text "测试" locator "一"

rule 只有标准 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  standard beyond_reasonable_doubt
  source text "测试" locator "二"

rule 只有例外举证 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  exception_burden court
  source text "测试" locator "三"

rule 只有例外标准 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  exception_standard preponderance
  source text "测试" locator "四"

rule 未声明 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  source text "测试" locator "五"
"#;

#[test]
fn inspect_shows_burden_and_standard_declarations() {
    let theory = TempTheory::new("inspect", INSPECT_THEORY);
    let output = check(load_and(&theory, ":inspect"), PROVED, &["已加载"]);
    let out = stdout(&output);

    let declared = rule_line(&out, "有声明");
    assert!(
        declared.contains("〔举证 claimant · 标准 preponderance〕"),
        "the burden/standard group is missing: {declared}"
    );
    assert!(
        declared.contains("〔例外举证 respondent · 例外标准 clear_and_convincing〕"),
        "the exception group is missing: {declared}"
    );

    let standard_only = rule_line(&out, "只有标准");
    assert!(
        standard_only.contains("〔标准 beyond_reasonable_doubt〕"),
        "an undeclared burden must not be shown, nor replaced by a default: {standard_only}"
    );
    assert!(
        !standard_only.contains("举证"),
        "no burden was declared, so no `举证` may be printed: {standard_only}"
    );

    let exception_only = rule_line(&out, "只有例外举证");
    assert!(
        exception_only.contains("〔例外举证 court〕"),
        "the exception burden is missing: {exception_only}"
    );
    assert!(
        !exception_only.contains("例外标准") && !exception_only.contains("〔举证"),
        "only the declared exception field may be shown: {exception_only}"
    );

    let exception_standard_only = rule_line(&out, "只有例外标准");
    assert!(
        exception_standard_only.contains("〔例外标准 preponderance〕"),
        "the exception standard is missing: {exception_standard_only}"
    );
    assert!(
        !exception_standard_only.contains("例外举证")
            && !exception_standard_only.contains("〔举证")
            && !exception_standard_only.contains("〔标准"),
        "only the declared exception field may be shown: {exception_standard_only}"
    );

    let undeclared = rule_line(&out, "未声明");
    for marker in [
        "〔举证",
        "〔标准",
        "〔例外举证",
        "〔例外标准",
        "claimant",
        "preponderance",
    ] {
        assert!(
            !undeclared.contains(marker),
            "an undeclared rule must print no breakdown ({marker}): {undeclared}"
        );
    }
}

const BASE_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 免责 : 公民 → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "事实"
rule 规则 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  source text "测试" locator "一"
"#;

const DECLARED_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 免责 : 公民 → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "事实"
rule 规则 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  burden claimant
  standard clear_and_convincing
  exception_burden respondent
  exception_standard beyond_reasonable_doubt
  source text "测试" locator "一"
"#;

/// The derivation section of `:why`, starting at the root line.
fn why_section(output: &Output) -> String {
    let out = stdout(output);
    let start = out
        .find('▸')
        .unwrap_or_else(|| panic!("no derivation in the output:\n{out}"));
    out[start..].to_owned()
}

/// The certificate JSON, starting at its first `{`.
fn cert_section(output: &Output) -> String {
    let out = stdout(output);
    let start = out
        .find('{')
        .unwrap_or_else(|| panic!("no certificate in the output:\n{out}"));
    out[start..].to_owned()
}

#[test]
fn declaring_burden_and_standard_does_not_change_the_derivation() {
    let base = TempTheory::new("why-base", BASE_THEORY);
    let declared = TempTheory::new("why-declared", DECLARED_THEORY);
    let base_out = check(
        load_and(&base, ":why 违法 张三"),
        PROVED,
        &["推导已通过独立校验。"],
    );
    let declared_out = check(
        load_and(&declared, ":why 违法 张三"),
        PROVED,
        &["推导已通过独立校验。"],
    );
    assert_eq!(
        why_section(&base_out),
        why_section(&declared_out),
        "burden/standard declarations must not change the derivation"
    );
}

#[test]
fn declaring_burden_and_standard_does_not_change_the_certificate() {
    let base = TempTheory::new("cert-base", BASE_THEORY);
    let declared = TempTheory::new("cert-declared", DECLARED_THEORY);
    let base_out = check(
        load_and(&base, ":cert 违法 张三"),
        PROVED,
        &["\"format_version\": 7"],
    );
    let declared_out = check(
        load_and(&declared, ":cert 违法 张三"),
        PROVED,
        &["\"format_version\": 7"],
    );
    assert_eq!(
        cert_section(&base_out),
        cert_section(&declared_out),
        "burden/standard declarations must not change the certificate"
    );
}

const ILLEGAL_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "事实"
rule 规则 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  burden plaintiff
  source text "测试" locator "一"
"#;

#[test]
fn an_illegal_value_fails_the_load_with_rule_field_and_allowed_values() {
    let theory = TempTheory::new("illegal", ILLEGAL_THEORY);
    let output = load_and(&theory, ":quit");
    let code = output.status.code();
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(code, Some(COMMAND_ERROR), "stdout:\n{out}\nstderr:\n{err}");
    assert!(
        err.contains("错误："),
        "the `:load` error keeps its prefix: {err}"
    );
    for needle in [
        "error: 规则 `规则` 的 burden 取值 `plaintiff` 非法",
        "claimant",
        "respondent",
        "court",
    ] {
        assert!(
            err.contains(needle),
            "the diagnostic must contain {needle:?}:\n{err}"
        );
    }
}

/// The line that starts with `prefix` after trimming its indentation.
fn line_starting_with(out: &str, prefix: &str) -> String {
    out.lines()
        .find(|line| line.trim_start().starts_with(prefix))
        .unwrap_or_else(|| panic!("no line starts with {prefix:?}:\n{out}"))
        .to_owned()
}

/// `:why` output starting at the formal tree's root line. A gap root is
/// printed as `? <proposition>  【未闭合】`; a proved root starts with `▸`.
fn why_body(output: &Output) -> String {
    let out = stdout(output);
    let start = out
        .find("? ")
        .or_else(|| out.find('▸'))
        .unwrap_or_else(|| panic!("no derivation in the output:\n{out}"));
    out[start..].to_owned()
}

/// Two rules concluding the same proposition: one declares a burden and
/// standard, the other declares nothing. Their missing premises differ, so the
/// report has to attribute each annotation to the rule that needs it.
const REPORT_THEORY: &str = r#"
sort 人
pred 侵占 : 人 → Prop
pred 占有 : 人 → Prop
pred 违法 : 人 → Prop
obj 张三 : 人

rule 声明规则 :
  params p : 人
  premise 侵占 p
  conclude 违法 p
  burden claimant
  standard preponderance
  source text "测试" locator "声明规则"

rule 未声明规则 :
  params p : 人
  premise 占有 p
  conclude 违法 p
  source text "测试" locator "未声明规则"
"#;

/// The same rules without any burden/standard clause: `:why` must not change.
const REPORT_THEORY_UNDECLARED: &str = r#"
sort 人
pred 侵占 : 人 → Prop
pred 占有 : 人 → Prop
pred 违法 : 人 → Prop
obj 张三 : 人

rule 声明规则 :
  params p : 人
  premise 侵占 p
  conclude 违法 p
  source text "测试" locator "声明规则"

rule 未声明规则 :
  params p : 人
  premise 占有 p
  conclude 违法 p
  source text "测试" locator "未声明规则"
"#;

#[test]
fn gap_and_issues_annotate_each_missing_premise_with_its_rule() {
    let theory = TempTheory::new("report-values", REPORT_THEORY);
    let gap = check(
        load_and(&theory, ":gap 违法 张三"),
        GAP,
        &[
            "缺 ⟨侵占 张三⟩〔举证：主张方 / 优势证据〕",
            "缺 ⟨占有 张三⟩〔举证：未声明举证责任 / 未声明证明标准〕",
        ],
    );
    // `:issues` renders the same gap tree, so it must carry the exact same
    // annotated lines, not a second wording.
    let issues = check(
        load_and(&theory, ":issues"),
        GAP,
        &[
            "争点 ⟨违法 张三⟩",
            "缺 ⟨侵占 张三⟩〔举证：主张方 / 优势证据〕",
            "缺 ⟨占有 张三⟩〔举证：未声明举证责任 / 未声明证明标准〕",
        ],
    );
    let gap_out = stdout(&gap);
    let issues_out = stdout(&issues);
    for (premise, needle) in [
        ("缺 ⟨侵占 张三⟩", "〔举证：主张方 / 优势证据〕"),
        (
            "缺 ⟨占有 张三⟩",
            "〔举证：未声明举证责任 / 未声明证明标准〕",
        ),
    ] {
        assert_eq!(
            line_starting_with(&gap_out, premise),
            line_starting_with(&issues_out, premise),
            ":gap and :issues must render the same line for {needle}"
        );
    }
    // An undeclared rule is not replaced by the claimant or by any standard.
    for line in gap_out
        .lines()
        .chain(issues_out.lines())
        .filter(|line| line.contains("占有 张三"))
    {
        assert!(
            !line.contains("主张方") && !line.contains("优势证据"),
            "an undeclared burden must not be defaulted: {line}"
        );
    }

    let explain = check(
        load_and(&theory, ":explain 违法 张三"),
        GAP,
        &[
            "缺少前提「侵占 张三」（这条证据由主张方提出，标准是优势证据）",
            "缺少前提「占有 张三」（这条证据未声明举证责任，未声明证明标准）",
            "举证责任：规则「声明规则」缺少前提「侵占 张三」：这条证据由主张方提出，标准是优势证据",
            "规则「未声明规则」缺少前提「占有 张三」：这条证据未声明举证责任，未声明证明标准",
        ],
    );
    let explain_out = stdout(&explain);
    assert!(
        !explain_out.contains("标准是未声明证明标准"),
        "the narrative must spell out an undeclared standard instead of hedging: {explain_out}"
    );
}

/// A rule whose `unless` is triggered is blocked; the report names who must
/// prove the exception, and an undeclared exception stays undeclared.
const EXCEPTION_THEORY: &str = r#"
sort 人
pred 侵占 : 人 → Prop
pred 违法 : 人 → Prop
pred 免责 : 人 → Prop
obj 张三 : 人
axiom 免责事实 : 免责 张三
  source text "测试" locator "免责事实"

rule 例外已声明 :
  params p : 人
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  exception_burden respondent
  exception_standard clear_and_convincing
  source text "测试" locator "例外已声明"

rule 例外未声明 :
  params p : 人
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  source text "测试" locator "例外未声明"
"#;

#[test]
fn a_triggered_unless_reports_the_exception_burden_or_says_it_is_undeclared() {
    let theory = TempTheory::new("exception-report", EXCEPTION_THEORY);
    for (command, needles) in [
        (
            ":gap 违法 张三",
            vec![
                "〔例外举证：相对方 / 清楚可信〕",
                "〔例外举证：未声明举证责任 / 未声明证明标准〕",
            ],
        ),
        (
            ":issues",
            vec![
                "〔例外举证：相对方 / 清楚可信〕",
                "〔例外举证：未声明举证责任 / 未声明证明标准〕",
            ],
        ),
        (
            ":explain 违法 张三",
            vec![
                "例外由相对方提出，标准是清楚可信",
                "例外未声明举证责任，未声明证明标准",
            ],
        ),
    ] {
        check(load_and(&theory, command), GAP, &needles);
    }
}

/// A two-step gap: the outer rule declares one burden, the inner rule another.
/// Each missing premise carries the burden of the rule that needs it, so the
/// two groups never bleed into one another.
const NESTED_THEORY: &str = r#"
sort 人
pred 基础 : 人 → Prop
pred 中间 : 人 → Prop
pred 另一 : 人 → Prop
pred 目标 : 人 → Prop
obj 张三 : 人

rule 目标规则 :
  params p : 人
  premise 中间 p
  premise 另一 p
  conclude 目标 p
  burden claimant
  standard preponderance
  source text "测试" locator "目标规则"

rule 中间规则 :
  params p : 人
  premise 基础 p
  conclude 中间 p
  burden respondent
  standard beyond_reasonable_doubt
  source text "测试" locator "中间规则"
"#;

#[test]
fn each_missing_premise_carries_only_its_own_rules_burden() {
    let theory = TempTheory::new("nested-report", NESTED_THEORY);
    let gap = check(
        load_and(&theory, ":gap 目标 张三"),
        GAP,
        &[
            "缺 ⟨中间 张三⟩〔举证：主张方 / 优势证据〕",
            "缺 ⟨另一 张三⟩〔举证：主张方 / 优势证据〕",
            "缺 ⟨基础 张三⟩〔举证：相对方 / 排除合理怀疑〕",
        ],
    );
    let out = stdout(&gap);
    for (premise, expected, other) in [
        ("缺 ⟨中间 张三⟩", "主张方 / 优势证据", "相对方"),
        ("缺 ⟨另一 张三⟩", "主张方 / 优势证据", "相对方"),
        ("缺 ⟨基础 张三⟩", "相对方 / 排除合理怀疑", "主张方"),
    ] {
        let line = line_starting_with(&out, premise);
        assert!(
            line.contains(expected),
            "the premise must carry its own rule's burden: {line}"
        );
        assert!(
            !line.contains(other),
            "another rule's burden must not bleed into this premise: {line}"
        );
    }
    // `:issues` lists the same nested tree and the same per-premise values.
    let issues = check(
        load_and(&theory, ":issues"),
        GAP,
        &[
            "缺 ⟨中间 张三⟩〔举证：主张方 / 优势证据〕",
            "缺 ⟨基础 张三⟩〔举证：相对方 / 排除合理怀疑〕",
        ],
    );
    let issues_out = stdout(&issues);
    assert!(
        line_starting_with(&issues_out, "缺 ⟨基础 张三⟩").contains("相对方 / 排除合理怀疑"),
        "an issue's nested premise keeps its own rule's burden:\n{issues_out}"
    );
}

/// The line `:explain` prints for one gap candidate rule.
fn candidate_line(out: &str, rule: &str) -> String {
    let prefix = format!("  · 候选规则「{rule}」：");
    out.lines()
        .find(|line| line.starts_with(&prefix))
        .unwrap_or_else(|| panic!("no narrative line for rule {rule}:\n{out}"))
        .to_owned()
}

/// A rule with both groups declared, a missing premise and a blocked `unless`:
/// the missing line takes the requirement group and the blocker line takes the
/// exception group, with no borrowing in either direction.
const BOTH_GROUPS_THEORY: &str = r#"
sort 人
pred 侵占 : 人 → Prop
pred 违法 : 人 → Prop
pred 免责 : 人 → Prop
obj 张三 : 人
axiom 免责事实 : 免责 张三
  source text "测试" locator "免责事实"

rule 两组 :
  params p : 人
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  burden claimant
  standard preponderance
  exception_burden respondent
  exception_standard clear_and_convincing
  source text "测试" locator "两组"
"#;

#[test]
fn both_groups_are_reported_without_borrowing_from_each_other() {
    let theory = TempTheory::new("both-groups", BOTH_GROUPS_THEORY);
    let gap = check(
        load_and(&theory, ":gap 违法 张三"),
        GAP,
        &[
            "缺 ⟨侵占 张三⟩〔举证：主张方 / 优势证据〕",
            "被阻断：「免责 张三」〔用户陈述〕已成立，故本规则不触发 〔例外举证：相对方 / 清楚可信〕",
        ],
    );
    let out = stdout(&gap);
    let missing = line_starting_with(&out, "缺 ⟨侵占 张三⟩");
    assert!(
        !missing.contains("相对方") && !missing.contains("清楚可信"),
        "the exception group must not leak into the requirement line: {missing}"
    );
    let blocked = line_starting_with(&out, "被阻断：");
    assert!(
        !blocked.contains("主张方") && !blocked.contains("优势证据"),
        "the requirement group must not leak into the exception line: {blocked}"
    );

    let explain = check(
        load_and(&theory, ":explain 违法 张三"),
        GAP,
        &[
            "缺少前提「侵占 张三」（这条证据由主张方提出，标准是优势证据）",
            "unless 条件「免责 张三」（用户陈述）已成立，故该规则被阻断（例外由相对方提出，标准是清楚可信）",
        ],
    );
    let explain_out = stdout(&explain);
    let line = candidate_line(&explain_out, "两组");
    let blocked_part = line.split("；unless").nth(1).unwrap_or_default();
    assert!(
        !blocked_part.contains("主张方") && !blocked_part.contains("优势证据"),
        "the narrative must not borrow the requirement group for the exception: {line}"
    );
}

/// Only the exception group is declared: the missing premise must stay
/// undeclared, and the blocker line takes the exception group.
const ONLY_EXCEPTION_THEORY: &str = r#"
sort 人
pred 侵占 : 人 → Prop
pred 违法 : 人 → Prop
pred 免责 : 人 → Prop
obj 张三 : 人
axiom 免责事实 : 免责 张三
  source text "测试" locator "免责事实"

rule 只有例外 :
  params p : 人
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  exception_burden respondent
  exception_standard clear_and_convincing
  source text "测试" locator "只有例外"
"#;

#[test]
fn an_exception_only_rule_does_not_borrow_for_the_missing_premise() {
    let theory = TempTheory::new("only-exception", ONLY_EXCEPTION_THEORY);
    let gap = check(
        load_and(&theory, ":gap 违法 张三"),
        GAP,
        &[
            "缺 ⟨侵占 张三⟩〔举证：未声明举证责任 / 未声明证明标准〕",
            "〔例外举证：相对方 / 清楚可信〕",
        ],
    );
    let out = stdout(&gap);
    let missing = line_starting_with(&out, "缺 ⟨侵占 张三⟩");
    assert!(
        !missing.contains("相对方") && !missing.contains("清楚可信"),
        "an undeclared requirement group must not take the exception values: {missing}"
    );

    let explain = check(
        load_and(&theory, ":explain 违法 张三"),
        GAP,
        &[
            "缺少前提「侵占 张三」（这条证据未声明举证责任，未声明证明标准）",
            "例外由相对方提出，标准是清楚可信",
        ],
    );
    let explain_out = stdout(&explain);
    let line = candidate_line(&explain_out, "只有例外");
    let missing_part = line.split("；unless").next().unwrap_or_default();
    assert!(
        !missing_part.contains("相对方") && !missing_part.contains("清楚可信"),
        "the narrative must not borrow the exception values for a missing premise: {line}"
    );
}

/// Only the requirement group is declared: the blocker must stay undeclared.
const ONLY_REQUIREMENT_THEORY: &str = r#"
sort 人
pred 占有 : 人 → Prop
pred 违法 : 人 → Prop
pred 免责 : 人 → Prop
obj 张三 : 人
axiom 免责事实 : 免责 张三
  source text "测试" locator "免责事实"

rule 只有本体 :
  params p : 人
  premise 占有 p
  conclude 违法 p
  unless 免责 p
  burden claimant
  standard preponderance
  source text "测试" locator "只有本体"
"#;

#[test]
fn a_requirement_only_rule_does_not_borrow_for_the_blocker() {
    let theory = TempTheory::new("only-requirement", ONLY_REQUIREMENT_THEORY);
    let gap = check(
        load_and(&theory, ":gap 违法 张三"),
        GAP,
        &[
            "缺 ⟨占有 张三⟩〔举证：主张方 / 优势证据〕",
            "〔例外举证：未声明举证责任 / 未声明证明标准〕",
        ],
    );
    let out = stdout(&gap);
    let blocked = line_starting_with(&out, "被阻断：");
    assert!(
        !blocked.contains("主张方") && !blocked.contains("优势证据"),
        "an undeclared exception group must not take the requirement values: {blocked}"
    );

    let explain = check(
        load_and(&theory, ":explain 违法 张三"),
        GAP,
        &[
            "缺少前提「占有 张三」（这条证据由主张方提出，标准是优势证据）",
            "例外未声明举证责任，未声明证明标准",
        ],
    );
    let explain_out = stdout(&explain);
    let line = candidate_line(&explain_out, "只有本体");
    let blocked_part = line.split("；unless").nth(1).unwrap_or_default();
    assert!(
        !blocked_part.contains("主张方") && !blocked_part.contains("优势证据"),
        "the narrative must not borrow the requirement values for the exception: {line}"
    );
}

/// Each group declares only one of its two fields, and the missing field is in
/// the *other* group. Every field must be reported as undeclared on its own;
/// a per-field fallback would fill it in from the other group.
const CROSS_FIELD_THEORY: &str = r#"
sort 人
pred 侵占 : 人 → Prop
pred 占有 : 人 → Prop
pred 违法 : 人 → Prop
pred 免责 : 人 → Prop
obj 张三 : 人
axiom 免责事实 : 免责 张三
  source text "测试" locator "免责事实"

rule 跨组一 :
  params p : 人
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  burden claimant
  exception_standard clear_and_convincing
  source text "测试" locator "跨组一"

rule 跨组二 :
  params p : 人
  premise 占有 p
  conclude 违法 p
  unless 免责 p
  standard preponderance
  exception_burden court
  source text "测试" locator "跨组二"
"#;

#[test]
fn each_undeclared_field_stays_undeclared_without_a_group_fallback() {
    let theory = TempTheory::new("cross-field", CROSS_FIELD_THEORY);
    let gap = check(
        load_and(&theory, ":gap 违法 张三"),
        GAP,
        &[
            "缺 ⟨侵占 张三⟩〔举证：主张方 / 未声明证明标准〕",
            "缺 ⟨占有 张三⟩〔举证：未声明举证责任 / 优势证据〕",
            "〔例外举证：未声明举证责任 / 清楚可信〕",
            "〔例外举证：法院职权 / 未声明证明标准〕",
        ],
    );
    let out = stdout(&gap);
    let first = line_starting_with(&out, "缺 ⟨侵占 张三⟩");
    let second = line_starting_with(&out, "缺 ⟨占有 张三⟩");
    assert!(
        first.contains("主张方") && !first.contains("清楚可信"),
        "the declared burden must not borrow the exception standard: {first}"
    );
    assert!(
        second.contains("优势证据") && !second.contains("法院职权"),
        "the declared standard must not borrow the exception burden: {second}"
    );
    assert!(
        out.lines()
            .any(|line| line.contains("〔例外举证：法院职权 / 未声明证明标准〕")),
        "the exception burden must not borrow the requirement standard:\n{out}"
    );

    let explain = check(
        load_and(&theory, ":explain 违法 张三"),
        GAP,
        &[
            "缺少前提「侵占 张三」（这条证据由主张方提出，但未声明证明标准）",
            "缺少前提「占有 张三」（这条证据未声明举证责任，标准是优势证据）",
            "例外未声明举证责任，标准是清楚可信",
            "例外由法院依职权查明，但未声明证明标准",
        ],
    );
    let explain_out = stdout(&explain);
    let first_line = candidate_line(&explain_out, "跨组一");
    assert!(
        !first_line.contains("清楚可信")
            || first_line.contains("例外未声明举证责任，标准是清楚可信"),
        "the declared burden must not borrow the exception standard: {first_line}"
    );
    let second_line = candidate_line(&explain_out, "跨组二");
    assert!(
        second_line.contains("例外由法院依职权查明，但未声明证明标准"),
        "the court role must read naturally and the standard must stay undeclared: {second_line}"
    );
}

#[test]
fn declaring_burden_and_standard_does_not_change_why_on_a_gap() {
    let base = TempTheory::new("why-gap-base", REPORT_THEORY_UNDECLARED);
    let declared = TempTheory::new("why-gap-declared", REPORT_THEORY);
    let base_out = check(load_and(&base, ":why 违法 张三"), GAP, &["【未闭合】"]);
    let declared_out = check(load_and(&declared, ":why 违法 张三"), GAP, &["【未闭合】"]);
    assert_eq!(
        why_body(&base_out),
        why_body(&declared_out),
        ":why must not gain the burden report"
    );
    let body = why_body(&declared_out);
    for marker in ["举证", "主张方", "优势证据", "未声明举证责任"] {
        assert!(
            !body.contains(marker),
            ":why must not print {marker:?}:\n{body}"
        );
    }
}
