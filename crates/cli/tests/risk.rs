//! End-to-end tests for risk themes and the disclaimer line.
//!
//! A theory marks a predicate with `risk <类别> <谓词>`; a derivation about that
//! predicate then prints one explicit high-risk line with its evidence, and a
//! low-risk case prints nothing. Every result output of `:why`, `:explain`,
//! `:labels` and `:cert` carries the same one-line disclaimer, which never enters
//! the derivation tree or the certificate JSON.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const GAP_OR_CONFLICT: i32 = 1;

const DISCLAIMER: &str = "声明：这是模型内推导，不是法律意见。";
/// The disclaimer sentence itself; `:cert` prints it behind a `说明：` prefix
/// because its two explanation lines are notices, not result declarations.
const MODEL_ONLY: &str = "这是模型内推导，不是法律意见";
const PRIVACY: &str = "证书包含案件原文，可能含个人信息，分享前请自行处理";

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("std-deduce-risk-{}-{tag}-{n}", std::process::id()));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn write(&self, name: &str, text: &str) -> String {
        let path = self.path.join(name);
        fs::write(&path, text).unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path.display().to_string()
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn run(commands: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(commands)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn session(file: &str, options: &[&str], commands: &[&str]) -> Output {
    let mut all = vec!["--no-default-packs".to_owned()];
    all.extend(options.iter().map(|option| (*option).to_owned()));
    all.push(file.to_owned());
    all.extend(commands.iter().map(|command| (*command).to_owned()));
    run(&all)
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

/// A minimal theory whose rule concludes a themed predicate, with a cited
/// source on both the fact and the rule so the evidence can name them.
fn themed_theory(theme: &str, predicate: &str, rule: &str, trigger: &str) -> String {
    format!(
        "sort 人\n\
         pred {predicate} : 人 → Prop\n\
         pred {trigger} : 人 → Prop\n\
         risk {theme} {predicate}\n\
         obj 甲 : 人\n\
         axiom 触发事实 : {trigger} 甲\n  \
           source text \"案情\" locator \"第一页\"\n\
         rule {rule} :\n  \
           params p : 人\n  \
           premise {trigger} p\n  \
           conclude {predicate} p\n  \
           source text \"测试法\" locator \"第一条\"\n"
    )
}

#[test]
fn each_high_risk_theme_prints_one_warning_line_with_its_basis() {
    let cases = [
        ("刑事", "犯罪", "认定犯罪", "实施犯罪行为"),
        ("人身安全", "人身受到伤害", "认定人身伤害", "遭受殴打"),
        ("重大财产", "重大财产损失", "认定重大财产损失", "房产被毁"),
        ("临近期限", "期限临近", "认定期限临近", "提出申请"),
        ("涉外或移民", "涉外交付", "认定涉外交付", "签署合同"),
    ];
    for (theme, predicate, rule, trigger) in cases {
        let dir = TempDir::new(theme);
        let file = dir.write("case.std", &themed_theory(theme, predicate, rule, trigger));
        for command in ["why", "explain"] {
            let output = session(&file, &[], &[&format!(":{command} {predicate} 甲")]);
            assert_exit(&output, PROVED);
            let out = stdout(&output);
            let expected = format!("高风险题材：涉及{theme}；建议尽快咨询执业律师。");
            assert!(
                out.contains(&expected),
                "`:{command}` must print exactly the high-risk line {expected:?}\n{out}"
            );
            assert_eq!(
                out.matches(&expected).count(),
                1,
                "the warning must be one line, not repeated\n{out}"
            );
            assert!(
                out.contains("  依据：命题「") && out.contains("被声明为风险题材「"),
                "the warning must carry its basis\n{out}"
            );
            assert!(
                out.contains(&format!("（声明 `risk {theme} {predicate}`）")),
                "{out}"
            );
            assert!(out.contains(&format!("由规则「{rule}」推出")), "{out}");
            assert!(out.contains("出处：「测试法第一条」"), "{out}");
            assert!(out.contains(DISCLAIMER), "{out}");
        }
    }
}

#[test]
fn a_case_without_a_risk_marker_prints_no_risk_line() {
    let dir = TempDir::new("low");
    let file = dir.write(
        "case.std",
        "sort 人\npred 违法 : 人 → Prop\npred 受罚 : 人 → Prop\nobj 甲 : 人\n\
         axiom 甲违法 : 违法 甲\n  source text \"案情\" locator \"一\"\n\
         rule 处罚 :\n  params p : 人\n  premise 违法 p\n  conclude 受罚 p\n  \
         source text \"测试法\" locator \"第一条\"\n",
    );
    for command in ["why", "explain", "labels"] {
        let output = session(&file, &[], &[&format!(":{command} 受罚 甲")]);
        assert_exit(&output, PROVED);
        let out = stdout(&output);
        assert!(
            !out.contains("高风险题材") && !out.contains("题材风险"),
            "a low-risk case must not be buried under a risk line\n{out}"
        );
        assert!(
            !out.lines().any(|line| line.starts_with("  依据：命题")),
            "a low-risk case must not print risk evidence\n{out}"
        );
        assert!(out.contains(DISCLAIMER), "the disclaimer stays\n{out}");
    }
}

#[test]
fn multiple_themes_share_one_warning_line_in_the_fixed_order() {
    let dir = TempDir::new("multi");
    let file = dir.write(
        "case.std",
        "sort 人\npred 犯罪 : 人 → Prop\npred 人身受到伤害 : 人 → Prop\n\
         risk 刑事 犯罪\nrisk 人身安全 人身受到伤害\nobj 甲 : 人\n\
         axiom 事实犯罪 : 犯罪 甲\n  source text \"案情\" locator \"一\"\n\
         axiom 事实受害 : 人身受到伤害 甲\n  source text \"案情\" locator \"二\"\n",
    );
    let output = session(&file, &[], &[":why 犯罪 甲"]);
    // The root is the fact `犯罪 甲`; `人身受到伤害 甲` is an unrelated fact and
    // must not join this conclusion's themes.
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("高风险题材：涉及刑事；建议尽快咨询执业律师。"),
        "{out}"
    );
    assert!(!out.contains("涉及刑事、人身安全"), "{out}");

    // A proof that uses both conclusions states both themes in one line.
    let file = dir.write(
        "both.std",
        "sort 人\npred 犯罪 : 人 → Prop\npred 人身受到伤害 : 人 → Prop\n\
         pred 双重 : 人 → Prop\nrisk 刑事 犯罪\nrisk 人身安全 人身受到伤害\nobj 甲 : 人\n\
         axiom 事实犯罪 : 犯罪 甲\n  source text \"案情\" locator \"一\"\n\
         axiom 事实受害 : 人身受到伤害 甲\n  source text \"案情\" locator \"二\"\n\
         rule 合并 :\n  params p : 人\n  premise 犯罪 p\n  premise 人身受到伤害 p\n  \
         conclude 双重 p\n  source text \"测试法\" locator \"第一条\"\n",
    );
    let output = session(&file, &[], &[":why 双重 甲"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("高风险题材：涉及刑事、人身安全；建议尽快咨询执业律师。"),
        "the themes are joined into one line in the fixed order\n{out}"
    );
    assert_eq!(
        out.lines()
            .filter(|line| line.starts_with("高风险题材："))
            .count(),
        1,
        "there is exactly one warning line\n{out}"
    );
}

#[test]
fn labels_lists_the_risk_theme_as_a_second_label_without_relabelling_the_trust() {
    let dir = TempDir::new("labels");
    let file = dir.write(
        "case.std",
        &themed_theory("人身安全", "人身受到伤害", "认定人身伤害", "遭受殴打"),
    );
    let output = session(&file, &[], &[":labels 人身受到伤害 甲"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("题材风险（次标签，与上面的五种信任标签相互独立，不并入「需律师判断」）："),
        "{out}"
    );
    assert!(
        out.contains("高风险题材：涉及人身安全；建议尽快咨询执业律师。"),
        "{out}"
    );
    assert!(out.contains("  人身安全\n"), "{out}");
    assert!(
        out.contains("    - 命题「人身受到伤害 甲」由规则「认定人身伤害」推出"),
        "{out}"
    );
    // The theme is not a trust label: this proof is `依赖假设`, not
    // `需律师判断`, and the label-based exit code stays `0`.
    assert!(out.contains("信任：依赖假设"), "{out}");
    assert!(
        !out.contains("  需律师判断\n"),
        "the theme must not be merged into the trust label\n{out}"
    );
    // Two runs are byte-identical.
    let second = session(&file, &[], &[":labels 人身受到伤害 甲"]);
    assert_eq!(stdout(&output), stdout(&second));
}

#[test]
fn inspect_shows_which_risk_declaration_matched() {
    let dir = TempDir::new("inspect");
    let file = dir.write(
        "case.std",
        &themed_theory("人身安全", "人身受到伤害", "认定人身伤害", "遭受殴打"),
    );
    let output = session(&file, &[], &[":inspect"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("pred  人身受到伤害 : 人 → Prop 〔风险 人身安全〕"),
        "the predicate line must show the theme\n{out}"
    );
    assert!(
        out.contains("risk  人身安全 人身受到伤害"),
        "the marker's own ledger entry must be visible\n{out}"
    );
}

#[test]
fn an_unknown_risk_theme_fails_the_load() {
    let dir = TempDir::new("bad");
    let file = dir.write(
        "case.std",
        "sort 人\npred 伤害 : 人 → Prop\nrisk 危险 伤害\n",
    );
    let output = session(&file, &[], &[":why 伤害 甲"]);
    assert_exit(&output, GAP_OR_CONFLICT);
    let err = stderr(&output);
    assert!(err.contains("未知风险类别"), "{err}");
    assert!(
        err.contains("刑事"),
        "the diagnostic lists the allowed themes\n{err}"
    );
}

/// A helper that returns the certificate JSON of a `:cert` run.
fn certificate_json(output: &Output) -> String {
    let out = stdout(output);
    let start = out.find('{').unwrap_or_else(|| {
        panic!("`:cert` output has no JSON:\n{out}");
    });
    out[start..].to_owned()
}

#[test]
fn the_disclaimer_appears_once_in_all_four_commands_and_never_in_the_tree_or_json() {
    let dir = TempDir::new("disclaimer");
    let file = dir.write(
        "case.std",
        "sort 人\npred 违法 : 人 → Prop\npred 受罚 : 人 → Prop\nobj 甲 : 人\n\
         axiom 甲违法 : 违法 甲\n  source text \"案情\" locator \"一\"\n\
         rule 处罚 :\n  params p : 人\n  premise 违法 p\n  conclude 受罚 p\n  \
         source text \"测试法\" locator \"第一条\"\n",
    );
    for command in ["why", "explain", "labels"] {
        let output = session(&file, &[], &[&format!(":{command} 受罚 甲")]);
        assert_exit(&output, PROVED);
        let out = stdout(&output);
        assert_eq!(
            out.matches(DISCLAIMER).count(),
            1,
            "`:{command}` prints the disclaimer exactly once\n{out}"
        );
        assert!(
            out.contains(&format!("{DISCLAIMER}\n")),
            "the disclaimer is its own line\n{out}"
        );
        assert!(
            !out.contains(&format!("· {DISCLAIMER}")) && !out.contains(&format!("▸ {DISCLAIMER}")),
            "the disclaimer must not be inside a derivation line\n{out}"
        );
        let last = out.trim_end().lines().last().unwrap_or_default();
        assert_eq!(
            last, DISCLAIMER,
            "the disclaimer is the last line of the result\n{out}"
        );
    }

    let output = session(&file, &[], &[":cert 受罚 甲"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert_eq!(
        out.matches(MODEL_ONLY).count(),
        1,
        "`:cert` states the model-only disclaimer exactly once, before the JSON\n{out}"
    );
    assert!(
        out.contains("说明：这是模型内推导，不是法律意见。"),
        "{out}"
    );
    assert!(
        out.contains(PRIVACY),
        "`:cert` must carry the privacy notice\n{out}"
    );
    let json = certificate_json(&output);
    assert!(
        !json.contains(MODEL_ONLY) && !json.contains(PRIVACY),
        "the certificate JSON must not contain display text\n{json}"
    );
    assert!(
        json.contains("\"format_version\": 8"),
        "the certificate stays v8\n{json}"
    );
    assert!(
        !json.contains("\"disclaimer\"") && !json.contains("\"risk\""),
        "no field was added to the certificate\n{json}"
    );
}

#[test]
fn help_carries_the_disclaimer_the_privacy_notice_and_the_redact_option() {
    let output = run(&["--help".to_owned()]);
    assert_exit(&output, 0);
    let out = stdout(&output);
    assert!(out.contains(DISCLAIMER), "{out}");
    assert!(out.contains(PRIVACY), "{out}");
    assert!(out.contains("--redact"), "{out}");
    assert!(out.contains("risk <类别> <谓词>"), "{out}");
}
