//! End-to-end tests for `:explain` and for the unchanged default `:why`
//! output. The narrative is derived from the same certificate `:why` checks;
//! these tests run the real binary so the explicit switch and the exit codes
//! are exercised too.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const PROVED: i32 = 0;
const GAP_OR_CONFLICT: i32 = 1;
const COMMAND_ERROR: i32 = 2;

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

/// Run the CLI from the repository root. `lawpacks/` is resolved relative to
/// the working directory, so the default environment is the repository one.
fn run(commands: Vec<String>) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(commands)
        .output()
        .unwrap_or_else(|e| panic!("failed to run the CLI: {e}"))
}

fn session(name: &str, commands: &[&str]) -> Output {
    let mut all = vec![format!(":load {}", example(name))];
    all.extend(commands.iter().map(|command| command.to_string()));
    run(all)
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

/// The whole stdout of the documented `:why` query, byte for byte. There is no
/// snapshot file in this repository, so this constant is the regression test
/// that adding `:explain` did not change the default output.
const CONSTITUTION_39_WHY: &str = "\
默认环境 cn.default：已加载 1 个包
  cn.constitution@0.4.0（official）
已加载 `examples/constitution-39.std`。
  + 公民
  + 住宅
  + 行为
  + 不受侵犯
  + 非法搜查
  + 非法侵入
  + 依法搜查
  + 张三
  + 甲宅
  + 某次搜查非法
  + 非法搜查即侵犯
  + 依法搜查不侵犯
▸ 不受侵犯 张三 甲宅  ⟨非法搜查即侵犯⟩ ← 「宪法第三十九条」
  实例：p ↦ 张三，h ↦ 甲宅
  · 非法搜查 张三 甲宅  〔用户陈述〕  [某次搜查非法]  ← 「示例案情某次搜查」

推导已通过独立校验。
";

#[test]
fn default_why_output_is_byte_identical() {
    let output = run(vec![
        ":load examples/constitution-39.std".to_owned(),
        ":why 不受侵犯 张三 甲宅".to_owned(),
    ]);
    assert_eq!(output.status.code(), Some(PROVED), "{}", stderr(&output));
    assert_eq!(stdout(&output), CONSTITUTION_39_WHY);
}

#[test]
fn explain_prints_a_because_so_narrative_with_sources_and_instances() {
    check(
        session("constitution-39.std", &[":explain 不受侵犯 张三 甲宅"]),
        PROVED,
        &[
            "【结论】「不受侵犯 张三 甲宅」由规则推出。",
            "【推理过程】",
            "1. 据用户陈述，「非法搜查 张三 甲宅」成立",
            "因为「非法搜查 张三 甲宅」（第 1 条），根据规则「非法搜查即侵犯」，所以「不受侵犯 张三 甲宅」成立。",
            "实例：p ↦ 张三，h ↦ 甲宅",
            "来源：「示例案情某次搜查」；说明：教学示例事实，非真实证据",
            "来源：「宪法第三十九条」",
            "推导已通过独立校验。",
        ],
    );
}

#[test]
fn explain_keeps_the_formal_tree_available_through_why() {
    let output = session(
        "constitution-39.std",
        &[":explain 不受侵犯 张三 甲宅", ":why 不受侵犯 张三 甲宅"],
    );
    check(
        output,
        PROVED,
        &["【结论】", "▸ 不受侵犯 张三 甲宅", "推导已通过独立校验。"],
    );
}

#[test]
fn explain_reports_a_gap_and_exits_one() {
    check(
        session("宪法案例-孙志刚.std", &[":explain 应当收容 孙志刚"]),
        GAP_OR_CONFLICT,
        &[
            "【结论】「应当收容 孙志刚」未获证明（此处是缺口）。",
            "【缺口】",
            "缺少前提",
            "证书有效，但根为缺口，结论未被证明。",
        ],
    );
}

#[test]
fn explain_reports_an_unresolved_conflict_as_pending() {
    check(
        session(
            "法律位阶-河南种子案-冲突.std",
            &[":explain 应适用 种子法 汝阳种子公司案"],
        ),
        GAP_OR_CONFLICT,
        &[
            "【结论】",
            "【冲突】",
            "冲突，此处未决。",
            "     原因：",
            "证书有效，但根为缺口，结论未被证明。",
        ],
    );
}

#[test]
fn explain_reports_a_rejected_conclusion_with_its_winner_and_basis() {
    check(
        session(
            "法律位阶-河南种子案-裁决.std",
            &[":explain 应适用 种子法 汝阳种子公司案"],
        ),
        PROVED,
        &[
            "【结论】「应适用 种子法 汝阳种子公司案」由规则推出。",
            "【冲突】",
            "已裁决",
            "胜出：",
            "被否决：",
            "依据：",
            "推导已通过独立校验。",
        ],
    );
}

#[test]
fn explain_without_a_goal_is_a_command_error() {
    let output = session("constitution-39.std", &[":explain"]);
    let code = output.status.code();
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(code, Some(COMMAND_ERROR), "stdout:\n{out}\nstderr:\n{err}");
    assert!(err.contains("错误："), "{err}");
    assert!(!out.contains("【结论】"), "{out}");
}
