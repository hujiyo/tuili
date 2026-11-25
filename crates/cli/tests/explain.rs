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
/// that adding `:explain` did not change the default output. The applicability
/// block is part of the current output: an unscoped case rule fires but says
/// that its scope was never declared.
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
▸ 不受侵犯 张三 甲宅  ⟨非法搜查即侵犯⟩〔适用性未判定（规则没有声明任何范围）〕 ← 「宪法第三十九条」
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

/// An unchecked applicability state is printed on the conclusion's own step:
/// the narrative form must not hide what `:why` labels.
#[test]
fn explain_labels_an_unchecked_applicability() {
    check(
        session("constitution-39.std", &[":explain 不受侵犯 张三 甲宅"]),
        PROVED,
        &[
            "【结论】「不受侵犯 张三 甲宅」由规则推出。 〔适用性未判定（规则没有声明任何范围）〕",
            "所以「不受侵犯 张三 甲宅」成立。 〔适用性未判定（规则没有声明任何范围）〕",
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
    let output = check(
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
            "时空适用性：",
            "⟨主张适用省条例⟩：适用性未判定（规则没有声明任何范围）",
            "⟨主张适用种子法⟩：适用性未判定（规则没有声明任何范围）",
            "证书有效，但根为缺口，结论未被证明。",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("冲突（未决）"),
        "the narrative already owns the conflict report:\n{out}"
    );
}

#[test]
fn explain_reports_a_rejected_conclusion_with_its_winner_and_basis() {
    let output = check(
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
    let out = stdout(&output);
    assert!(
        !out.contains("冲突（已裁决）"),
        "the narrative already owns the conflict report:\n{out}"
    );
    assert!(
        !out.contains("注：与「"),
        "the narrative already states the defeat:\n{out}"
    );
    assert!(
        !out.lines().any(|line| line.starts_with("  依据：")),
        "the narrative keeps its own indented basis line:\n{out}"
    );
    assert!(
        out.lines().any(|line| line.starts_with("     依据：")),
        "the narrative must keep its basis line:\n{out}"
    );
}

#[test]
fn explain_reports_a_defeated_loser_as_rejected_not_pending() {
    let output = check(
        session(
            "法律位阶-河南种子案-裁决.std",
            &[":explain 应适用 河南省农作物种子管理条例 汝阳种子公司案"],
        ),
        GAP_OR_CONFLICT,
        &[
            "【结论】「应适用 河南省农作物种子管理条例 汝阳种子公司案」未获证明（此处是缺口）。",
            "说明：目标已被否决：冲突已裁决，依据见冲突记录",
            "被否决：",
            "证书有效，但根为缺口，结论未被证明。",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("需要人工裁决"),
        "a defeated loser is not unresolved:\n{out}"
    );
    assert!(
        !out.contains("冲突（已裁决）"),
        "the narrative already owns the conflict report:\n{out}"
    );
    assert!(
        !out.contains("注：与「"),
        "the narrative already states the defeat:\n{out}"
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
