//! End-to-end tests for the recursive gap tree and the `:issues` command.
//!
//! `:gap` now expands each missing premise into its own gap until a fact, a
//! rule-less proposition or a rule cycle is reached, and every expansion is
//! bounded by explicit limits that must be reported instead of silently
//! truncating. `:issues` scans the whole fact set for contestable conclusions.

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

fn run(arguments: Vec<String>) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(arguments)
        .output()
        .unwrap_or_else(|e| panic!("failed to run the CLI: {e}"))
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
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
            "std-deduce-gap-tree-{}-{tag}-{n}.std",
            std::process::id()
        ));
        fs::write(&path, source).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        TempTheory { path }
    }

    fn session(&self, commands: &[&str]) -> Output {
        // The scan under test belongs to the theory alone: do not let the
        // repository's default legal environment add its own rules.
        let mut all = vec![
            "--no-default-packs".to_string(),
            format!(":load {}", self.path.display()),
        ];
        all.extend(commands.iter().map(|command| command.to_string()));
        run(all)
    }
}

impl Drop for TempTheory {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
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

/// A two-step gap: `目标` misses `中间` and `另一`; `中间` misses `基础`;
/// `另一` and `基础` have no rule at all.
const TWO_STEPS: &str = r#"
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
  source text "测试" locator "目标规则"

rule 中间规则 :
  params p : 人
  premise 基础 p
  conclude 中间 p
  source text "测试" locator "中间规则"
"#;

#[test]
fn gap_prints_a_recursive_tree_with_every_missing_premise_expanded() {
    let theory = TempTheory::new("recursive-gap", TWO_STEPS);
    let output = check(
        theory.session(&[":gap 目标 张三"]),
        GAP,
        &[
            "无法推出 目标 张三",
            "缺口树（最大深度 6，最多 128 个节点，每条规则最多尝试 8 次）",
            "缺口 ⟨目标 张三⟩",
            "候选 ⟨目标规则⟩",
            "缺 ⟨中间 张三⟩",
            "候选 ⟨中间规则⟩",
            "缺 ⟨基础 张三⟩",
            "缺 ⟨另一 张三⟩",
        ],
    );
    let out = stdout(&output);
    assert_eq!(
        out.matches("没有任何规则以它为结论").count(),
        2,
        "基础 and 另一 are fact leaves:\n{out}"
    );
    assert!(
        !out.contains("已截断"),
        "this tree is inside every default limit:\n{out}"
    );

    // The nested gap belongs to its missing premise: it is indented deeper
    // than the `缺` line and appears before the next premise.
    let position = |needle: &str| {
        out.find(needle)
            .unwrap_or_else(|| panic!("missing {needle:?} in:\n{out}"))
    };
    let middle_premise = position("缺 ⟨中间 张三⟩");
    let middle_rule = position("候选 ⟨中间规则⟩");
    let base = position("缺 ⟨基础 张三⟩");
    let other = position("缺 ⟨另一 张三⟩");
    assert!(
        middle_premise < middle_rule && middle_rule < base && base < other,
        "the tree nests each premise's gap under that premise:\n{out}"
    );
}

#[test]
fn issues_lists_every_contestable_conclusion_and_succeeds_when_there_is_none() {
    let theory = TempTheory::new(
        "issues-scan",
        r#"
sort 人
pred 健在 : 人 → Prop
pred 有住所 : 人 → Prop
pred 失踪 : 人 → Prop
obj 乙 : 人

rule 宣告失踪 :
  params p : 人
  premise 健在 p
  premise 有住所 p
  conclude 失踪 p
  source text "民法典" locator "第四十条"
"#,
    );
    check(
        theory.session(&[":issues"]),
        GAP,
        &[
            "当前事实集下可争的结论 1 条",
            "争点 ⟨失踪 乙⟩",
            "候选 ⟨宣告失踪⟩",
            "← 「民法典第四十条」",
            "缺 ⟨健在 乙⟩",
            "缺 ⟨有住所 乙⟩",
        ],
    );
    // Fill both premises: the only rule now fires, so nothing is contestable.
    let proved = check(
        theory.session(&[":given 健在 乙", ":given 有住所 乙", ":issues"]),
        PROVED,
        &["没有可争的结论。"],
    );
    let out = stdout(&proved);
    assert!(
        !out.contains("争点"),
        "a proved conclusion is not an issue:\n{out}"
    );
    // `:issues` answers the whole fact set; a goal is not an argument.
    let rejected = theory.session(&[":issues 失踪 乙"]);
    assert_eq!(
        rejected.status.code(),
        Some(COMMAND_ERROR),
        "an argument is a usage error\nstdout:\n{}",
        stdout(&rejected)
    );
    assert!(
        stderr(&rejected).contains(":issues（不接受参数"),
        "stderr must explain the usage:\n{}",
        stderr(&rejected)
    );
}

#[test]
fn a_deep_chain_is_truncated_at_the_depth_limit_and_says_so() {
    let mut source = String::from("sort 人\nobj 张三 : 人\n");
    for level in 0..9 {
        source.push_str(&format!("pred 层{level} : 人 → Prop\n"));
    }
    for level in 0..8 {
        source.push_str(&format!(
            "rule 规则{level} :\n  params p : 人\n  premise 层{} p\n  conclude 层{level} p\n  source text \"测试\" locator \"规则{level}\"\n",
            level + 1
        ));
    }
    let theory = TempTheory::new("depth-limit", &source);
    let output = check(
        theory.session(&[":gap 层0 张三"]),
        GAP,
        &[
            "无法推出 层0 张三",
            "已截断：达到最大展开深度（6 层）；其余缺口不再展开。",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("缺 ⟨层8 张三⟩"),
        "the expansion stops at the depth limit:\n{out}"
    );
}

#[test]
fn the_issue_list_is_truncated_at_its_limit_and_says_so() {
    // One rule per contestable conclusion: the per-rule attempt cap cannot be
    // what stops this scan, so the issue cap is what the test pins down.
    let mut source = String::from("sort 人\npred 条件 : 人 → Prop\nobj 甲 : 人\n");
    for index in 0..33 {
        source.push_str(&format!("pred 状态{index} : 人 → Prop\n"));
    }
    for index in 0..33 {
        source.push_str(&format!(
            "rule 规则{index} :\n  params p : 人\n  premise 条件 p\n  conclude 状态{index} p\n  source text \"测试\" locator \"规则{index}\"\n"
        ));
    }
    let theory = TempTheory::new("issue-limit", &source);
    let output = check(
        theory.session(&[":issues"]),
        GAP,
        &[
            "当前事实集下可争的结论 32 条",
            "已截断：可争的结论已达到上限（32 条）；其余未列出。",
        ],
    );
    let out = stdout(&output);
    assert_eq!(
        out.matches("争点 ⟨").count(),
        32,
        "the cap is exactly the reported number of issues:\n{out}"
    );
}
