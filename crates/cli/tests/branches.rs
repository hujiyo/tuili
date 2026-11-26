//! End-to-end tests for `:branches` and the open-concept candidate hints.
//!
//! A branch is not a "possible conclusion": it is one independent derivation
//! with exactly one candidate interpretation enabled, its own certificate and
//! its own two-layer check. These tests pin the candidate criterion, the
//! report structure, the per-branch exit-code category, the 8-branch bound and
//! the session isolation: after `:branches`, the session's enabled set is the
//! one the user left.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const GAP: i32 = 1;
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

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-branches-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn write(&self, relative: &str, contents: &str) -> PathBuf {
        let path = self.path.join(relative);
        fs::write(&path, contents)
            .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn run_case(path: &Path, commands: &[&str]) -> Output {
    let mut args = vec!["--no-default-packs".to_owned(), path.display().to_string()];
    args.extend(commands.iter().map(|command| (*command).to_owned()));
    run(&args)
}

/// The acceptance case. `情节严重` is open and nothing derives `情节严重 甲`
/// for it, so the baseline is a gap. Two declared interpretations relate to the
/// blocked proposition:
///
/// * `解释B` states the same open predicate about another individual — a
///   same-head candidate whose branch stays a gap;
/// * `解释A` licenses exactly `情节严重 甲` — enabling a sourced interpretation
///   is the explicit human reading, so the branch releases the open-concept
///   obligation, labels as `依赖假设` and is classified `证明` with exit `0`.
const TWO_CANDIDATES: &str = r#"sort 人
pred 损害 : 人 → Prop
pred 重大 : 人 → Prop
pred 情节严重 : 人 → Prop
obj 甲 : 人
obj 乙 : 人
open 情节严重
axiom 损害事实 : 损害 甲
  source text "案件" locator "一"
axiom 重大事实 : 重大 乙
  source text "案件" locator "四"
interpret 解释A : 损害 甲 → 情节严重 甲
  direction literal
  source text "解释甲" locator "二" version "2020"
interpret 解释B : 重大 乙 → 情节严重 乙
  direction literal
  source text "解释乙" locator "三" version "2020"
"#;

#[test]
fn branches_report_each_candidate_with_its_own_result_and_check() {
    let temp = TempDir::new("two");
    let case = temp.write("case.std", TWO_CANDIDATES);
    let output = check(
        run_case(&case, &[":branches 情节严重 甲"]),
        PROVED,
        &[
            "分支重跑 `情节严重 甲`",
            "开放概念命题 1 个（基线证明图上的，含已由已启用解释许可的）：`情节严重 甲`",
            "候选解释 2 个（上限 8 个，按 id 排序；一次只启用一个，可单独启用）",
            "基线（不启用任何解释）：",
            "分支 1/2：`解释A`（损害 甲 → 情节严重 甲；精确匹配）",
            "分支 2/2：`解释B`（重大 乙 → 情节严重 乙；同谓词候选（另一主体/同谓词，需人工确认是否适用））",
            "根：已证明（情节严重 甲）",
            "信任：依赖假设",
            "归类：证明（退出码 0）",
            "证书校验：通过（逻辑层 cert::check + 内核层 kernel_proof）",
            "归类：缺口（退出码 1）",
            "与基线（不启用任何解释）对比：",
            "基线：缺口（1）",
            "启用 `解释A` 后：证明（0）",
            "启用 `解释B` 后：缺口（1）",
            "汇总（含基线）：证明 1 个，未决 0 个，缺口 2 个，冲突 0 个。",
        ],
    );
    let out = stdout(&output);
    // One branch is proved by the exact candidate; the same-head branch
    // licenses another individual and cannot prove this target.
    assert!(
        out.contains("分支 1/2：`解释A`"),
        "candidates are sorted by id:\n{out}"
    );
    assert!(
        !out.contains("开放概念：`情节严重`"),
        "the licensed concept is no longer reported as a pending judgement:\n{out}"
    );
}

#[test]
fn branches_do_not_change_the_sessions_enabled_set() {
    let temp = TempDir::new("isolation");
    let case = temp.write("case.std", TWO_CANDIDATES);
    // `:interpret list` after `:branches` must still show both as unenabled,
    // and `:why` must be the same text as if `:branches` had never run.
    let with_branches = run_case(&case, &[":branches 情节严重 甲", ":interpret list"]);
    assert_exit(&with_branches, PROVED);
    let out = stdout(&with_branches);
    assert!(
        out.contains("[未启用] 解释A") && out.contains("[未启用] 解释B"),
        "the temporary enable leaked into the session:\n{out}"
    );
    assert!(
        out.contains("解释（已启用 0 条，共 2 条）"),
        "the session enabled count changed:\n{out}"
    );

    let why_after_branches = run_case(&case, &[":branches 情节严重 甲", ":why 情节严重 甲"]);
    let why_alone = run_case(&case, &[":why 情节严重 甲"]);
    assert_exit(&why_after_branches, GAP);
    assert_exit(&why_alone, GAP);
    // Both runs must render the same `:why` block; only the branch report may
    // differ. The block starts at the derivation tree.
    let with_out = stdout(&why_after_branches);
    let alone = stdout(&why_alone);
    let marker = "? 情节严重 甲";
    let with_why = &with_out[with_out.rfind(marker).expect("why tree")..];
    let alone_why = &alone[alone.find(marker).expect("why tree")..];
    assert_eq!(
        with_why, alone_why,
        "`:why` after `:branches` differs from a fresh `:why`"
    );
    assert!(
        !with_why.contains("〈解释 解释A（literal）〉"),
        "`:why` must not apply an interpretation left enabled by `:branches`:\n{with_why}"
    );
}

/// A related interpretation is unavailable when its `from` does not hold; a
/// direction-reversed interpretation (its `from` is the blocked proposition)
/// is not a candidate at all.
const UNAVAILABLE_AND_REVERSED: &str = r#"sort 人
pred 损害 : 人 → Prop
pred 情节严重 : 人 → Prop
pred 从轻处罚 : 人 → Prop
pred 未持有 : 人 → Prop
obj 甲 : 人
obj 丙 : 人
open 情节严重
axiom 损害事实 : 损害 甲
  source text "案件" locator "一"
interpret 不可用解释 : 未持有 丙 → 情节严重 甲
  direction literal
  source text "解释" locator "二" version "2020"
interpret 反向解释 : 情节严重 甲 → 从轻处罚 甲
  direction literal
  source text "解释" locator "三" version "2020"
"#;

#[test]
fn unavailable_candidates_are_reported_with_reasons_and_reversed_ones_are_absent() {
    let temp = TempDir::new("unavailable");
    let case = temp.write("case.std", UNAVAILABLE_AND_REVERSED);
    let output = check(
        run_case(&case, &[":branches 情节严重 甲"]),
        GAP,
        &[
            "候选解释 0 个",
            "没有可用的候选解释",
            "相关但不可用 1 个（上限 8 个）：",
            "`不可用解释`：未持有 丙 → 情节严重 甲（from 在解释应用前的事实集（已登记事实与规则结论）里不成立）",
        ],
    );
    let out = stdout(&output);
    let report = &out[out.find("分支重跑").expect("branch report")..];
    assert!(
        !report.contains("反向解释"),
        "a direction-reversed interpretation must not be listed as a candidate:\n{report}"
    );
    assert!(
        !report.contains("分支 1/"),
        "no branch can run without a usable candidate:\n{report}"
    );
}

fn many_candidates(count: usize) -> String {
    let mut theory = String::from(
        "sort 人\npred 情节严重 : 人 → Prop\npred 触发 : 人 → Prop\nobj 甲 : 人\nopen 情节严重\n\
         axiom 事实 : 触发 甲\n  source text \"案件\" locator \"一\"\n",
    );
    // All candidates exact and usable: the target is a gap until one is
    // enabled, and every branch releases the open-concept obligation. The cap
    // must keep the first eight by id and name what it left out.
    for index in 0..count {
        theory.push_str(&format!(
            "interpret 解释{} : 触发 甲 → 情节严重 甲\n  direction literal\n  \
             source text \"解释{index}\" locator \"{index}\" version \"2020\"\n",
            (b'A' + index as u8) as char
        ));
    }
    theory
}

#[test]
fn more_than_eight_candidates_are_truncated_with_the_omitted_ids() {
    let temp = TempDir::new("cap");
    let case = temp.write("case.std", &many_candidates(10));
    let output = check(
        run_case(&case, &[":branches 情节严重 甲"]),
        PROVED,
        &[
            "候选解释 8 个（上限 8 个",
            "候选解释超过上限 8 个：已截断，未列出 ⟨解释I⟩、⟨解释J⟩",
            "分支 8/8：",
            "汇总（含基线）",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("分支 9/"),
        "the bound must never run a ninth branch:\n{out}"
    );
}

#[test]
fn the_baseline_is_the_sessions_enabled_set_and_a_duplicate_to_is_unavailable() {
    let temp = TempDir::new("enabled-baseline");
    let case = temp.write("case.std", TWO_CANDIDATES);
    let mut args = vec![
        "--no-default-packs".to_owned(),
        "--interpret".to_owned(),
        "解释B".to_owned(),
        case.display().to_string(),
        ":branches 情节严重 甲".to_owned(),
        ":interpret list".to_owned(),
    ];
    args.shrink_to_fit();
    let output = check(
        run(&args),
        PROVED,
        &[
            "基线（会话已启用的解释：`解释B`）",
            "分支 1/1：`解释A`",
            "解释（已启用 1 条，共 2 条）",
            "[已启用] 解释B",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("分支 2/"),
        "an already enabled interpretation is part of the baseline, not a branch:\n{out}"
    );
}

#[test]
fn a_duplicate_to_of_an_enabled_interpretation_is_unavailable() {
    let temp = TempDir::new("duplicate-to");
    let theory = TWO_CANDIDATES.to_owned()
        + "interpret 解释C : 重大 乙 → 情节严重 乙\n  direction literal\n  \
           source text \"解释丙\" locator \"五\" version \"2020\"\n";
    let case = temp.write("case.std", &theory);
    let output = check(
        run(
            &[
                "--no-default-packs".to_owned(),
                "--interpret".to_owned(),
                "解释B".to_owned(),
                case.display().to_string(),
                ":branches 情节严重 甲".to_owned(),
            ],
        ),
        PROVED,
        &[
            "相关但不可用 1 个（上限 8 个）：",
            "`解释C`：重大 乙 → 情节严重 乙（to 与已启用的解释 `解释B` 在内核下等价，两者不能同时启用）",
        ],
    );
    let out = stdout(&output);
    assert!(
        out.contains("候选解释 1 个"),
        "only `解释A` remains usable:\n{out}"
    );
}

#[test]
fn the_same_case_produces_byte_identical_branch_reports() {
    let temp = TempDir::new("determinism");
    let case = temp.write("case.std", TWO_CANDIDATES);
    let first = run_case(&case, &[":branches 情节严重 甲"]);
    assert_exit(&first, PROVED);
    let second = run_case(&case, &[":branches 情节严重 甲"]);
    assert_exit(&second, PROVED);
    assert_eq!(
        stdout(&first),
        stdout(&second),
        "the branch report must be reproducible byte for byte"
    );
}

#[test]
fn gap_and_why_and_issues_list_candidates_without_enabling_them() {
    let temp = TempDir::new("hints");
    let case = temp.write("case.std", TWO_CANDIDATES);
    for command in [":why 情节严重 甲", ":gap 情节严重 甲"] {
        let output = check(
            run_case(&case, &[command]),
            GAP,
            &[
                "受阻的开放概念：`情节严重 甲`",
                "候选解释（不自动启用；一次只启用一个，不枚举组合）：`解释A`",
                "用 :branches 情节严重 甲 查看每个解释单独启用后的后果（不会自动启用）。",
            ],
        );
        let out = stdout(&output);
        assert!(
            !out.contains("〈解释 解释A（literal）〉"),
            "the hint must not enable the interpretation:\n{out}"
        );
    }

    let issues_case = temp.write(
        "issues.std",
        r#"sort 人
pred 损害 : 人 → Prop
pred 情节严重 : 人 → Prop
pred 应重罚 : 人 → Prop
obj 甲 : 人
open 情节严重
axiom 损害事实 : 损害 甲
  source text "案件" locator "一"
interpret 解释A : 损害 甲 → 情节严重 甲
  direction literal
  source text "解释甲" locator "二" version "2020"
rule 重罚规则 :
  params x : 人
  premise 情节严重 x
  conclude 应重罚 x
  source text "规则" locator "三"
"#,
    );
    let issues = check(
        run_case(&issues_case, &[":issues"]),
        GAP,
        &[
            "受阻的开放概念：`情节严重 甲`",
            "候选解释（不自动启用；一次只启用一个，不枚举组合）：`解释A`",
            "用 :branches 应重罚 甲 查看每个解释单独启用后的后果（不会自动启用）。",
        ],
    );
    assert_eq!(
        stdout(&issues).matches("受阻的开放概念：").count(),
        1,
        "the issue scan names the blocked concept once for the issue:\n{}",
        stdout(&issues)
    );
}

#[test]
fn an_open_concept_without_candidates_says_so_in_the_hint() {
    let temp = TempDir::new("no-candidates");
    let case = temp.write(
        "case.std",
        "sort 人\npred 情节严重 : 人 → Prop\nobj 甲 : 人\nopen 情节严重\n",
    );
    let output = check(
        run_case(&case, &[":why 情节严重 甲", ":branches 情节严重 甲"]),
        GAP,
        &[
            "没有可用的候选解释：当前环境没有与受阻的开放概念命题相关的 `interpret` 声明",
            "候选解释 0 个（上限 8 个",
            "开放概念命题 1 个（基线证明图上的，含已由已启用解释许可的）：`情节严重 甲`",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("候选解释（不自动启用"),
        "an empty candidate table must never be printed:\n{out}"
    );
    assert!(
        out.contains("候选解释 0 个（上限 8 个"),
        "the branch report must state the usable count explicitly:\n{out}"
    );
}

#[test]
fn review_lists_candidates_and_names_them_in_the_questions() {
    let temp = TempDir::new("review");
    let case = temp.write("case.std", TWO_CANDIDATES);
    let output = check(
        run_case(&case, &[":review 情节严重 甲"]),
        GAP,
        &[
            "## 七、需人判断",
            "开放概念的候选解释（证明图上的开放概念命题 1 个）：",
            "`解释A`：损害 甲 → 情节严重 甲〔精确匹配：与开放概念命题「情节严重 甲」内核等价，启用后许可该命题〕",
            "`解释B`：重大 乙 → 情节严重 乙〔同谓词候选（另一主体/同谓词，需人工确认是否适用）：与开放概念命题「情节严重 甲」同谓词，但不是同一命题〕",
            "本报告只列当前环境声明的候选，不运行分支，也不建议采用某一条。",
            "## 八、建议向律师确认的问题",
            "候选解释 `解释A`、`解释B` 都可能影响对开放概念命题「情节严重 甲」的判断",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("分支 1/"),
        "the review must not invent branch results:\n{out}"
    );
}

#[test]
fn a_case_without_open_concepts_gets_no_branch_lines() {
    let temp = TempDir::new("no-open");
    let case = temp.write(
        "case.std",
        "sort 人\npred 受罚 : 人 → Prop\nobj 甲 : 人\n\
         axiom 事实 : 受罚 甲\n  source text \"案件\" locator \"一\"\n",
    );
    let output = check(
        run_case(&case, &[":why 受罚 甲"]),
        PROVED,
        &["推导已通过独立校验。"],
    );
    let out = stdout(&output);
    for needle in ["候选解释", ":branches", "受阻的开放概念", "此处需人判断"] {
        assert!(
            !out.contains(needle),
            "a closed proof must not gain an open-concept line {needle:?}:\n{out}"
        );
    }
}

#[test]
fn branches_requires_a_loaded_theory_and_a_goal() {
    let output = run(&[":branches 受罚 甲".to_owned()]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(
        err.contains("尚未加载理论"),
        "an unloaded session must refuse the command:\n{err}"
    );

    let temp = TempDir::new("usage");
    let case = temp.write("case.std", TWO_CANDIDATES);
    let empty = run_case(&case, &[":branches"]);
    assert_exit(&empty, ERROR);
    assert!(
        stderr(&empty).contains("用法：:branches <目标命题>"),
        "the command needs a goal:\n{}",
        stderr(&empty)
    );
}
