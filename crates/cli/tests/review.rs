//! End-to-end tests for `:review`, the Markdown lawyer review report.
//!
//! The three example theories live in `examples/`. The tests pin the report's
//! section structure, the three accepted scenarios (a closed strict-fact
//! proof, a user-claim gap and an open concept with an effective range), the
//! query-derived questions, byte-identical repeated output, the file mode and
//! the escaping boundary.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const NOT_PROVED: i32 = 1;
const COMMAND_ERROR: i32 = 2;

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-review-{}-{tag}-{n}",
            std::process::id()
        ));
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

/// Run the CLI from the repository root without the default environment.
fn run(args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .arg("--no-default-packs")
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn session(file: &str, options: &[&str], commands: &[&str]) -> Output {
    let mut all = Vec::new();
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

fn assert_contains(haystack: &str, needles: &[&str], what: &str) {
    for needle in needles {
        assert!(
            haystack.contains(needle),
            "{what} does not contain {needle:?}\n---\n{haystack}"
        );
    }
}

/// The report starts at its first heading; the load report before it is not
/// part of the Markdown.
fn report_part(out: &str) -> &str {
    let marker = "# 律师复核报告";
    let index = out
        .find(marker)
        .unwrap_or_else(|| panic!("stdout has no report heading:\n{out}"));
    &out[index..]
}

fn section<'a>(report: &'a str, heading: &str) -> &'a str {
    let marker = format!("## {heading}");
    let index = report
        .find(&marker)
        .unwrap_or_else(|| panic!("report has no section {heading:?}:\n{report}"))
        + marker.len();
    let rest = &report[index..];
    match rest.find("\n## ") {
        Some(end) => &rest[..end],
        None => rest,
    }
}

/// Top-level numbered items in a section. Nested bullets start with spaces and
/// are not counted.
fn top_level_items(section: &str) -> Vec<usize> {
    section
        .lines()
        .filter_map(|line| {
            let (number, _) = line.split_once(". ")?;
            number.parse::<usize>().ok()
        })
        .collect()
}

/// Every `〔见「…」第 N 条〕` anchor in one line.
fn anchors(line: &str) -> Vec<(&str, usize)> {
    let mut found = Vec::new();
    let mut rest = line;
    while let Some(start) = rest.find("〔见「") {
        let after = &rest[start + "〔见".len()..];
        let inner = after
            .strip_prefix('「')
            .unwrap_or_else(|| panic!("anchor has no section name: {line:?}"));
        let close = inner
            .find('」')
            .unwrap_or_else(|| panic!("unclosed section name in question: {line:?}"));
        let name = &inner[..close];
        let after_name = &inner[close + '」'.len_utf8()..];
        let after_prefix = after_name
            .strip_prefix("第 ")
            .unwrap_or_else(|| panic!("anchor has no item number: {line:?}"));
        let end = after_prefix
            .find(" 条〕")
            .unwrap_or_else(|| panic!("anchor has no 条 marker: {line:?}"));
        let number: usize = after_prefix[..end]
            .parse()
            .unwrap_or_else(|_| panic!("anchor item is not a number: {line:?}"));
        found.push((name, number));
        rest = &after_prefix[end + " 条〕".len()..];
    }
    found
}

fn heading_for(short: &str) -> &'static str {
    match short {
        "争点" => "二、争点",
        "规则与出处" => "三、规则与出处",
        "事实账本" => "四、事实账本",
        "缺口与举证" => "五、缺口与举证",
        "未决与冲突" => "六、未决与冲突",
        "需人判断" => "七、需人判断",
        other => panic!("unknown section name in a question anchor: {other:?}"),
    }
}

/// Extract the quoted values after `prefix` (for example `规则「`).
fn quoted_values<'a>(line: &'a str, prefix: &str) -> Vec<&'a str> {
    let mut values = Vec::new();
    let mut rest = line;
    while let Some(start) = rest.find(prefix) {
        let after = &rest[start + prefix.len()..];
        let Some(close) = after.find('」') else {
            break;
        };
        values.push(&after[..close]);
        rest = &after[close + '」'.len_utf8()..];
    }
    values
}

/// Assert every numbered question has an anchor, the anchor's item exists, and
/// every rule or concept the question names also exists in its own section.
fn assert_questions_are_grounded(report: &str) {
    let questions = section(report, "八、建议向律师确认的问题");
    for line in questions.lines() {
        let trimmed = line.trim_start();
        let Some((number, _)) = trimmed.split_once(". ") else {
            continue;
        };
        if number.parse::<usize>().is_err() {
            continue;
        }
        let references = anchors(line);
        assert!(
            !references.is_empty(),
            "a numbered question must reference an existing item: {line:?}"
        );
        for (short, item) in references {
            let body = section(report, heading_for(short));
            assert!(
                top_level_items(body).contains(&item),
                "question points at {short} item {item}, which does not exist:\n{body}"
            );
        }
        // A question names a rule, a concept, a contestable conclusion or the
        // root conclusion; each named item must be present in its section.
        let rules_section = section(report, "三、规则与出处");
        for rule in quoted_values(line, "规则「") {
            assert!(
                rules_section.contains(&format!("规则「{rule}」")),
                "question names rule {rule:?}, which the rules section does not list:\n{line}"
            );
        }
        let concepts_section = section(report, "七、需人判断");
        for concept in quoted_values(line, "开放概念「") {
            assert!(
                concepts_section.contains(&format!("开放概念「{concept}」")),
                "question names concept {concept:?}, which the human-judgement section does not list:\n{line}"
            );
        }
        let issues_section = section(report, "二、争点");
        for issue in quoted_values(line, "争点「") {
            assert!(
                issues_section.contains(&format!("「{issue}」")),
                "question names issue {issue:?}, which the issues section does not list:\n{line}"
            );
        }
        let gaps_section = section(report, "五、缺口与举证");
        for goal in quoted_values(line, "结论「") {
            assert!(
                gaps_section.contains(&format!("结论「{goal}」")),
                "question names root {goal:?}, which the gap section does not list:\n{line}"
            );
        }
    }
}

const CLOSED: &str = "examples/复核-闭合证明.std";
const CLAIM_GAP: &str = "examples/复核-用户陈述与缺口.std";
const OPEN_CONCEPT: &str = "examples/复核-开放概念与生效区间.std";
const THREE_LEVEL: &str = "examples/复核-三层缺口.std";

#[test]
fn closed_strict_fact_proof_is_verified_and_has_no_gap() {
    let output = session(CLOSED, &[], &[":review 受罚 张三"]);
    assert_exit(&output, PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &[
            "# 律师复核报告",
            "不是法律意见",
            "**结论命题：**「受罚 张三」",
            "**根是否可达（即本次推导是否证明了结论）：**是",
            "「已验证」：成立",
            "模型内：结论的证明只使用严格事实（法院查明 1 条、双方无争议 0 条）",
            "## 二、争点",
            "当前事实集下没有可争的结论",
            "规则「处罚」",
            "文本：「示例法」；条号：「第一条」；版本：「2024」",
            "法院查明（严格事实）",
            "## 五、缺口与举证",
            "结论已证明，当前事实集下也没有可争结论，因此没有缺口",
            "## 七、需人判断",
            "本案推导没有记录开放概念、需人判断事项或案件扩展",
            "〔见「规则与出处」第 1 条〕",
        ],
        "closed proof report",
    );
    assert!(
        !report.contains("法律意见：正确"),
        "the report must not dress itself up as a legal opinion:\n{report}"
    );
    assert_questions_are_grounded(report);
}

#[test]
fn user_claim_gap_reports_fact_needs_evidence_burden_and_missing_premise() {
    let output = session(CLAIM_GAP, &[], &[":review 受罚 张三"]);
    assert_exit(&output, NOT_PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &[
            "事实待举证",
            "**根是否可达（即本次推导是否证明了结论）：**否（结论未获证明）",
            "「违法 张三」：身份：用户陈述（主张，不是证明）",
            "结论缺口已掌握的材料",
            "1. 结论「受罚 张三」未获证明（缺口）",
            "候选规则「处罚」",
            "缺：「故意 张三」",
            "举证责任：主张方",
            "证明标准：优势证据",
            "判定口径：按已持有事实；补上缺失前提后判定可能变化。",
            "例外举证：未声明举证责任",
            "例外证明标准：未声明证明标准",
            "没有任何规则以这个命题为结论",
            "〔见「缺口与举证」第 1 条〕",
        ],
        "user-claim gap report",
    );
    assert_questions_are_grounded(report);
}

#[test]
fn proved_user_claim_reports_depends_on_assumption_and_gap_issue() {
    let output = session(CLAIM_GAP, &[], &[":review 警告 张三"]);
    assert_exit(&output, PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &[
            "「依赖假设」：成立（据用户陈述 1 条）",
            "**根是否可达（即本次推导是否证明了结论）：**是",
            "1. 「受罚 张三」：候选规则「处罚」；缺少前提合计 1 条",
            "1. 争点「受罚 张三」的缺口",
        ],
        "proved claim report",
    );
    assert_questions_are_grounded(report);
}

#[test]
fn open_concept_with_effective_range_reports_lawyer_judgment_and_basis() {
    let output = session(
        OPEN_CONCEPT,
        &["--jurisdiction", "CN"],
        &[":review 严重情节 张三"],
    );
    assert_exit(&output, NOT_PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &[
            "「需律师判断」：成立",
            "开放概念「严重情节」：需要人来解释的法律用语",
            "所在推导步骤",
            "推导步骤 1（规则「认定严重」的结论「严重情节 张三」）",
            "为什么不能自动判定",
            "适用（事件时间 2005-05-06（区间内）",
            "生效范围 2000-01-01..2010-01-01（开始：规则；结束：规则）",
            "管辖 CN（规则）",
            "地域 CN-HN（规则）",
            "开放概念「严重情节」不能由模型自动判定",
            "〔见「需人判断」第 1 条〕",
        ],
        "open concept report",
    );
    assert_questions_are_grounded(report);
}

#[test]
fn the_same_case_twice_is_byte_identical() {
    for file in [CLOSED, CLAIM_GAP, OPEN_CONCEPT, THREE_LEVEL] {
        let options: &[&str] = if file == OPEN_CONCEPT {
            &["--jurisdiction", "CN"]
        } else {
            &[]
        };
        let command = if file == OPEN_CONCEPT {
            ":review 严重情节 张三"
        } else if file == THREE_LEVEL {
            ":review 应罚 张三"
        } else {
            ":review 受罚 张三"
        };
        let first = session(file, options, &[command]);
        let second = session(file, options, &[command]);
        assert_exit(&first, if file == CLOSED { PROVED } else { NOT_PROVED });
        assert_eq!(
            first.stdout, second.stdout,
            "two processes must produce byte-identical reports for {file}"
        );
    }
}

#[test]
fn an_unresolved_conflict_reports_both_sides_and_the_reason() {
    let output = session(
        "examples/法律位阶-河南种子案-冲突.std",
        &[],
        &[":review 应适用 种子法 汝阳种子公司案"],
    );
    assert_exit(&output, NOT_PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &[
            "争点未决",
            "## 六、未决与冲突",
            "1. 未决冲突：「应适用 河南省农作物种子管理条例 汝阳种子公司案」与「应适用 种子法 汝阳种子公司案」",
            "- 左侧：",
            "- 右侧：",
            "未决原因：",
            "两侧规则之间没有声明优先级",
            "〔见「未决与冲突」第 1 条〕",
        ],
        "unresolved conflict report",
    );
    assert_questions_are_grounded(report);
}

#[test]
fn file_mode_writes_the_whole_report_and_reports_a_path_with_spaces() {
    let temp = TempDir::new("path");
    let directory = temp.path.join("报告 目录");
    fs::create_dir_all(&directory).expect("create report directory");
    let destination = directory.join("复核 报告.md");
    let quoted = format!("\"{}\"", destination.display());
    let command = format!(":review 受罚 张三 --out {quoted}");
    let written = session(CLAIM_GAP, &[], &[command.as_str()]);
    assert_exit(&written, NOT_PROVED);
    let stdout_text = stdout(&written);
    assert!(
        stdout_text.contains("已写入复核报告："),
        "file mode must report the path:\n{stdout_text}"
    );
    assert!(
        !stdout_text.contains("# 律师复核报告"),
        "file mode must not also print the report to stdout:\n{stdout_text}"
    );
    let file_text = fs::read_to_string(&destination)
        .unwrap_or_else(|error| panic!("read {}: {error}", destination.display()));
    assert!(
        file_text.starts_with("# 律师复核报告"),
        "the written file is not the report:\n{file_text}"
    );
    assert!(
        file_text.ends_with('\n'),
        "the report must end with a newline"
    );

    // The stdout form is the same Markdown, so the two forms cannot diverge.
    let stdout_report = session(CLAIM_GAP, &[], &[":review 受罚 张三"]);
    assert_exit(&stdout_report, NOT_PROVED);
    let stdout_text = stdout(&stdout_report);
    assert_eq!(
        file_text,
        report_part(&stdout_text),
        "file mode and stdout mode must contain the same report"
    );
}

#[test]
fn a_gap_chain_past_the_depth_limit_prints_the_truncation_marker() {
    let temp = TempDir::new("depth-limit");
    let mut theory = String::from("sort 人\nobj 张三 : 人\n");
    for index in 0..=8 {
        theory.push_str(&format!("pred P{index} : 人 → Prop\n"));
    }
    for index in 0..8 {
        theory.push_str(&format!(
            "rule R{index} :\n  params p : 人\n  premise P{next} p\n  conclude P{index} p\n  source text \"示例法\" locator \"第{index}条\"\n",
            next = index + 1
        ));
    }
    let path = temp.write("deep.std", &theory);
    let output = run(&[path, ":review P0 张三".to_owned()]);
    assert_exit(&output, NOT_PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &["已截断：达到最大展开深度（6 层）", "其余缺口不再展开"],
        "truncated gap report",
    );
}

#[test]
fn three_level_gap_expands_to_the_leaf_and_keeps_each_layer_burden() {
    let output = session(THREE_LEVEL, &[], &[":review 应罚 张三"]);
    assert_exit(&output, NOT_PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &[
            "1. 结论「应罚 张三」未获证明（缺口）",
            "缺：「情节严重 张三」",
            "缺：「损害 张三」",
            "缺：「行为 张三」",
            "没有任何规则以这个命题为结论",
            "举证责任：主张方",
            "证明标准：优势证据",
            "证明标准：清楚可信",
            "举证责任：相对方",
            "「已确认 张三」：身份：用户陈述（主张，不是证明）；与结论的关系：结论缺口已掌握的材料",
        ],
        "three-level gap report",
    );
    assert_eq!(
        report.matches("子缺口：").count(),
        6,
        "the root tree has three nested levels and each contestable conclusion repeats its own subtree:\n{report}"
    );
    assert_questions_are_grounded(report);
}

#[test]
fn file_mode_accepts_an_unquoted_path_with_spaces() {
    let temp = TempDir::new("unquoted-path");
    let destination = temp.path.join("复核 报告 未加引号.md");
    let command = format!(":review 受罚 张三 --out {}", destination.display());
    let output = session(CLAIM_GAP, &[], &[command.as_str()]);
    assert_exit(&output, NOT_PROVED);
    assert!(stdout(&output).contains("已写入复核报告："));
    let file_text = fs::read_to_string(&destination)
        .unwrap_or_else(|error| panic!("read {}: {error}", destination.display()));
    assert!(
        file_text.starts_with("# 律师复核报告"),
        "the unquoted path must receive the report:\n{file_text}"
    );
}

#[test]
fn a_failed_write_leaves_no_half_report_and_no_temporary_file() {
    let temp = TempDir::new("failed-write");
    let directory = temp.path.join("已有目录");
    fs::create_dir_all(&directory).expect("create destination directory");
    let command = format!(":review 受罚 张三 --out \"{}\"", directory.display());
    let output = session(CLAIM_GAP, &[], &[command.as_str()]);
    assert_exit(&output, COMMAND_ERROR);
    let err = stderr(&output);
    assert!(
        err.contains("写入复核报告") && err.contains("失败"),
        "a failed write must be reported as an error:\n{err}"
    );
    let entries: Vec<String> = fs::read_dir(&temp.path)
        .expect("read temp directory")
        .map(|entry| {
            entry
                .expect("read entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    assert_eq!(
        entries,
        vec!["已有目录".to_owned()],
        "the failed write must not leave a temporary or half file: {entries:?}"
    );
}

#[test]
fn a_missing_destination_directory_is_an_error_without_a_file() {
    let temp = TempDir::new("missing-parent");
    let destination = temp.path.join("不存在").join("报告.md");
    let command = format!(":review 受罚 张三 --out \"{}\"", destination.display());
    let output = session(CLAIM_GAP, &[], &[command.as_str()]);
    assert_exit(&output, COMMAND_ERROR);
    assert!(
        !destination.exists(),
        "a failed write must not create the destination"
    );
    let err = stderr(&output);
    assert!(
        err.contains("写入复核报告") && err.contains("失败"),
        "a missing directory must be reported:\n{err}"
    );
}

#[test]
fn review_out_argument_errors_are_command_errors() {
    for command in [
        ":review --out report.md",
        ":review 受罚 张三 --out",
        ":review 受罚 张三 --out \"未闭合",
        ":review 受罚 张三 --out a --out b",
    ] {
        let output = session(CLAIM_GAP, &[], &[command]);
        assert_exit(&output, COMMAND_ERROR);
        assert!(
            !stderr(&output).is_empty(),
            "a usage error must be reported for {command:?}"
        );
    }
}

#[test]
fn source_notes_cannot_inject_a_markdown_heading() {
    let temp = TempDir::new("injection");
    let theory = temp.write(
        "case.std",
        &format!(
            r#"
sort 人
pred 违法 : 人 → Prop
pred 受罚 : 人 → Prop
obj 张三 : 人
axiom 张三违法 : 违法 张三
  identity verified
  source text "判决" locator "第一页" note "第一行\n## 伪造标题{}反向"
rule 处罚 :
  params p : 人
  premise 违法 p
  conclude 受罚 p
  source text "示例法" locator "第一条" quote "引文\n## 伪造标题"
"#,
            '\u{202E}'
        ),
    );
    let output = run(&[theory, ":review 受罚 张三".to_owned()]);
    assert_exit(&output, PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &["说明：第一行\\n## 伪造标题\\u{202E}反向"],
        "injection report",
    );
    assert_contains(
        report,
        &["引文：「引文\\n## 伪造标题」"],
        "injection report",
    );
    assert!(
        !report.lines().any(|line| line.starts_with("## 伪造标题")),
        "a newline in a source note must not start a Markdown line:\n{report}"
    );
}

#[test]
fn help_documents_review() {
    let output = Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .arg("--help")
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"));
    assert_exit(&output, PROVED);
    let text = stdout(&output);
    assert_contains(
        &text,
        &[
            ":review <命题> [--out <文件>]",
            "不是法律意见",
            "根已证明且无未决义务为 0",
        ],
        "--help",
    );
}

#[test]
fn review_does_not_change_why_or_cert_output() {
    let baseline_why = run(&[format!(":load {CLOSED}"), ":why 受罚 张三".to_owned()]);
    let after_review_why = run(&[
        format!(":load {CLOSED}"),
        ":review 受罚 张三".to_owned(),
        ":why 受罚 张三".to_owned(),
    ]);
    let baseline_why_text = stdout(&baseline_why);
    let why_start = baseline_why_text
        .find("▸ 受罚 张三")
        .unwrap_or_else(|| panic!("no :why output in baseline:\n{baseline_why_text}"));
    let expected_why = &baseline_why_text[why_start..];
    let after_text = stdout(&after_review_why);
    assert!(
        after_text.ends_with(expected_why),
        ":review changed :why output\n--- expected suffix ---\n{expected_why}\n--- actual ---\n{after_text}"
    );

    let baseline_cert = run(&[format!(":load {CLOSED}"), ":cert 受罚 张三".to_owned()]);
    let after_review_cert = run(&[
        format!(":load {CLOSED}"),
        ":review 受罚 张三".to_owned(),
        ":cert 受罚 张三".to_owned(),
    ]);
    let baseline_cert_text = stdout(&baseline_cert);
    let cert_start = baseline_cert_text
        .find("{\n")
        .unwrap_or_else(|| panic!("no certificate JSON in baseline:\n{baseline_cert_text}"));
    let expected_cert = &baseline_cert_text[cert_start..];
    assert!(
        stdout(&after_review_cert).ends_with(expected_cert),
        ":review changed :cert output"
    );
}

#[test]
fn a_gap_node_limit_reports_the_node_limit_not_a_generic_reason() {
    let temp = TempDir::new("node-limit");
    let mut theory = String::from("sort 人\nobj 张三 : 人\npred G : 人 → Prop\n");
    for rule in 0..3 {
        for premise in 0..63 {
            theory.push_str(&format!("pred Q{rule}_{premise} : 人 → Prop\n"));
        }
    }
    // Three rules with 63 premises each hit the 128-node bound before the last
    // premise is expanded.
    for rule in 0..3 {
        theory.push_str(&format!(
            "rule R{rule} :\n  params p : 人\n  premise Q{rule}_0 p\n"
        ));
        for premise in 1..63 {
            theory.push_str(&format!("  premise Q{rule}_{premise} p\n"));
        }
        theory.push_str(&format!(
            "  conclude G p\n  source text \"示例法\" locator \"{rule}\"\n"
        ));
    }
    let path = temp.write("wide.std", &theory);
    let output = run(&[path, ":review G 张三".to_owned()]);
    assert_exit(&output, NOT_PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &[
            "已截断：达到最大节点数（128 个）",
            "未展开（已截断：达到最大节点数（128 个）",
        ],
        "node-limit report",
    );
}

#[test]
fn a_rule_attempt_limit_reports_the_rule_and_its_attempt_bound() {
    let temp = TempDir::new("attempt-limit");
    let mut theory = String::from(
        "sort 人\nobj 张三 : 人\npred G : 人 → Prop\npred H : 人 → Prop\npred X : 人 → Prop\n",
    );
    for index in 0..9 {
        theory.push_str(&format!(
            "rule A{index} :\n  params p : 人\n  premise H p\n  conclude G p\n  source text \"示例法\" locator \"{index}\"\n"
        ));
    }
    theory.push_str(
        "rule R :\n  params p : 人\n  premise X p\n  conclude H p\n  source text \"示例法\" locator \"R\"\n",
    );
    let path = temp.write("attempts.std", &theory);
    let output = run(&[path, ":review G 张三".to_owned()]);
    assert_exit(&output, NOT_PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &["规则 ⟨R⟩ 的尝试次数已达上限（8 次）"],
        "attempt-limit report",
    );
}

#[test]
fn an_inapplicable_candidate_is_not_reported_as_a_node_limit() {
    let temp = TempDir::new("inapplicable");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 违法 : 人 → Prop
pred 其他 : 人 → Prop
pred 受罚 : 人 → Prop
obj 张三 : 人
axiom 张三违法 : 违法 张三
  identity verified
  source text "判决" locator "第一页"
  occurred_at 2030-01-01
rule 旧法 :
  params p : 人
  premise 违法 p
  premise 其他 p
  conclude 受罚 p
  effective 1999-01-01
  repealed 2000-01-01
  source text "示例法" locator "第一条"
"#,
    );
    let output = run(&[theory, ":review 受罚 张三".to_owned()]);
    assert_exit(&output, NOT_PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &[
            "适用性：不适用（",
            "未展开：候选规则「旧法」的适用性为不适用（",
            "补上该前提也不会让它触发",
        ],
        "inapplicable report",
    );
    assert!(
        !report.contains("节点上限"),
        "an inapplicable candidate must not be described as a node-limit truncation:\n{report}"
    );
}

#[test]
fn an_undecidable_candidate_carries_the_reference_time_notice() {
    let temp = TempDir::new("undecidable");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 早 : 人 → Prop
pred 晚 : 人 → Prop
pred 结果 : 人 → Prop
obj 张三 : 人
axiom 早事实 : 早 张三
  identity verified
  source text "判决" locator "第一页"
  occurred_at 2005-01-01
axiom 晚事实 : 晚 张三
  identity verified
  source text "判决" locator "第二页"
  occurred_at 2015-01-01
rule 规则 :
  params p : 人
  premise 早 p
  premise 晚 p
  conclude 结果 p
  effective 2000-01-01
  repealed 2010-01-01
  source text "示例法" locator "第一条"
"#,
    );
    let output = run(&[theory, ":review 结果 张三".to_owned()]);
    assert_exit(&output, NOT_PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &[
            "适用性无法判定",
            "需要为该争点显式指定引用时间（尚未实现）。",
        ],
        "undecidable report",
    );
}

#[test]
fn the_report_header_names_the_model_report_and_denies_legal_advice() {
    let output = session(CLOSED, &[], &[":review 受罚 张三"]);
    assert_exit(&output, PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    let header: String = report.lines().take(4).collect::<Vec<_>>().join("\n");
    assert!(
        header.contains("模型内推导报告"),
        "the first lines must declare the report is model-internal:\n{header}"
    );
    assert!(
        header.contains("不是法律意见"),
        "the first lines must deny legal advice:\n{header}"
    );
}

#[test]
fn issue_scan_truncation_uses_the_explicit_marker() {
    let temp = TempDir::new("issue-limit");
    let mut theory = String::from("sort 人\nobj 张三 : 人\n");
    for index in 0..33 {
        theory.push_str(&format!(
            "pred P{index} : 人 → Prop\npred Q{index} : 人 → Prop\n"
        ));
    }
    for index in 0..33 {
        theory.push_str(&format!(
            "rule R{index} :\n  params p : 人\n  premise Q{index} p\n  conclude P{index} p\n  source text \"示例法\" locator \"{index}\"\n"
        ));
    }
    let path = temp.write("issues.std", &theory);
    let output = run(&[path, ":review P0 张三".to_owned()]);
    assert_exit(&output, NOT_PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    assert_contains(
        report,
        &[
            "当前事实集下可争的结论 32 条",
            "已截断：可争的结论已达到上限（32 条）",
        ],
        "issue-limit report",
    );
}

#[test]
fn a_rule_in_both_a_proof_and_a_gap_has_one_applicability_wording() {
    let temp = TempDir::new("one-applicability");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred A : 人 → Prop
pred B : 人 → Prop
obj 甲 : 人
obj 乙 : 人
axiom 甲成立 : A 甲
  identity verified
  source text "判决" locator "第一页"
rule R :
  params p : 人
  premise A p
  conclude B p
  source text "示例法" locator "第一条"
"#,
    );
    let output = run(&[theory, ":review B 甲".to_owned()]);
    assert_exit(&output, PROVED);
    let out_text = stdout(&output);
    let report = report_part(&out_text);
    let rules = section(report, "三、规则与出处");
    assert_eq!(
        rules.matches("适用性：").count(),
        1,
        "the same rule must not print two differently-worded applicability lines:\n{rules}"
    );
}

#[test]
fn a_read_only_destination_fails_closed_with_an_explicit_message() {
    let temp = TempDir::new("read-only");
    let destination = temp.path.join("只读报告.md");
    fs::write(&destination, "原始内容").expect("write original");
    let original_permissions = fs::metadata(&destination).expect("metadata").permissions();
    let mut permissions = original_permissions.clone();
    permissions.set_readonly(true);
    fs::set_permissions(&destination, permissions).expect("set read-only");
    let command = format!(":review 受罚 张三 --out \"{}\"", destination.display());
    let output = session(CLAIM_GAP, &[], &[command.as_str()]);
    assert_exit(&output, COMMAND_ERROR);
    let err = stderr(&output);
    assert!(
        err.contains("目标不可写（只读）"),
        "a read-only destination must have an explicit error:\n{err}"
    );
    assert_eq!(
        fs::read_to_string(&destination).expect("read original"),
        "原始内容",
        "a failed write must not change the target"
    );
    let metadata = fs::metadata(&destination).expect("metadata after");
    assert!(metadata.permissions().readonly());
    fs::set_permissions(&destination, original_permissions).expect("restore permissions");
}

/// A case whose conclusion rests on a `risk`-marked predicate: the report must
/// carry the high-risk line and the model-internal disclaimer, without merging
/// the risk theme into the `需律师判断` trust label and without changing the exit
/// code.
#[test]
fn the_report_carries_the_disclaimer_and_the_risk_theme() {
    let temp = TempDir::new("risk-disclaimer");
    let theory = temp.write(
        "risk.std",
        "sort 人\n\
         pred 违法 : 人 → Prop\n\
         pred 受罚 : 人 → Prop\n\
         risk 刑事 受罚\n\
         obj 张三 : 人\n\
         axiom 违法事实 : 违法 张三\n\
           source text \"案件材料\" locator \"一\"\n\
         rule 处罚 :\n\
           params p : 人\n\
           premise 违法 p\n\
           conclude 受罚 p\n\
           source text \"刑法\" locator \"一\"\n",
    );
    let output = session(&theory, &[], &[":review 受罚 张三"]);
    assert_exit(&output, PROVED);
    let text = stdout(&output);
    let report = report_part(&text);
    assert_contains(
        report,
        &[
            "高风险题材：涉及刑事；",
            "  依据：",
            "声明：这是模型内推导，不是法律意见。",
        ],
        "the risk report",
    );
    assert!(
        !report.contains("「需律师判断」：成立"),
        "a risk theme must not turn into the 需律师判断 trust label:\n{report}"
    );
    assert_contains(
        report,
        &["「依赖假设」：成立"],
        "the trust labels of a claim-based proof",
    );
}

/// `--redact` is display-only, but the report file is display too: both the
/// stdout and the `--out` form must replace the individual names, while the
/// certificate JSON keeps them for `:verify-cert`.
#[test]
fn redaction_applies_to_the_review_report_and_the_file() {
    let output = session(
        "examples/复核-闭合证明.std",
        &["--redact"],
        &[":review 受罚 张三"],
    );
    assert_exit(&output, PROVED);
    let text = stdout(&output);
    assert!(
        !text.contains("张三"),
        "a redacted report must not print the original name:\n{text}"
    );
    assert_contains(
        &text,
        &["甲1", "输出已脱敏；证书未脱敏。"],
        "the redacted report",
    );

    let temp = TempDir::new("redact-report-file");
    let out_path = temp.path.join("report.md").display().to_string();
    let command = format!(":review 受罚 张三 --out {out_path}");
    let file_output = run(&[
        "--redact".to_owned(),
        "examples/复核-闭合证明.std".to_owned(),
        command,
    ]);
    assert_exit(&file_output, PROVED);
    let file_text = fs::read_to_string(&out_path).expect("read the report file");
    assert!(
        !file_text.contains("张三"),
        "a redacted report file must not contain the original name:\n{file_text}"
    );
    assert_contains(&file_text, &["甲1"], "the redacted report file");
}
