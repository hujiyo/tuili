//! End-to-end tests for the official `cn.constitution` law pack.
//!
//! These tests exercise the repository's fixed `lawpacks/` registry, so every
//! CLI run starts from the repository root. The corruption test copies the
//! registry into its own temporary directory; it never edits the repository.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const LOAD_FAILED: i32 = 1;
const ERROR: i32 = 2;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The facts-only example that imports the official pack.
fn import_example() -> PathBuf {
    repo_root().join("examples/宪法第三十九条-导入包.std")
}

fn run_in(current_dir: &Path, args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(current_dir)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn run_in_repo(args: &[String]) -> Output {
    run_in(&repo_root(), args)
}

fn run_repl_in(current_dir: &Path, input: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(current_dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"));
    child
        .stdin
        .take()
        .expect("stdin is piped")
        .write_all(input.as_bytes())
        .expect("write REPL input");
    child
        .wait_with_output()
        .unwrap_or_else(|error| panic!("failed to wait for the CLI: {error}"))
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// Assert the exit code and that stdout contains every needle.
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

fn check_stderr(output: Output, expected: i32, needles: &[&str]) -> Output {
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
            err.contains(needle),
            "stderr does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

#[test]
fn the_official_pack_is_listed_and_its_lock_verifies() {
    let output = check(
        run_in_repo(&[":packs lawpacks".to_string()]),
        PROVED,
        &[
            "cn.constitution 0.3.0",
            "中华人民共和国宪法官方包 v0.3.0（第三十三至四十六条中的选定基本权利；非完整形式化）",
            "文件 1 个",
            "锁定校验：通过（1 个包）",
        ],
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn inspect_marks_pack_declarations_with_the_pack_version() {
    let output = check(
        run_in_repo(&[
            import_example().display().to_string(),
            ":inspect".to_string(),
        ]),
        PROVED,
        &[
            "rule  cn.constitution.非法搜查侵犯住宅",
            "pred  cn.constitution.公民 : cn.constitution.人 → Prop",
            "[cn.constitution@0.3.0]",
            "引文：中华人民共和国公民的住宅不受侵犯。禁止非法搜查或者非法侵入公民的住宅。",
        ],
    );
    let out = stdout(&output);
    // The pack contributes 2 sorts + 53 predicates + 41 rules = 96 declarations,
    // all marked with the locked version; the case objects are not.
    assert_eq!(out.matches("[cn.constitution@0.3.0]").count(), 96, "{out}");
}

/// A user file may not declare into the official pack's namespace. The ledger
/// is flat, so such declarations would merge with the pack's and could be
/// displayed as if the pack had contributed them.
#[test]
fn a_file_cannot_declare_into_a_loaded_pack_namespace() {
    let temp = TempDir::new("pack-namespace-injection");
    let fake = temp.path().join("fake.std");
    fs::write(
        &fake,
        "namespace cn.constitution\nsort cn.constitution.伪造\n",
    )
    .expect("write the fake file");

    let input = format!(
        ":load {}\n:load {}\n:inspect\n:quit\n",
        import_example().display(),
        fake.display()
    );
    let output = run_repl_in(&repo_root(), &input);
    let code = output.status.code();
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(code, Some(ERROR), "stdout:\n{out}\nstderr:\n{err}");
    assert!(
        out.contains("不能向已加载包 `cn.constitution` 添加声明；请使用独立 namespace"),
        "the rejected file must name the pack namespace:\n{out}"
    );
    assert!(
        !out.contains("伪造"),
        "a rejected declaration must not enter the ledger:\n{out}"
    );
    assert_eq!(
        out.matches("[cn.constitution@0.3.0]").count(),
        96,
        "the pack's 96 declarations still carry the pack suffix:\n{out}"
    );
}

#[test]
fn audit_matches_the_quotations_inside_the_official_pack() {
    let output = check(
        run_in_repo(&[import_example().display().to_string(), ":audit".to_string()]),
        PROVED,
        &[
            "✓ 「宪法第三十三条」← cn.constitution@2018",
            "✓ 「宪法第三十四条」← cn.constitution@2018",
            "✓ 「宪法第三十五条」← cn.constitution@2018",
            "✓ 「宪法第三十六条」← cn.constitution@2018",
            "✓ 「宪法第三十七条」← cn.constitution@2018",
            "✓ 「宪法第三十八条」← cn.constitution@2018",
            "✓ 「宪法第三十九条」← cn.constitution@2018",
            "✓ 「宪法第四十条」← cn.constitution@2018",
            "✓ 「宪法第四十一条」← cn.constitution@2018",
            "✓ 「宪法第四十二条」← cn.constitution@2018",
            "✓ 「宪法第四十三条」← cn.constitution@2018",
            "✓ 「宪法第四十四条」← cn.constitution@2018",
            "✓ 「宪法第四十五条」← cn.constitution@2018",
            "✓ 「宪法第四十六条」← cn.constitution@2018",
            "核对 41 条带引文来源：命中 41，不一致 0，未核对 0；另有 2 条来源无引文（不参与核对）。",
            "条文哈希：41 条已固定并核验，0 条未固定，0 条未核验或格式非法。",
            "覆盖 cn.constitution@2018：形式化 14 条 / 索引 129 条 / 开放概念 29 个",
            "  形式化：「第三十三条」、「第三十四条」、「第三十五条」、「第三十六条」、「第三十七条」、「第三十八条」、「第三十九条」、「第四十条」、「第四十一条」、「第四十二条」、「第四十三条」、「第四十四条」、「第四十五条」、「第四十六条」",
        ],
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

/// A case file only states nationality and the two unlawful acts; the pack's
/// selected sentences must carry the reasoning for all five articles.
#[test]
fn a_facts_only_case_proves_the_selected_sentences_of_five_articles() {
    let temp = TempDir::new("five-articles");
    let case = temp.path().join("case.std");
    fs::write(
        &case,
        r#"import cn.constitution

obj 张三 : cn.constitution.人
obj 甲宅 : cn.constitution.住宅

axiom 张三有中国国籍 : cn.constitution.中国国籍 张三
  source text "测试案情" locator "国籍"

axiom 张三被非法拘禁 : cn.constitution.非法拘禁 张三
  source text "测试案情" locator "拘禁"

axiom 张三住宅遭非法搜查 : cn.constitution.非法搜查 张三 甲宅
  source text "测试案情" locator "搜查"
"#,
    )
    .expect("write the case file");

    let output = check(
        run_in(
            &repo_root(),
            &[
                case.display().to_string(),
                ":why cn.constitution.公民 张三".to_string(),
                ":why cn.constitution.法律面前平等 张三".to_string(),
                ":why cn.constitution.言论自由 张三".to_string(),
                ":why cn.constitution.人身自由受侵犯 张三".to_string(),
                ":why cn.constitution.住宅受侵犯 张三 甲宅".to_string(),
                ":why cn.constitution.受教育权 张三".to_string(),
                ":why cn.constitution.受教育义务 张三".to_string(),
            ],
        ),
        PROVED,
        &[
            "▸ cn.constitution.公民 张三  ⟨cn.constitution.中国国籍即公民⟩",
            "▸ cn.constitution.法律面前平等 张三  ⟨cn.constitution.公民法律面前平等⟩",
            "▸ cn.constitution.言论自由 张三  ⟨cn.constitution.公民有言论自由⟩",
            "▸ cn.constitution.人身自由受侵犯 张三  ⟨cn.constitution.非法拘禁侵犯人身自由⟩",
            "▸ cn.constitution.住宅受侵犯 张三 甲宅  ⟨cn.constitution.非法搜查侵犯住宅⟩",
            "▸ cn.constitution.受教育权 张三  ⟨cn.constitution.公民有受教育权⟩",
            "▸ cn.constitution.受教育义务 张三  ⟨cn.constitution.公民有受教育义务⟩",
        ],
    );
    let out = stdout(&output);
    assert_eq!(
        out.matches("推导已通过独立校验。").count(),
        7,
        "all seven queries must pass both certificate checks:\n{out}"
    );
}

/// The second-chapter batch adds rights whose conditions are explicit facts:
/// age, religious coercion, defamation, communication checks, state-inflicted
/// loss, employment, retirement and old age. Each article must reach its
/// conclusion through its own pack rule and pass both certificate checks.
#[test]
fn a_facts_only_case_proves_the_first_batch_of_chapter_two_rights() {
    let temp = TempDir::new("chapter-two-rights");
    let case = temp.path().join("case.std");
    fs::write(
        &case,
        r#"import cn.constitution

obj 张三 : cn.constitution.人

axiom 张三有中国国籍 : cn.constitution.中国国籍 张三
  source text "测试案情" locator "国籍"

axiom 张三年满十八周岁 : cn.constitution.年满十八周岁 张三
  source text "测试案情" locator "年龄"

axiom 张三被强制不信仰宗教 : cn.constitution.被强制不信仰宗教 张三
  source text "测试案情" locator "信仰"

axiom 张三受侮辱 : cn.constitution.侮辱 张三
  source text "测试案情" locator "侮辱"

axiom 张三被非法检查通信 : cn.constitution.非法检查通信 张三
  source text "测试案情" locator "通信"

axiom 张三因国家机关侵权受损失 : cn.constitution.因国家机关侵权受损失 张三
  source text "测试案情" locator "损失"

axiom 张三是劳动者 : cn.constitution.劳动者 张三
  source text "测试案情" locator "劳动者"

axiom 张三是退休人员 : cn.constitution.退休人员 张三
  source text "测试案情" locator "退休"

axiom 张三年老 : cn.constitution.年老 张三
  source text "测试案情" locator "年老"
"#,
    )
    .expect("write the case file");

    let output = check(
        run_in(
            &repo_root(),
            &[
                case.display().to_string(),
                ":why cn.constitution.选举权 张三".to_string(),
                ":why cn.constitution.被选举权 张三".to_string(),
                ":why cn.constitution.宗教信仰自由 张三".to_string(),
                ":why cn.constitution.宗教信仰自由受侵犯 张三".to_string(),
                ":why cn.constitution.人格尊严受侵犯 张三".to_string(),
                ":why cn.constitution.通信自由和通信秘密受侵犯 张三".to_string(),
                ":why cn.constitution.批评建议权 张三".to_string(),
                ":why cn.constitution.申诉权 张三".to_string(),
                ":why cn.constitution.控告权 张三".to_string(),
                ":why cn.constitution.检举权 张三".to_string(),
                ":why cn.constitution.取得赔偿权 张三".to_string(),
                ":why cn.constitution.劳动权 张三".to_string(),
                ":why cn.constitution.劳动义务 张三".to_string(),
                ":why cn.constitution.休息权 张三".to_string(),
                ":why cn.constitution.退休生活受保障 张三".to_string(),
                ":why cn.constitution.物质帮助权 张三".to_string(),
            ],
        ),
        PROVED,
        &[
            "▸ cn.constitution.选举权 张三  ⟨cn.constitution.公民有选举权⟩",
            "▸ cn.constitution.被选举权 张三  ⟨cn.constitution.公民有被选举权⟩",
            "▸ cn.constitution.宗教信仰自由 张三  ⟨cn.constitution.公民有宗教信仰自由⟩",
            "▸ cn.constitution.宗教信仰自由受侵犯 张三  ⟨cn.constitution.被强制不信仰宗教侵犯宗教信仰自由⟩",
            "▸ cn.constitution.人格尊严受侵犯 张三  ⟨cn.constitution.侮辱侵犯人格尊严⟩",
            "▸ cn.constitution.通信自由和通信秘密受侵犯 张三  ⟨cn.constitution.非法检查通信侵犯通信自由和通信秘密⟩",
            "▸ cn.constitution.批评建议权 张三  ⟨cn.constitution.公民有批评建议权⟩",
            "▸ cn.constitution.申诉权 张三  ⟨cn.constitution.公民有申诉权⟩",
            "▸ cn.constitution.控告权 张三  ⟨cn.constitution.公民有控告权⟩",
            "▸ cn.constitution.检举权 张三  ⟨cn.constitution.公民有检举权⟩",
            "▸ cn.constitution.取得赔偿权 张三  ⟨cn.constitution.因国家机关侵权受损失取得赔偿权⟩",
            "▸ cn.constitution.劳动权 张三  ⟨cn.constitution.公民有劳动权⟩",
            "▸ cn.constitution.劳动义务 张三  ⟨cn.constitution.公民有劳动义务⟩",
            "▸ cn.constitution.休息权 张三  ⟨cn.constitution.劳动者有休息权⟩",
            "▸ cn.constitution.退休生活受保障 张三  ⟨cn.constitution.退休人员生活受保障⟩",
            "▸ cn.constitution.物质帮助权 张三  ⟨cn.constitution.年老公民有物质帮助权⟩",
        ],
    );
    let out = stdout(&output);
    assert_eq!(
        out.matches("推导已通过独立校验。").count(),
        16,
        "all sixteen queries must pass both certificate checks:\n{out}"
    );
}

/// Article 34's `unless` clause blocks the electoral right only when the legal
/// deprivation is actually proved; the blocked query stays a gap, never a
/// negation.
#[test]
fn article_34_electoral_right_is_blocked_by_a_legal_deprivation() {
    let temp = TempDir::new("chapter-two-deprivation");
    let case = temp.path().join("case.std");
    fs::write(
        &case,
        r#"import cn.constitution

obj 李四 : cn.constitution.人

axiom 李四有中国国籍 : cn.constitution.中国国籍 李四
  source text "测试案情" locator "国籍"

axiom 李四年满十八周岁 : cn.constitution.年满十八周岁 李四
  source text "测试案情" locator "年龄"

axiom 李四依法被剥夺政治权利 : cn.constitution.依法被剥夺政治权利 李四
  source text "测试案情" locator "剥夺政治权利"
"#,
    )
    .expect("write the case file");

    let output = check(
        run_in(
            &repo_root(),
            &[
                case.display().to_string(),
                ":why cn.constitution.选举权 李四".to_string(),
            ],
        ),
        LOAD_FAILED,
        &[
            "? cn.constitution.选举权 李四  【未闭合】",
            "候选 ⟨cn.constitution.公民有选举权⟩ ← 「宪法第三十四条」（2018）",
            "被阻断：「cn.constitution.依法被剥夺政治权利 李四」已成立",
            "证书有效，但根为缺口，结论未被证明。",
        ],
    );
    assert!(
        !stdout(&output).contains("推导已通过独立校验。"),
        "a blocked right must not be reported as proved:\n{}",
        stdout(&output)
    );
}

/// A changed pack file must be caught by both the registry lock check and the
/// import path. The copy keeps the repository untouched.
#[test]
fn a_corrupted_pack_file_fails_packs_and_load() {
    let temp = TempDir::new("official-pack-corrupt");
    copy_official_pack(temp.path());
    let theory = temp
        .path()
        .join("lawpacks/cn.constitution/constitution.std");
    let mut text = fs::read_to_string(&theory).expect("read the copied pack file");
    text.push_str("\n-- 改动：破坏锁哈希\n");
    fs::write(&theory, text).expect("write the corrupted pack file");

    let output = check(
        run_in(temp.path(), &[":packs lawpacks".to_string()]),
        ERROR,
        &["哈希不符"],
    );
    assert!(
        stderr(&output).contains("错误：1 个锁定校验错误"),
        "{}",
        stderr(&output)
    );

    let output = check_stderr(
        run_in(
            temp.path(),
            &[
                import_example().display().to_string(),
                ":why cn.constitution.住宅受侵犯 张三 甲宅".to_string(),
            ],
        ),
        LOAD_FAILED,
        &["哈希不符"],
    );
    assert!(
        !stdout(&output).contains("已加载"),
        "a failed import must not report a loaded theory:\n{}",
        stdout(&output)
    );
}

/// Copy the two files and the lock that make up the official pack.
fn copy_official_pack(root: &Path) {
    let source = repo_root().join("lawpacks");
    let target = root.join("lawpacks");
    copy_file(&source.join("std.lock"), &target.join("std.lock"));
    copy_file(
        &source.join("cn.constitution/lawpack.toml"),
        &target.join("cn.constitution/lawpack.toml"),
    );
    copy_file(
        &source.join("cn.constitution/constitution.std"),
        &target.join("cn.constitution/constitution.std"),
    );
}

fn copy_file(from: &Path, to: &Path) {
    if let Some(parent) = to.parent() {
        fs::create_dir_all(parent)
            .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
    }
    fs::copy(from, to)
        .unwrap_or_else(|error| panic!("copy {} to {}: {error}", from.display(), to.display()));
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cli-official-pack-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
