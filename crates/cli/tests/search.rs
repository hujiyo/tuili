//! End-to-end tests for `:search`.
//!
//! Corups searches run against the repository's fixed `law/corpus`, and the
//! filter and escaping cases build their own corpora under temporary roots. The
//! assertions pin the command's documented output shape and exit codes.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const NO_MATCH: i32 = 1;
const ERROR: i32 = 2;

const ARTICLE_39: &str = "中华人民共和国公民的住宅不受侵犯。禁止非法搜查或者非法侵入公民的住宅。";
const ARTICLE_39_HASH: &str =
    "sha256:9aae70936e97a9f380fd0c74e8318c404b0612aaa33b358df83b5ee404a7cf7e";

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn import_example() -> PathBuf {
    repo_root().join("examples/宪法第三十九条-导入包.std")
}

fn run_in(dir: &Path, args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        // Search never loads the lazy default environment; disabling it keeps
        // the assertions independent of the profile's extra packs.
        .arg("--no-default-packs")
        .current_dir(dir)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn run(args: &[String]) -> Output {
    run_in(&repo_root(), args)
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

/// Assert the exit code and that stdout contains every needle.
fn check(output: Output, expected: i32, needles: &[&str]) -> Output {
    assert_exit(&output, expected);
    let out = stdout(&output);
    for needle in needles {
        assert!(
            out.contains(needle),
            "stdout does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{}",
            stderr(&output)
        );
    }
    assert!(
        stderr(&output).is_empty(),
        "stderr should be empty:\n{}",
        stderr(&output)
    );
    output
}

/// Assert the exit code and that stderr contains every needle.
fn check_stderr(output: Output, expected: i32, needles: &[&str]) -> Output {
    assert_exit(&output, expected);
    let err = stderr(&output);
    for needle in needles {
        assert!(
            err.contains(needle),
            "stderr does not contain {needle:?}\nstdout:\n{}\nstderr:\n{err}",
            stdout(&output)
        );
    }
    output
}

#[test]
fn an_unloaded_search_finds_article_39_and_lists_the_declared_rules() {
    let output = check(
        run(&[":search 住宅不受侵犯".to_string()]),
        PROVED,
        &[
            "条文检索：关键词「住宅不受侵犯」",
            "cn.constitution@2018 第三十九条",
            "片段：中华人民共和国公民的住宅不受侵犯。",
            "覆盖：已形式化（来源：语料 coverage 台账）",
            "清单声明（包未加载）：",
            "「cn.constitution.非法搜查侵犯住宅」",
            "「cn.constitution.非法侵入侵犯住宅」",
            "注：包未加载，无法给出条号定位；先 :load 或 import <包名> 再检索。",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("尚未形式化"),
        "a formalized article must not read as unformalized:\n{out}"
    );
    // The pack is not loaded, so no locator may be invented. The `←` form only
    // appears on a real "引用规则（已加载）" line.
    assert!(
        !out.contains('←'),
        "an unloaded pack must not produce a locator/source arrow:\n{out}"
    );
}

#[test]
fn a_loaded_pack_search_lists_rules_with_their_locator_and_trust() {
    let output = check(
        run(&[
            import_example().display().to_string(),
            ":search 住宅不受侵犯".to_string(),
            ":search --article 39".to_string(),
        ]),
        PROVED,
        &[
            "命中 1 条",
            "cn.constitution@2018 第三十九条",
            "信任：official（本项目审核）（cn.constitution@0.4.0）",
            "引用规则（已加载）：",
            "- cn.constitution.非法搜查侵犯住宅 ← 「宪法第三十九条」（2018）",
            "- cn.constitution.非法侵入侵犯住宅 ← 「宪法第三十九条」（2018）",
            "哈希核对：2 条规则声明的 hash 与本地计算一致。",
        ],
    );
    let out = stdout(&output);
    assert!(!out.contains("清单声明"), "{out}");
}

#[test]
fn an_indexed_article_is_reported_but_not_formalized() {
    check(
        run(&[":search 五星红旗".to_string()]),
        PROVED,
        &[
            "cn.constitution@2018 第一百四十一条",
            "覆盖：仅索引（来源：语料 coverage 台账）",
            "尚未形式化",
        ],
    );
}

#[test]
fn a_needs_ontology_article_names_its_gap_and_is_not_formalized() {
    check(
        run(&[":search 一切权力属于人民".to_string()]),
        PROVED,
        &[
            "cn.constitution@2018 第二条",
            "覆盖：待本体（来源：语料 coverage 台账）",
            "本体缺口：state_organs（国家机关、职权、组成、任期与会议程序）",
            "尚未形式化",
        ],
    );
}

#[test]
fn an_unknown_version_is_an_error_and_is_not_replaced() {
    let output = check_stderr(
        run(&[":search 住宅 --version 1999".to_string()]),
        ERROR,
        &["没有该版本的语料", "`1999`", "`2018`"],
    );
    assert!(
        !stdout(&output).contains("cn.constitution@2018"),
        "a missing version must not silently use 2018:\n{}",
        stdout(&output)
    );
}

/// A corpus without a `jurisdiction` field. `:search` tolerates this so the
/// corpus can be excluded by `--jurisdiction` instead of failing the lookup.
fn corpus_without_jurisdiction(law: &str, title: &str) -> String {
    format!(
        r#"{{
  "format": 2,
  "law": "{law}",
  "title": "{title}",
  "version": "2018",
  "articles": [ {{ "number": "第一条", "text": "住宅不受侵犯" }} ]
}}"#
    )
}

fn corpus_with_jurisdiction(law: &str, title: &str) -> String {
    corpus_with_jurisdiction_code(law, title, "CN")
}

fn corpus_with_jurisdiction_code(law: &str, title: &str, code: &str) -> String {
    format!(
        r#"{{
  "format": 2,
  "law": "{law}",
  "title": "{title}",
  "version": "2018",
  "jurisdiction": "{code}",
  "articles": [ {{ "number": "第一条", "text": "住宅不受侵犯" }} ]
}}"#
    )
}

#[test]
fn a_jurisdiction_filter_excludes_an_unrecorded_corpus_with_a_warning() {
    let temp = TempDir::new("jurisdiction-mixed");
    temp.corpus(
        "law/corpus/cn.known/2018.json",
        &corpus_with_jurisdiction("cn.known", "已知法"),
    );
    temp.corpus(
        "law/corpus/cn.unknown/2018.json",
        &corpus_without_jurisdiction("cn.unknown", "未记管辖法"),
    );
    temp.corpus(
        "law/corpus/cn.foreign/2018.json",
        &corpus_with_jurisdiction_code("cn.foreign", "外国管辖法", "US"),
    );
    let output = check(
        run_in(temp.path(), &[":search 住宅 --jurisdiction CN".to_string()]),
        PROVED,
        &[
            "注：cn.unknown@2018 的语料没有记录管辖，已排除；如需检索该语料请去掉 --jurisdiction",
            "管辖过滤：`CN` 保留 1 个语料（因管辖不同排除 1 份，因管辖未记录排除 1 份）",
            "cn.known@2018 第一条",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("cn.unknown@2018 第一条"),
        "the unrecorded corpus must not be searched under --jurisdiction:\n{out}"
    );
    assert!(
        !out.contains("cn.foreign@2018 第一条"),
        "the foreign-jurisdiction corpus must be excluded:\n{out}"
    );
}

#[test]
fn an_all_unrecorded_jurisdiction_search_has_no_results_and_exits_one() {
    let temp = TempDir::new("jurisdiction-all-unrecorded");
    temp.corpus(
        "law/corpus/cn.unknown-a/2018.json",
        &corpus_without_jurisdiction("cn.unknown-a", "未记管辖法甲"),
    );
    temp.corpus(
        "law/corpus/cn.unknown-b/2018.json",
        &corpus_without_jurisdiction("cn.unknown-b", "未记管辖法乙"),
    );
    let output = run_in(temp.path(), &[":search 住宅 --jurisdiction CN".to_string()]);
    assert_exit(&output, NO_MATCH);
    let out = stdout(&output);
    assert!(
        out.contains(
            "注：cn.unknown-a@2018 的语料没有记录管辖，已排除；如需检索该语料请去掉 --jurisdiction"
        ),
        "{out}"
    );
    assert!(
        out.contains(
            "注：cn.unknown-b@2018 的语料没有记录管辖，已排除；如需检索该语料请去掉 --jurisdiction"
        ),
        "{out}"
    );
    assert!(out.contains("没有命中的条文"), "{out}");
    assert!(!out.contains("cn.unknown-a@2018 第一条"), "{out}");
    assert!(!out.contains("cn.unknown-b@2018 第一条"), "{out}");
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn an_unrecorded_jurisdiction_does_not_block_an_unfiltered_search() {
    let temp = TempDir::new("jurisdiction-unfiltered");
    temp.corpus(
        "law/corpus/cn.unknown/2018.json",
        &corpus_without_jurisdiction("cn.unknown", "未记管辖法"),
    );
    check(
        run_in(temp.path(), &[":search 住宅".to_string()]),
        PROVED,
        &[
            "cn.unknown@2018 第一条",
            "覆盖：覆盖率台账不可用（不猜覆盖状态）",
        ],
    );
}

#[test]
fn a_recorded_jurisdiction_matches_the_filter() {
    check(
        run(&[":search 住宅 --jurisdiction CN".to_string()]),
        PROVED,
        &[
            "管辖过滤：`CN` 保留 1 个语料",
            "cn.constitution@2018 第三十九条",
        ],
    );
}

#[test]
fn the_article_filter_prints_the_full_text_and_the_audit_hash() {
    check(
        run(&[":search --article 39".to_string()]),
        PROVED,
        &[
            "条文检索：无关键词（--article 直接列出条文）",
            "条号过滤：`第三十九条`",
            "cn.constitution@2018 第三十九条",
            format!("全文：{ARTICLE_39}").as_str(),
            format!("条文哈希：{ARTICLE_39_HASH}").as_str(),
            "与 :audit 同口径",
        ],
    );
}

#[test]
fn an_ascii_article_number_is_matched_literally_first() {
    let temp = TempDir::new("article-ascii");
    temp.corpus(
        "law/corpus/cn.ascii/2018.json",
        r#"{
  "format": 2,
  "law": "cn.ascii",
  "title": "ASCII 条号法",
  "version": "2018",
  "jurisdiction": "CN",
  "articles": [ { "number": "39", "text": "住宅不受侵犯" } ]
}"#,
    );
    check(
        run_in(temp.path(), &[":search 住宅 --article 39".to_string()]),
        PROVED,
        &["条号过滤：`39`", "cn.ascii@2018 39", "全文：住宅不受侵犯"],
    );
}

#[test]
fn a_chinese_article_number_is_also_accepted() {
    check(
        run(&[":search --article 第三十九条".to_string()]),
        PROVED,
        &["条号过滤：`第三十九条`", "cn.constitution@2018 第三十九条"],
    );
}

#[test]
fn an_article_number_above_9999_is_rejected() {
    check_stderr(
        run(&[":search 住宅 --article 10000".to_string()]),
        ERROR,
        &["只支持 1–9999", "10000"],
    );
}

#[test]
fn the_search_and_audit_agree_on_the_article_hash() {
    // `:audit` accepts the official pack's 56 quoted sources, including the two
    // citing article 39 with hash sha256:9aae…. `:search --article 39` prints
    // the same digest, so both paths use the article-text hash rather than a
    // corpus-file hash.
    let audit = check(
        run(&[import_example().display().to_string(), ":audit".to_string()]),
        PROVED,
        &[
            "条带引文来源：命中 56",
            "✓ 「宪法第三十九条」← cn.constitution@2018",
        ],
    );
    let _ = stdout(&audit);
    check(
        run(&[":search --article 39".to_string()]),
        PROVED,
        &[ARTICLE_39_HASH],
    );
}

#[test]
fn an_oversized_limit_is_a_usage_error() {
    check_stderr(
        run(&[":search 住宅 --limit 1000".to_string()]),
        ERROR,
        &["--limit 1000", "上限 64"],
    );
}

#[test]
fn a_repeated_limit_is_rejected_instead_of_taking_the_last() {
    check_stderr(
        run(&[":search 住宅 --limit 5 --limit 10".to_string()]),
        ERROR,
        &["--limit", "重复"],
    );
}

#[test]
fn a_limit_below_the_hit_count_prints_an_explicit_truncation_marker() {
    let output = check(
        run(&[":search 公民 --limit 5".to_string()]),
        PROVED,
        &[
            "命中 25 条：显示前 5 条",
            "已截断：命中 25 条",
            "cn.constitution@2018 第十三条",
        ],
    );
    let out = stdout(&output);
    assert_eq!(
        out.lines()
            .filter(|line| line.starts_with("cn.constitution@2018 "))
            .count(),
        5,
        "the limit must cap the printed article blocks:\n{out}"
    );
}

#[test]
fn a_control_character_in_the_keyword_is_escaped_on_one_line() {
    let output = run(&[":search 住宅\n不受侵犯".to_string()]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("关键词「住宅\\n不受侵犯」"),
        "a newline in the keyword must be escaped:\n{out:?}"
    );
    assert!(!out.contains('\u{001b}'), "{out:?}");
    // The newline split the keyword into two terms, and both match article 39.
    assert!(out.contains("命中 1 条"), "{out}");

    let output = run(&[":search 住宅\u{001b}[31m不受侵犯".to_string()]);
    assert_exit(&output, NO_MATCH);
    let out = stdout(&output);
    assert!(
        out.contains("关键词「住宅\\u{001B}[31m不受侵犯」"),
        "ESC must be escaped:\n{out:?}"
    );
    assert!(!out.contains('\u{001b}'), "{out:?}");
    assert_eq!(
        out.lines().filter(|line| line.contains("不受侵犯")).count(),
        1,
        "the escaped keyword stays on the keyword line:\n{out:?}"
    );
}

#[test]
fn the_law_filter_accepts_the_id_title_and_alias() {
    for law in ["cn.constitution", "中华人民共和国宪法", "宪法"] {
        let expected = format!("法名过滤：`{law}` 保留 1/1 个语料");
        check(
            run(&[format!(":search 住宅 --law {law}")]),
            PROVED,
            &[expected.as_str(), "cn.constitution@2018 第三十九条"],
        );
    }
}

#[test]
fn unknown_law_and_article_filters_are_errors() {
    check_stderr(
        run(&[":search 住宅 --law 刑法".to_string()]),
        ERROR,
        &["没有该法名的语料", "`刑法`"],
    );
    check_stderr(
        run(&[":search 住宅 --article 999".to_string()]),
        ERROR,
        &["没有该条号的语料", "`第九百九十九条`"],
    );
}

#[test]
fn a_missing_corpus_directory_is_an_environment_error() {
    let temp = TempDir::new("missing-corpus");
    let output = run_in(temp.path(), &[":search 住宅".to_string()]);
    assert_exit(&output, ERROR);
    assert!(
        stderr(&output).contains("无法读取语料目录"),
        "a missing directory is an environment error, not an empty corpus:\n{}",
        stderr(&output)
    );
}

#[test]
fn an_empty_corpus_directory_is_not_a_pass() {
    let temp = TempDir::new("empty-corpus");
    fs::create_dir_all(temp.path().join("law/corpus")).expect("create the empty corpus directory");
    let output = run_in(temp.path(), &[":search 住宅".to_string()]);
    assert_exit(&output, NO_MATCH);
    assert!(
        stdout(&output).contains("语料目录中没有语料"),
        "{}",
        stdout(&output)
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

fn coverage_two_articles(
    first_status: &str,
    first_rules: &str,
    second_status: &str,
    second_rules: &str,
) -> String {
    format!(
        r#"{{ "open_concepts": [], "gaps": {{}}, "articles": [
  {{ "number": "第一条", "status": "{first_status}"{first_rules} }},
  {{ "number": "第二条", "status": "{second_status}"{second_rules} }}
] }}"#
    )
}

fn corpus_two_articles(law: &str, title: &str, first_text: &str, coverage: &str) -> String {
    format!(
        r#"{{
  "format": 2,
  "law": "{law}",
  "title": "{title}",
  "version": "2018",
  "jurisdiction": "CN",
  "coverage": {coverage},
  "articles": [
    {{ "number": "第一条", "text": "{first_text}" }},
    {{ "number": "第二条", "text": "其他条文" }}
  ]
}}"#
    )
}

#[test]
fn a_loaded_rule_that_cites_another_article_is_a_ledger_inconsistency() {
    let temp = TempDir::new("ledger-loaded-elsewhere");
    temp.community_pack(
        "cn.b",
        "2018",
        r#"namespace cn.b
sort cn.b.人
pred cn.b.命题 : cn.b.人 → Prop
rule cn.b.规则一 :
  params x : cn.b.人
  premise cn.b.命题 x
  conclude cn.b.命题 x
  source text "测试法" locator "第二条" version "2018"
"#,
    );
    let coverage =
        coverage_two_articles("formalized", r#", "rules": ["cn.b.规则一"]"#, "indexed", "");
    temp.corpus(
        "law/corpus/cn.b/2018.json",
        &corpus_two_articles("cn.b", "测试法", "住宅不受侵犯", &coverage),
    );
    temp.write("case.std", "import cn.b\n");
    check(
        run_in(temp.path(), &[":lock".to_string()]),
        PROVED,
        &["已写入", "1 个包"],
    );
    let output = check(
        run_in(
            temp.path(),
            &["case.std".to_string(), ":search 住宅".to_string()],
        ),
        PROVED,
        &[
            "台账与已加载规则不一致：清单声明 `cn.b.规则一`，已加载规则 `cn.b.规则一` 的来源是 「测试法第二条」（2018）。",
        ],
    );
    assert!(
        !stdout(&output).contains("包未加载"),
        "the pack is loaded; the output must not claim otherwise"
    );
}

#[test]
fn a_loaded_pack_with_no_loaded_ledger_rule_says_the_rule_is_not_loaded() {
    let temp = TempDir::new("ledger-rule-not-loaded");
    temp.community_pack("cn.c", "2018", "namespace cn.c\nsort cn.c.人\n");
    let coverage = coverage_two_articles(
        "formalized",
        r#", "rules": ["cn.c.未加载规则"]"#,
        "indexed",
        "",
    );
    temp.corpus(
        "law/corpus/cn.c/2018.json",
        &corpus_two_articles("cn.c", "测试法", "住宅不受侵犯", &coverage),
    );
    temp.write("case.std", "import cn.c\n");
    check(
        run_in(temp.path(), &[":lock".to_string()]),
        PROVED,
        &["已写入", "1 个包"],
    );
    let output = run_in(
        temp.path(),
        &["case.std".to_string(), ":search 住宅".to_string()],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("清单声明 `cn.c.未加载规则`，当前环境未加载该规则"),
        "{out}"
    );
    assert!(
        !out.contains("包未加载"),
        "a linked pack exists; the output must not claim it is unloaded:\n{out}"
    );
}

#[test]
fn a_ledger_contradiction_with_loaded_rules_is_reported() {
    let temp = TempDir::new("ledger-contradiction");
    temp.community_pack(
        "cn.d",
        "2018",
        r#"namespace cn.d
sort cn.d.人
pred cn.d.命题 : cn.d.人 → Prop
rule cn.d.规则一 :
  params x : cn.d.人
  premise cn.d.命题 x
  conclude cn.d.命题 x
  source text "测试法" locator "第一条" version "2018"
"#,
    );
    let coverage =
        coverage_two_articles("indexed", "", "formalized", r#", "rules": ["cn.d.规则二"]"#);
    temp.corpus(
        "law/corpus/cn.d/2018.json",
        &corpus_two_articles("cn.d", "测试法", "住宅不受侵犯条文", &coverage),
    );
    temp.write("case.std", "import cn.d\n");
    check(
        run_in(temp.path(), &[":lock".to_string()]),
        PROVED,
        &["已写入", "1 个包"],
    );
    let output = check(
        run_in(
            temp.path(),
            &["case.std".to_string(), ":search 条文".to_string()],
        ),
        PROVED,
        &[
            "台账与已加载规则不一致：台账声明仅索引，但已加载规则引用了该条。",
            "台账与已加载规则不一致：台账声明已形式化，但当前环境没有引用该条的已加载规则。",
        ],
    );
    let _ = stdout(&output);
}

#[test]
fn a_tampered_corpus_hash_is_warned_about_and_makes_the_search_fail() {
    let temp = TempDir::new("hash-tampered");
    temp.community_pack(
        "cn.hash",
        "2018",
        r#"namespace cn.hash
sort cn.hash.人
pred cn.hash.命题 : cn.hash.人 → Prop
rule cn.hash.规则 :
  params x : cn.hash.人
  premise cn.hash.命题 x
  conclude cn.hash.命题 x
  source text "住宅法" locator "第一条" version "2018"
         quote "公民住宅不受侵犯"
         hash "sha256:c8e651cb5ae082ea2f90cfcaf030ec2ef70b10995d37e8261a489af84f99d76b"
"#,
    );
    temp.corpus(
        "law/corpus/cn.hash/2018.json",
        r#"{
  "format": 2,
  "law": "cn.hash",
  "title": "住宅法",
  "version": "2018",
  "jurisdiction": "CN",
  "articles": [ { "number": "第一条", "text": "公民住宅不受侵犯" } ]
}"#,
    );
    temp.write("case.std", "import cn.hash\n");
    check(
        run_in(temp.path(), &[":lock".to_string()]),
        PROVED,
        &["已写入", "1 个包"],
    );
    // The pack and its lock cover the theory file, not the linked corpus; a
    // one-character corpus edit therefore leaves the pack loadable.
    temp.corpus(
        "law/corpus/cn.hash/2018.json",
        r#"{
  "format": 2,
  "law": "cn.hash",
  "title": "住宅法",
  "version": "2018",
  "jurisdiction": "CN",
  "articles": [ { "number": "第一条", "text": "公民住宅不受侵范" } ]
}"#,
    );
    let output = run_in(
        temp.path(),
        &[
            "case.std".to_string(),
            ":search 住宅 --article 1".to_string(),
        ],
    );
    assert_exit(&output, NO_MATCH);
    let out = stdout(&output);
    assert!(
        out.contains("⚠ 语料哈希与规则声明不一致（本地"),
        "the tampered corpus must be reported:\n{out}"
    );
    assert!(
        out.contains(
            "规则 sha256:c8e651cb5ae082ea2f90cfcaf030ec2ef70b10995d37e8261a489af84f99d76b"
        ),
        "{out}"
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn a_versionless_rule_with_several_corpus_versions_is_not_attributed() {
    let temp = TempDir::new("versionless-rule");
    temp.community_pack(
        "cn.multi",
        "2018",
        r#"namespace cn.multi
sort cn.multi.人
pred cn.multi.命题 : cn.multi.人 → Prop
rule cn.multi.规则 :
  params x : cn.multi.人
  premise cn.multi.命题 x
  conclude cn.multi.命题 x
  source text "多版本法" locator "第一条"
"#,
    );
    for version in ["2018", "2020"] {
        temp.corpus(
            &format!("law/corpus/cn.multi/{version}.json"),
            &format!(
                r#"{{
  "format": 2,
  "law": "cn.multi",
  "title": "多版本法",
  "version": "{version}",
  "jurisdiction": "CN",
  "articles": [ {{ "number": "第一条", "text": "住宅不受侵犯" }} ]
}}"#
            ),
        );
    }
    temp.write("case.std", "import cn.multi\n");
    check(
        run_in(temp.path(), &[":lock".to_string()]),
        PROVED,
        &["已写入", "1 个包"],
    );
    let output = run_in(
        temp.path(),
        &["case.std".to_string(), ":search 住宅".to_string()],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("注：规则 `cn.multi.规则` 未记录版本，存在多版本（2018/2020），无法确定引用哪一版，未列为引用规则。"),
        "{out}"
    );
    assert!(
        !out.contains("引用规则（已加载）"),
        "a versionless rule must not be attributed to either version:\n{out}"
    );
}

#[test]
fn a_loaded_community_pack_is_searchable_with_its_trust_level() {
    let temp = TempDir::new("community-pack");
    temp.write(
        "lawpacks/cn.community/lawpack.toml",
        r#"[pack]
name = "cn.community"
version = "0.1.0"
jurisdiction = "CN"
territory = "CN"
namespace = "cn.community"
trust = "community"
corpus = "cn.community/2018"

[[files]]
path = "community.std"
kind = "theory"
"#,
    );
    temp.write(
        "lawpacks/cn.community/community.std",
        r#"namespace cn.community
sort cn.community.人
pred cn.community.住宅安全 : cn.community.人 → Prop
rule cn.community.住宅安全规则 :
  params x : cn.community.人
  premise cn.community.住宅安全 x
  conclude cn.community.住宅安全 x
  source text "社区法" locator "第一条" version "2018"
"#,
    );
    temp.corpus(
        "law/corpus/cn.community/2018.json",
        r#"{
  "format": 2,
  "law": "cn.community",
  "title": "社区法",
  "version": "2018",
  "jurisdiction": "CN",
  "articles": [ { "number": "第一条", "text": "公民住宅不受侵犯" } ]
}"#,
    );
    temp.write("case.std", "import cn.community\n");
    check(
        run_in(temp.path(), &[":lock".to_string()]),
        PROVED,
        &["已写入", "1 个包"],
    );
    check(
        run_in(
            temp.path(),
            &["case.std".to_string(), ":search 住宅不受侵犯".to_string()],
        ),
        PROVED,
        &[
            "cn.community@2018 第一条",
            " 信任：community（未经本项目审核）（cn.community@0.1.0）",
            "覆盖：覆盖率台账不可用（不猜覆盖状态）",
            "引用规则（已加载）：",
            "- cn.community.住宅安全规则 ← 「社区法第一条」（2018）",
        ],
    );
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cli-search-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn corpus(&self, relative: &str, text: &str) -> PathBuf {
        self.write(relative, text)
    }

    /// Write a minimal community pack whose single theory file is `theory`.
    /// The pack name, namespace and law id are all `law`, and its manifest
    /// links `law/corpus_version`.
    fn community_pack(&self, law: &str, corpus_version: &str, theory: &str) {
        self.write(
            &format!("lawpacks/{law}/lawpack.toml"),
            &format!(
                r#"[pack]
name = "{law}"
version = "0.1.0"
jurisdiction = "CN"
territory = "CN"
namespace = "{law}"
trust = "community"
corpus = "{law}/{corpus_version}"

[[files]]
path = "community.std"
kind = "theory"
"#
            ),
        );
        self.write(&format!("lawpacks/{law}/community.std"), theory);
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.path.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
        }
        fs::write(&path, text).unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
