//! Tests for corpus parsing, discovery and citation auditing.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_lawpack::corpus::{self, Audit, Citation, Corpus};

const TEXT_39: &str = "中华人民共和国公民的住宅不受侵犯。\n禁止非法搜查或者非法侵入公民的住宅。";
const TEXT_39_JSON: &str =
    r"中华人民共和国公民的住宅不受侵犯。\n禁止非法搜查或者非法侵入公民的住宅。";
const QUOTE_39: &str = "中华人民共和国公民的住宅不受侵犯。禁止非法搜查或者非法侵入公民的住宅。";
const TEXT_39_SHA256: &str =
    "sha256:b0102d49a2563dde914e6247384e97403529aeb110f467434e620d1d08735fdb";
const ABC_SHA256: &str = "sha256:ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";

/// The 64-digit hash used by the general fixture; only its shape matters.
const FIXTURE_SHA256: &str =
    "sha256:ee6e873b9595a23b87d25fde0dfa9324dd9c338e71bfdd952dd08e06ae798749";

fn corpus_json(law: &str, title: &str, aliases: &str, version: &str, articles: &str) -> String {
    format!(
        r#"{{
  "format": 1,
  "law": "{law}",
  "title": "{title}",
  "aliases": {aliases},
  "version": "{version}",
  "jurisdiction": "CN",
  "effective_from": "1982-12-04",
  "source_url": "https://example.test/law",
  "retrieved_at": "2026-11-22",
  "text_sha256": "{FIXTURE_SHA256}",
  "articles": [ {articles} ]
}}"#
    )
}

fn article(number: &str, text_json: &str) -> String {
    format!(r#"{{ "number": "{number}", "text": "{text_json}" }}"#)
}

fn constitution_json() -> String {
    corpus_json(
        "cn.constitution",
        "中华人民共和国宪法",
        r#"["宪法"]"#,
        "2018",
        &article("第三十九条", TEXT_39_JSON),
    )
}

fn constitution() -> Corpus {
    Corpus::parse(&constitution_json()).expect("the fixture corpus is valid")
}

fn ascii_corpus() -> Corpus {
    Corpus::parse(&corpus_json(
        "cn.test",
        "测试法",
        "[]",
        "1",
        &article("第一条", "abc"),
    ))
    .expect("the ASCII fixture corpus is valid")
}

fn citation<'a>(text: &'a str, locator: &'a str, quote: &'a str) -> Citation<'a> {
    Citation {
        text,
        locator,
        version: "",
        quote,
        hash: "",
        jurisdiction: "",
    }
}

fn parse_error(text: &str) -> String {
    match Corpus::parse(text) {
        Ok(_) => panic!("corpus should be rejected:\n{text}"),
        Err(error) => error.message().to_owned(),
    }
}

#[test]
fn valid_corpus_parses_all_fields() {
    let corpus = constitution();
    assert_eq!(corpus.format, 1);
    assert_eq!(corpus.law, "cn.constitution");
    assert_eq!(corpus.title, "中华人民共和国宪法");
    assert_eq!(corpus.aliases, ["宪法"]);
    assert_eq!(corpus.version, "2018");
    assert_eq!(corpus.jurisdiction, "CN");
    assert_eq!(corpus.effective_from.as_deref(), Some("1982-12-04"));
    assert_eq!(
        corpus.source_url.as_deref(),
        Some("https://example.test/law")
    );
    assert_eq!(corpus.retrieved_at.as_deref(), Some("2026-11-22"));
    assert_eq!(corpus.text_sha256.as_deref(), Some(FIXTURE_SHA256));
    assert_eq!(corpus.notes, None);
    assert_eq!(corpus.articles.len(), 1);
    assert_eq!(corpus.articles[0].number, "第三十九条");
    assert_eq!(corpus.articles[0].text, TEXT_39);
}

#[test]
fn unknown_fields_are_rejected() {
    let text = constitution_json().replace("\"format\": 1,", "\"format\": 1,\n  \"bogus\": 1,");
    let error = parse_error(&text);
    assert!(error.contains("bogus"), "{error}");

    let text = constitution_json().replace(
        &article("第三十九条", TEXT_39_JSON),
        &article("第三十九条", "x").replace("\"text\": \"x\"", "\"text\": \"x\", \"extra\": 1"),
    );
    let error = parse_error(&text);
    assert!(error.contains("extra"), "{error}");
}

#[test]
fn unsupported_format_is_rejected() {
    let text = constitution_json().replace("\"format\": 1", "\"format\": 2");
    let error = parse_error(&text);
    assert!(error.contains("格式版本") && error.contains('2'), "{error}");
}

#[test]
fn invalid_law_ids_are_rejected() {
    for law in ["CN.Constitution", "cn constitution", "cn/constitution", ""] {
        let text = constitution_json().replace("cn.constitution", law);
        let error = parse_error(&text);
        assert!(error.contains("law"), "`{law}`: {error}");
    }
}

#[test]
fn empty_required_fields_are_rejected() {
    for (field, value) in [
        ("title", "中华人民共和国宪法"),
        ("version", "2018"),
        ("jurisdiction", "CN"),
    ] {
        let text = constitution_json().replace(value, "");
        let error = parse_error(&text);
        assert!(error.contains(field), "{field}: {error}");
    }
}

#[test]
fn invalid_dates_are_rejected() {
    for (field, from, to) in [
        ("effective_from", "1982-12-04", "1982-02-30"),
        ("effective_from", "1982-12-04", "1982-2-4"),
        ("retrieved_at", "2026-11-22", "2026-11-31"),
    ] {
        let text = constitution_json().replace(from, to);
        let error = parse_error(&text);
        assert!(error.contains(field), "{field}={to}: {error}");
    }
}

#[test]
fn invalid_text_sha256_is_rejected() {
    for value in [
        "sha256:",
        "sha256:abc",
        "sha256:EE6E873B9595A23B87D25FDE0DFA9324DD9C338E71BFDD952DD08E06AE798749",
        "ee6e873b9595a23b87d25fde0dfa9324dd9c338e71bfdd952dd08e06ae798749",
        "md5:ee6e873b9595a23b87d25fde0dfa9324dd9c338e71bfdd952dd08e06ae798749",
    ] {
        let text = constitution_json().replace(FIXTURE_SHA256, value);
        let error = parse_error(&text);
        assert!(error.contains("text_sha256"), "`{value}`: {error}");
    }
}

#[test]
fn empty_articles_are_rejected() {
    let text = corpus_json("cn.test", "测试法", "[]", "1", "");
    let error = parse_error(&text);
    assert!(error.contains("articles"), "{error}");
}

#[test]
fn duplicate_article_numbers_are_rejected() {
    let text = corpus_json(
        "cn.test",
        "测试法",
        "[]",
        "1",
        &format!("{}, {}", article("第一条", "a"), article("第一条", "b")),
    );
    let error = parse_error(&text);
    assert!(
        error.contains("第一条") && error.contains("重复"),
        "{error}"
    );

    let text = corpus_json(
        "cn.test",
        "测试法",
        "[]",
        "1",
        &format!("{}, {}", article("第一条", "a"), article(" 第一条 ", "b")),
    );
    let error = parse_error(&text);
    assert!(error.contains("重复"), "{error}");
}

#[test]
fn blank_article_fields_are_rejected() {
    for article_text in [article("", "a"), article("   ", "a"), article("第一条", "")] {
        let text = corpus_json("cn.test", "测试法", "[]", "1", &article_text);
        let error = parse_error(&text);
        assert!(error.contains("articles[0]."), "{error}");
    }
}

#[test]
fn optional_fields_may_be_absent() {
    let text = r#"{
      "format": 1,
      "law": "cn.test",
      "title": "测试法",
      "version": "1",
      "jurisdiction": "CN",
      "articles": [ { "number": "第一条", "text": "abc" } ]
    }"#;
    let corpus = Corpus::parse(text).expect("optional fields may be omitted");
    assert!(corpus.aliases.is_empty());
    assert_eq!(corpus.effective_from, None);
    assert_eq!(corpus.source_url, None);
    assert_eq!(corpus.retrieved_at, None);
    assert_eq!(corpus.text_sha256, None);
    assert_eq!(corpus.notes, None);
}

#[test]
fn exact_quote_hits() {
    let result = corpus::audit(&[constitution()], &citation("宪法", "第三十九条", QUOTE_39));
    assert_eq!(result.audit, Audit::Hit);
    assert_eq!(
        result.corpus.as_ref().map(ToString::to_string),
        Some("cn.constitution@2018".to_owned())
    );
    assert!(result.detail.is_empty());
    assert!(result.audit.is_hit());
    assert!(!result.audit.is_unverified());
}

#[test]
fn whitespace_and_newline_differences_still_hit() {
    let quote = " 中华人民共和国公民的住宅不受侵犯。 \n\t 禁止非法搜查或者非法侵入公民的住宅。 ";
    let result = corpus::audit(&[constitution()], &citation("宪法", "第三十九条", quote));
    assert_eq!(result.audit, Audit::Hit);
}

#[test]
fn one_changed_character_is_a_mismatch() {
    let quote = QUOTE_39.replace("住宅不受侵犯", "住宅不受侵范");
    let result = corpus::audit(&[constitution()], &citation("宪法", "第三十九条", &quote));
    assert_eq!(result.audit, Audit::Mismatch);
    assert!(result.detail.contains("不一致"), "{}", result.detail);
    assert_eq!(
        result.corpus.as_ref().map(ToString::to_string),
        Some("cn.constitution@2018".to_owned())
    );
}

#[test]
fn changed_punctuation_is_a_mismatch() {
    let quote = QUOTE_39.replace('。', "，");
    let result = corpus::audit(&[constitution()], &citation("宪法", "第三十九条", &quote));
    assert_eq!(result.audit, Audit::Mismatch);
}

#[test]
fn changed_case_and_digits_are_a_mismatch() {
    let corpus = ascii_corpus();
    for quote in ["abc ABC 124", "abc abc 123", "ABC ABC 123"] {
        let result = corpus::audit(
            std::slice::from_ref(&corpus),
            &citation("测试法", "第一条", quote),
        );
        assert_eq!(result.audit, Audit::Mismatch, "`{quote}`");
    }
}

#[test]
fn missing_quote_is_unverified() {
    for quote in ["", "  \n\t "] {
        let checked = corpus::audit(&[constitution()], &citation("宪法", "第三十九条", quote));
        assert_eq!(checked.audit, Audit::NoQuote);
        assert!(checked.audit.is_unverified());
        assert!(!checked.audit.is_hit());
        assert!(checked.corpus.is_none());
    }
}

#[test]
fn missing_corpus_is_unverified() {
    let checked = corpus::audit(&[constitution()], &citation("刑法", "第二十条", QUOTE_39));
    assert_eq!(checked.audit, Audit::NoCorpus);
    assert!(checked.audit.is_unverified());
    assert!(checked.detail.contains("未找到语料"), "{}", checked.detail);
}

#[test]
fn empty_name_or_locator_is_invalid() {
    for (text, locator) in [
        ("", "第三十九条"),
        ("  ", "第三十九条"),
        ("宪法", ""),
        ("宪法", "  "),
    ] {
        let checked = corpus::audit(&[constitution()], &citation(text, locator, QUOTE_39));
        assert_eq!(checked.audit, Audit::InvalidSource, "`{text}`/`{locator}`");
    }
}

#[test]
fn missing_article_is_a_failure() {
    let checked = corpus::audit(&[constitution()], &citation("宪法", "第四十条", QUOTE_39));
    assert_eq!(checked.audit, Audit::NoArticle);
    assert!(checked.detail.contains("条号"), "{}", checked.detail);
    assert_eq!(
        checked.corpus.as_ref().map(ToString::to_string),
        Some("cn.constitution@2018".to_owned())
    );
}

#[test]
fn version_mismatch_is_a_failure() {
    let checked = corpus::audit(
        &[constitution()],
        &Citation {
            version: "2019",
            ..citation("宪法", "第三十九条", QUOTE_39)
        },
    );
    assert_eq!(checked.audit, Audit::VersionMismatch);
    assert!(checked.detail.contains("版本不符"), "{}", checked.detail);
    assert!(
        checked.detail.contains("cn.constitution@2018"),
        "{}",
        checked.detail
    );
}

#[test]
fn multiple_versions_without_a_source_version_are_ambiguous() {
    let other = Corpus::parse(&corpus_json(
        "cn.constitution",
        "中华人民共和国宪法",
        r#"["宪法"]"#,
        "2017",
        &article("第三十九条", TEXT_39_JSON),
    ))
    .expect("the second version is valid");
    let checked = corpus::audit(
        &[constitution(), other],
        &citation("宪法", "第三十九条", QUOTE_39),
    );
    assert_eq!(checked.audit, Audit::Ambiguous);
    assert!(checked.corpus.is_none());
    assert!(checked.detail.contains("候选"), "{}", checked.detail);
}

#[test]
fn source_version_selects_one_of_multiple_versions() {
    let other = Corpus::parse(&corpus_json(
        "cn.constitution",
        "中华人民共和国宪法",
        r#"["宪法"]"#,
        "2017",
        &article("第三十九条", TEXT_39_JSON),
    ))
    .expect("the second version is valid");
    let checked = corpus::audit(
        &[constitution(), other],
        &Citation {
            version: "2018",
            ..citation("宪法", "第三十九条", QUOTE_39)
        },
    );
    assert_eq!(checked.audit, Audit::Hit);
    assert_eq!(
        checked.corpus.as_ref().map(ToString::to_string),
        Some("cn.constitution@2018".to_owned())
    );
}

#[test]
fn same_version_but_different_laws_is_ambiguous() {
    let other = Corpus::parse(&corpus_json(
        "cn.other-constitution",
        "中华人民共和国宪法",
        r#"["宪法"]"#,
        "2018",
        &article("第三十九条", TEXT_39_JSON),
    ))
    .expect("the other law is valid");
    let checked = corpus::audit(
        &[constitution(), other],
        &Citation {
            version: "2018",
            ..citation("宪法", "第三十九条", QUOTE_39)
        },
    );
    assert_eq!(checked.audit, Audit::Ambiguous);
}

#[test]
fn hash_match_is_a_hit() {
    let checked = corpus::audit(
        &[ascii_corpus()],
        &Citation {
            hash: ABC_SHA256,
            ..citation("测试法", "第一条", "abc")
        },
    );
    assert_eq!(checked.audit, Audit::Hit);
}

#[test]
fn hash_is_computed_over_the_article_text_with_newlines() {
    let checked = corpus::audit(
        &[constitution()],
        &Citation {
            hash: TEXT_39_SHA256,
            ..citation("宪法", "第三十九条", QUOTE_39)
        },
    );
    assert_eq!(checked.audit, Audit::Hit);
}

#[test]
fn wrong_hash_is_a_hash_mismatch() {
    let wrong = "sha256:ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ae";
    let checked = corpus::audit(
        &[ascii_corpus()],
        &Citation {
            hash: wrong,
            ..citation("测试法", "第一条", "abc")
        },
    );
    assert_eq!(checked.audit, Audit::HashMismatch);
    assert!(checked.detail.contains("哈希不符"), "{}", checked.detail);
}

#[test]
fn malformed_hash_is_a_hash_mismatch() {
    for value in [
        "sha256:abc",
        "md5:ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        "sha256:BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD",
    ] {
        let checked = corpus::audit(
            &[ascii_corpus()],
            &Citation {
                hash: value,
                ..citation("测试法", "第一条", "abc")
            },
        );
        assert_eq!(checked.audit, Audit::HashMismatch, "`{value}`");
        assert!(
            checked.detail.contains("格式"),
            "`{value}`: {}",
            checked.detail
        );
    }
}

#[test]
fn jurisdiction_mismatch_is_a_failure() {
    let checked = corpus::audit(
        &[constitution()],
        &Citation {
            jurisdiction: "US",
            ..citation("宪法", "第三十九条", QUOTE_39)
        },
    );
    assert_eq!(checked.audit, Audit::JurisdictionMismatch);
    assert!(checked.detail.contains("US"), "{}", checked.detail);
    assert!(checked.detail.contains("CN"), "{}", checked.detail);
}

#[test]
fn matching_jurisdiction_still_hits() {
    let checked = corpus::audit(
        &[constitution()],
        &Citation {
            jurisdiction: "CN",
            ..citation("宪法", "第三十九条", QUOTE_39)
        },
    );
    assert_eq!(checked.audit, Audit::Hit);
}

#[test]
fn names_match_the_title_or_an_alias_after_whitespace_normalization() {
    let corpus = constitution();
    assert!(corpus.matches_name("中华人民共和国宪法"));
    assert!(corpus.matches_name("  中华人民共和国宪法  "));
    assert!(corpus.matches_name("宪法"));
    assert!(!corpus.matches_name("宪法性文件"));

    for name in ["宪法", " 中华人民共和国宪法 "] {
        let checked = corpus::audit(
            std::slice::from_ref(&corpus),
            &citation(name, "第三十九条", QUOTE_39),
        );
        assert_eq!(checked.audit, Audit::Hit, "`{name}`");
    }
}

#[test]
fn article_lookup_normalizes_whitespace() {
    let checked = corpus::audit(
        &[constitution()],
        &citation("宪法", " 第三十九条 ", QUOTE_39),
    );
    assert_eq!(checked.audit, Audit::Hit);
}

#[test]
fn scan_loads_corpora_in_stable_order_and_ignores_other_files() {
    let temp = TempDir::new("scan");
    temp.write(
        "cn.a/2018.json",
        &corpus_json("cn.a", "甲法", "[]", "2018", &article("第一条", "a")),
    );
    temp.write(
        "cn.b/2019.json",
        &corpus_json("cn.b", "乙法", "[]", "2019", &article("第一条", "b")),
    );
    temp.write("cn.a/notes.txt", "not a corpus");
    temp.write("README.txt", "not a corpus");

    let scan = corpus::scan(temp.path()).expect("the directory is readable");
    assert!(scan.errors.is_empty(), "{:?}", scan.errors);
    let laws: Vec<&str> = scan
        .corpora
        .iter()
        .map(|loaded| loaded.corpus.law.as_str())
        .collect();
    assert_eq!(laws, ["cn.a", "cn.b"]);
}

#[test]
fn scan_reports_a_missing_root() {
    let temp = TempDir::new("missing");
    let missing = temp.path().join("does-not-exist");
    let error = corpus::scan(&missing).expect_err("a missing root is an error");
    assert!(error.message().contains("无法读取语料目录"), "{error}");
}

#[test]
fn scan_reports_bad_json_but_keeps_valid_corpora() {
    let temp = TempDir::new("bad-json");
    temp.write(
        "cn.a/2018.json",
        &corpus_json("cn.a", "甲法", "[]", "2018", &article("第一条", "a")),
    );
    temp.write("cn.b/2018.json", "not json");

    let scan = corpus::scan(temp.path()).expect("the directory is readable");
    assert_eq!(scan.corpora.len(), 1);
    assert_eq!(scan.errors.len(), 1);
    assert!(scan.errors[0].message().contains("JSON 解析失败"));
}

#[test]
fn scan_reports_duplicate_law_and_version() {
    let temp = TempDir::new("duplicate");
    let body = corpus_json("cn.a", "甲法", "[]", "2018", &article("第一条", "a"));
    temp.write("cn.a/2018.json", &body);
    temp.write("cn.a-copy/2018.json", &body);

    let scan = corpus::scan(temp.path()).expect("the directory is readable");
    assert_eq!(scan.corpora.len(), 1);
    assert_eq!(scan.errors.len(), 1);
    assert!(scan.errors[0].message().contains("重复"));
    assert!(scan.errors[0].message().contains("cn.a@2018"));
}

#[test]
fn scan_of_an_empty_directory_has_no_corpora_and_no_errors() {
    let temp = TempDir::new("empty");
    let scan = corpus::scan(temp.path()).expect("the directory is readable");
    assert!(scan.corpora.is_empty());
    assert!(scan.errors.is_empty());
}

#[test]
fn the_repository_constitution_corpus_parses() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../law/corpus");
    let scan = corpus::scan(&root).expect("the repository corpus directory is readable");
    assert!(scan.errors.is_empty(), "{:?}", scan.errors);
    assert_eq!(scan.corpora.len(), 1);

    let corpus = &scan.corpora[0].corpus;
    assert_eq!(corpus.law, "cn.constitution");
    assert_eq!(corpus.title, "中华人民共和国宪法");
    assert_eq!(corpus.aliases, ["宪法"]);
    assert_eq!(corpus.version, "2018");
    assert_eq!(corpus.jurisdiction, "CN");
    assert_eq!(corpus.effective_from.as_deref(), Some("1982-12-04"));
    assert_eq!(corpus.retrieved_at.as_deref(), Some("2026-11-22"));
    assert_eq!(corpus.text_sha256.as_deref(), Some(FIXTURE_SHA256));
    let numbers: Vec<&str> = corpus
        .articles
        .iter()
        .map(|article| article.number.as_str())
        .collect();
    assert_eq!(
        numbers,
        [
            "第三十三条",
            "第三十五条",
            "第三十七条",
            "第三十九条",
            "第四十六条"
        ]
    );
    assert_eq!(
        corpus
            .article("第三十三条")
            .expect("article 33")
            .text
            .lines()
            .count(),
        4
    );
    assert_eq!(
        corpus
            .article("第三十七条")
            .expect("article 37")
            .text
            .lines()
            .count(),
        3
    );
    assert_eq!(
        corpus.article("第三十九条").expect("article 39").text,
        "中华人民共和国公民的住宅不受侵犯。禁止非法搜查或者非法侵入公民的住宅。"
    );
    assert_eq!(
        corpus
            .article("第四十六条")
            .expect("article 46")
            .text
            .lines()
            .count(),
        2
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
            "std-deduce-lawpack-corpus-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn path(&self) -> &Path {
        &self.path
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
