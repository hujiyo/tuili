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

/// SHA-256 of the staging constitution text. The repository corpus records the
/// same value as provenance; the general fixture only relies on its shape.
const FIXTURE_SHA256: &str =
    "sha256:ee6e873b9595a23b87d25fde0dfa9324dd9c338e71bfdd952dd08e06ae798749";

/// Exact official text of the six articles asserted against the repository corpus.
const OFFICIAL_33: &str = "凡具有中华人民共和国国籍的人都是中华人民共和国公民。\n\
中华人民共和国公民在法律面前一律平等。\n\
国家尊重和保障人权。\n\
任何公民享有宪法和法律规定的权利，同时必须履行宪法和法律规定的义务。";
const OFFICIAL_35: &str = "中华人民共和国公民有言论、出版、集会、结社、游行、示威的自由。";
const OFFICIAL_37: &str = "中华人民共和国公民的人身自由不受侵犯。\n\
任何公民，非经人民检察院批准或者决定或者人民法院决定，并由公安机关执行，不受逮捕。\n\
禁止非法拘禁和以其他方法非法剥夺或者限制公民的人身自由，禁止非法搜查公民的身体。";
const OFFICIAL_39: &str = "中华人民共和国公民的住宅不受侵犯。禁止非法搜查或者非法侵入公民的住宅。";
const OFFICIAL_46: &str = "中华人民共和国公民有受教育的权利和义务。\n\
国家培养青年、少年、儿童在品德、智力、体质等方面全面发展。";
const OFFICIAL_143: &str = "中华人民共和国首都是北京。";

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

/// Insert a coverage declaration into the fixture corpus.
fn constitution_with_coverage(formalized: &str, open_concepts: &str) -> String {
    constitution_with_coverage_fields(formalized, open_concepts, Some("声明"))
}

fn constitution_with_coverage_fields(
    formalized: &str,
    open_concepts: &str,
    notes: Option<&str>,
) -> String {
    let notes = notes
        .map(|notes| format!(",\n    \"notes\": \"{notes}\""))
        .unwrap_or_default();
    let coverage = format!(
        "  \"coverage\": {{\n    \"formalized\": [{formalized}],\n    \"open_concepts\": [{open_concepts}]{notes}\n  }},\n"
    );
    constitution_json().replace("  \"articles\": [", &format!("{coverage}  \"articles\": ["))
}

/// Read a Chinese article number (`第...条`) as an integer.
fn article_number_value(number: &str) -> u32 {
    let body = number
        .strip_prefix('第')
        .and_then(|rest| rest.strip_suffix('条'))
        .unwrap_or_else(|| panic!("not an article number: {number}"));
    let mut total = 0;
    let mut current = 0;
    let mut seen = false;
    for character in body.chars() {
        match character {
            '零' | '〇' => {
                current = 0;
                seen = true;
            }
            '一' => {
                current = 1;
                seen = true;
            }
            '二' => {
                current = 2;
                seen = true;
            }
            '三' => {
                current = 3;
                seen = true;
            }
            '四' => {
                current = 4;
                seen = true;
            }
            '五' => {
                current = 5;
                seen = true;
            }
            '六' => {
                current = 6;
                seen = true;
            }
            '七' => {
                current = 7;
                seen = true;
            }
            '八' => {
                current = 8;
                seen = true;
            }
            '九' => {
                current = 9;
                seen = true;
            }
            '十' => {
                if !seen {
                    current = 1;
                }
                total += current * 10;
                current = 0;
                seen = false;
            }
            '百' => {
                if !seen {
                    current = 1;
                }
                total += current * 100;
                current = 0;
                seen = false;
            }
            other => panic!("unexpected numeral {other} in {number}"),
        }
    }
    total + current
}

/// Render an article number in the canonical Chinese form used by the corpus.
fn canonical_article_number(value: u32) -> String {
    let digit = |value: u32| {
        "零一二三四五六七八九"
            .chars()
            .nth(value as usize)
            .unwrap_or_else(|| panic!("not a digit: {value}"))
    };
    let below_hundred = |value: u32| -> String {
        if value < 10 {
            digit(value).to_string()
        } else if value < 20 {
            if value == 10 {
                "十".to_owned()
            } else {
                format!("十{}", digit(value % 10))
            }
        } else if value.is_multiple_of(10) {
            format!("{}十", digit(value / 10))
        } else {
            format!("{}十{}", digit(value / 10), digit(value % 10))
        }
    };
    let body = if value < 100 {
        below_hundred(value)
    } else {
        let hundreds = value / 100;
        let rest = value % 100;
        let tens = rest / 10;
        let ones = rest % 10;
        if rest == 0 {
            format!("{}百", digit(hundreds))
        } else if rest < 10 {
            format!("{}百零{}", digit(hundreds), digit(rest))
        } else if ones == 0 {
            format!("{}百{}十", digit(hundreds), digit(tens))
        } else {
            format!("{}百{}十{}", digit(hundreds), digit(tens), digit(ones))
        }
    };
    format!("第{body}条")
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
    assert_eq!(corpus.coverage, None);
}

#[test]
fn coverage_parses_and_may_have_no_open_concepts() {
    let text = constitution_with_coverage(r#""第三十九条""#, r#""住宅", "非法""#);
    let corpus = Corpus::parse(&text).expect("the coverage declaration is valid");
    let coverage = corpus.coverage.as_ref().expect("coverage was parsed");
    assert_eq!(coverage.formalized, ["第三十九条"]);
    assert_eq!(coverage.open_concepts, ["住宅", "非法"]);
    assert_eq!(coverage.notes.as_deref(), Some("声明"));

    let text = constitution_with_coverage(r#""第三十九条""#, "");
    let corpus = Corpus::parse(&text).expect("open_concepts may be empty");
    assert!(corpus.coverage.unwrap().open_concepts.is_empty());
}

#[test]
fn coverage_without_notes_parses() {
    let text = constitution_with_coverage_fields(r#""第三十九条""#, r#""住宅""#, None);
    let corpus = Corpus::parse(&text).expect("coverage.notes is optional");
    let coverage = corpus.coverage.expect("coverage was parsed");
    assert_eq!(coverage.notes, None);
}

#[test]
fn coverage_rejects_unknown_duplicate_or_blank_formalized_numbers() {
    for (formalized, expected) in [
        (r#""第四十条""#, "不在 articles"),
        (r#""第三十九条", "第三十九条""#, "重复"),
        (r#""""#, "coverage.formalized[0]"),
        ("", "不能为空"),
        (r#"" 第三十九条""#, "首尾空白"),
        (r#""第三十九条 ""#, "首尾空白"),
        (r#""\t第三十九条""#, "首尾空白"),
    ] {
        let text = constitution_with_coverage(formalized, "");
        let error = parse_error(&text);
        assert!(
            error.contains(expected),
            "`{formalized}` expected `{expected}`: {error}"
        );
    }
}

#[test]
fn coverage_rejects_duplicate_or_blank_open_concepts() {
    for (concepts, expected) in [
        (r#""住宅", "住宅""#, "重复"),
        (r#""住宅", " ""#, "coverage.open_concepts[1]"),
        (r#"" 住宅""#, "首尾空白"),
        (r#""住宅 ""#, "首尾空白"),
    ] {
        let text = constitution_with_coverage(r#""第三十九条""#, concepts);
        let error = parse_error(&text);
        assert!(
            error.contains(expected),
            "`{concepts}` expected `{expected}`: {error}"
        );
    }
}

#[test]
fn coverage_rejects_unknown_fields() {
    let text = constitution_with_coverage(r#""第三十九条""#, r#""住宅""#)
        .replace("\"notes\": \"声明\"", "\"notes\": \"声明\", \"bogus\": 1");
    let error = parse_error(&text);
    assert!(error.contains("bogus"), "{error}");
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
    assert!(!result.hash_checked, "no hash was recorded");
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
    assert!(checked.hash_checked);
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
    assert!(checked.hash_checked);
}

#[test]
fn a_valid_hash_is_not_checked_when_the_quote_differs() {
    let checked = corpus::audit(
        &[ascii_corpus()],
        &Citation {
            hash: ABC_SHA256,
            ..citation("测试法", "第一条", "abd")
        },
    );
    assert_eq!(checked.audit, Audit::Mismatch);
    assert!(!checked.hash_checked);
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
    assert!(
        checked.detail.contains("条文哈希不符"),
        "{}",
        checked.detail
    );
    assert!(checked.hash_checked, "a well-formed hash was compared");
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
        assert!(!checked.hash_checked, "`{value}` was never compared");
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
    assert!(!checked.hash_checked, "no hash was recorded");
}

#[test]
fn a_hash_is_checked_before_the_jurisdiction() {
    let checked = corpus::audit(
        &[ascii_corpus()],
        &Citation {
            hash: ABC_SHA256,
            jurisdiction: "US",
            ..citation("测试法", "第一条", "abc")
        },
    );
    assert_eq!(checked.audit, Audit::JurisdictionMismatch);
    assert!(checked.hash_checked);
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
fn scan_loads_corpora_in_stable_order() {
    let temp = TempDir::new("scan");
    temp.write(
        "cn.a/2018.json",
        &corpus_json("cn.a", "甲法", "[]", "2018", &article("第一条", "a")),
    );
    temp.write(
        "cn.b/2019.json",
        &corpus_json("cn.b", "乙法", "[]", "2019", &article("第一条", "b")),
    );

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
fn scan_rejects_entries_outside_the_layout() {
    let temp = TempDir::new("layout");
    temp.write(
        "cn.a/2018.json",
        &corpus_json("cn.a", "甲法", "[]", "2018", &article("第一条", "a")),
    );
    temp.write("README.txt", "not a corpus");
    temp.write("cn.a/notes.txt", "not a corpus");
    temp.write("cn.a/2018/nested.json", "not json");

    let scan = corpus::scan(temp.path()).expect("the directory is readable");
    assert_eq!(scan.corpora.len(), 1, "the valid corpus still loads");
    assert_eq!(scan.errors.len(), 3, "{:?}", scan.errors);
    assert!(
        scan.errors
            .iter()
            .any(|error| error.message().contains("根目录")),
        "{:?}",
        scan.errors
    );
    assert!(
        scan.errors
            .iter()
            .any(|error| error.message().contains("子目录")),
        "{:?}",
        scan.errors
    );
    assert!(
        scan.errors
            .iter()
            .any(|error| error.message().contains("<version>.json")),
        "{:?}",
        scan.errors
    );
    assert!(
        scan.errors
            .iter()
            .any(|error| error.path().ends_with("cn.a/2018") && error.message().contains("子目录")),
        "the nested directory must not be skipped silently: {:?}",
        scan.errors
    );
}

#[test]
fn scan_rejects_a_directory_name_that_does_not_match_law() {
    let temp = TempDir::new("dir-name");
    temp.write(
        "cn.other/2018.json",
        &corpus_json("cn.a", "甲法", "[]", "2018", &article("第一条", "a")),
    );

    let scan = corpus::scan(temp.path()).expect("the directory is readable");
    assert!(scan.corpora.is_empty());
    assert_eq!(scan.errors.len(), 1);
    let message = scan.errors[0].message();
    assert!(message.contains("目录名"), "{message}");
    assert!(message.contains("cn.a"), "{message}");
    assert!(message.contains("cn.other"), "{message}");
}

#[test]
fn scan_rejects_a_file_name_that_does_not_match_version() {
    let temp = TempDir::new("file-name");
    temp.write(
        "cn.a/2019.json",
        &corpus_json("cn.a", "甲法", "[]", "2018", &article("第一条", "a")),
    );

    let scan = corpus::scan(temp.path()).expect("the directory is readable");
    assert!(scan.corpora.is_empty());
    assert_eq!(scan.errors.len(), 1);
    let message = scan.errors[0].message();
    assert!(message.contains("文件名主干"), "{message}");
    assert!(message.contains("2018"), "{message}");
}

#[test]
fn scan_rejects_an_empty_law_directory() {
    let temp = TempDir::new("empty-law");
    temp.dir("cn.a");

    let scan = corpus::scan(temp.path()).expect("the directory is readable");
    assert!(scan.corpora.is_empty());
    assert_eq!(scan.errors.len(), 1);
    assert!(
        scan.errors[0].message().contains("没有任何语料"),
        "{:?}",
        scan.errors
    );
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
    let notes = corpus.notes.as_deref().unwrap_or_default();
    assert!(notes.contains("序言未入库"), "{notes}");
    assert!(notes.contains("1982-12-04"), "{notes}");
    assert!(notes.contains("2018 修正文本"), "{notes}");

    assert_eq!(corpus.articles.len(), 143);
    let values: Vec<u32> = corpus
        .articles
        .iter()
        .map(|article| article_number_value(&article.number))
        .collect();
    assert_eq!(values, (1u32..=143).collect::<Vec<_>>());
    assert_eq!(corpus.articles[0].number, "第一条");
    assert_eq!(corpus.articles[142].number, "第一百四十三条");
    for article in &corpus.articles {
        assert!(
            !article.text.starts_with(&article.number),
            "{} still starts with its article number",
            article.number
        );
    }

    for (number, expected) in [
        ("第三十三条", OFFICIAL_33),
        ("第三十五条", OFFICIAL_35),
        ("第三十七条", OFFICIAL_37),
        ("第三十九条", OFFICIAL_39),
        ("第四十六条", OFFICIAL_46),
        ("第一百四十三条", OFFICIAL_143),
    ] {
        let article = corpus
            .article(number)
            .unwrap_or_else(|| panic!("missing {number}"));
        assert_eq!(article.text, expected, "{number}");
    }

    let coverage = corpus
        .coverage
        .as_ref()
        .expect("the repository corpus declares coverage");
    assert_eq!(
        coverage.formalized,
        [
            "第三十三条",
            "第三十四条",
            "第三十五条",
            "第三十六条",
            "第三十七条",
            "第三十八条",
            "第三十九条",
            "第四十条",
            "第四十一条",
            "第四十二条",
            "第四十三条",
            "第四十四条",
            "第四十五条",
            "第四十六条"
        ]
    );
    assert_eq!(
        coverage.open_concepts,
        [
            "非法",
            "住宅",
            "侵犯",
            "人身自由",
            "言论自由",
            "出版自由",
            "集会自由",
            "结社自由",
            "游行自由",
            "示威自由",
            "受教育权",
            "中国国籍",
            "年满十八周岁",
            "依法被剥夺政治权利",
            "正常宗教活动",
            "侮辱",
            "诽谤",
            "诬告陷害",
            "通信自由",
            "通信秘密",
            "国家安全",
            "批评建议",
            "申诉控告检举",
            "违法失职",
            "劳动能力",
            "退休",
            "物质帮助",
            "年老",
            "疾病",
        ]
    );
    assert!(
        !coverage.formalized.iter().any(|number| number == "第五条"),
        "article 5 is indexed, not formalized in the official pack"
    );
    assert!(
        !coverage
            .formalized
            .iter()
            .any(|number| number == "第四十七条"),
        "article 47 belongs to the next batch and is not formalized yet"
    );
    let notes = coverage.notes.as_deref().unwrap_or_default();
    assert!(
        notes.contains("不等于整条完整形式化"),
        "coverage.notes must define formalized as a lower bar than a whole article: {notes:?}"
    );
    assert!(
        notes.contains("第三十六、四十、四十四条按 partial 处理"),
        "coverage.notes must name the partial articles: {notes:?}"
    );
    assert!(
        notes.contains("合法检查程序") && notes.contains("退休制度"),
        "coverage.notes must name the unmodelled sentences: {notes:?}"
    );
    assert!(
        notes.contains("光荣职责") && notes.contains("不窄化该义务"),
        "coverage.notes must explain the article 42 reading: {notes:?}"
    );
    assert!(
        notes.contains("不要求提出者本人受侵害")
            && notes.contains("具体是哪个机关或人员是开放概念"),
        "coverage.notes must explain the article 41 condition: {notes:?}"
    );
    assert!(
        notes.contains("第二章第一批") && notes.contains("第四十七至五十六条"),
        "{notes:?}"
    );
}

#[test]
fn the_repository_constitution_article_numbers_are_canonical() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../law/corpus");
    let scan = corpus::scan(&root).expect("the repository corpus directory is readable");
    assert!(scan.errors.is_empty(), "{:?}", scan.errors);
    let corpus = &scan.corpora[0].corpus;
    let actual: Vec<&str> = corpus
        .articles
        .iter()
        .map(|article| article.number.as_str())
        .collect();
    let expected: Vec<String> = (1..=143).map(canonical_article_number).collect();
    assert_eq!(actual, expected);
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

    fn dir(&self, relative: &str) -> PathBuf {
        let path = self.path.join(relative);
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        path
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
