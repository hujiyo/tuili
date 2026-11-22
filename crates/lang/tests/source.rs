//! Lexer and parser tests for the structured `source` clause.
//!
//! A source is a sequence of known `key "value"` pairs. Values are quoted
//! strings with a deliberately small escape set, so article text, URLs and
//! quotations survive parsing without opening a second, string-free syntax.

use std_deduce_lang::ast::{Item, SourceSpec};
use std_deduce_lang::lexer::{lex, Tok};
use std_deduce_lang::parser::{parse, ParseError};

fn parse_source(clause: &str) -> Result<SourceSpec, ParseError> {
    let src = format!("sort 公民\n{clause}\n");
    let items = parse(&src)?;
    match items.into_iter().next() {
        Some(Item::Sort {
            source: Some(source),
            ..
        }) => Ok(source),
        other => panic!("expected a sort with one source clause, got {other:?}"),
    }
}

#[test]
fn strings_decode_the_supported_escapes_and_unicode_characters() {
    let toks = lex(
        r#""宪法\n第三十九条\t附件\r" "https://www.npc.gov.cn/law?article=39&lang=zh#top" "甲\\乙\"丙""#,
    )
    .expect("string literals lex");
    let strings: Vec<&str> = toks
        .iter()
        .filter_map(|token| match &token.tok {
            Tok::Str(value) => Some(value.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(
        strings,
        vec![
            "宪法\n第三十九条\t附件\r",
            "https://www.npc.gov.cn/law?article=39&lang=zh#top",
            "甲\\乙\"丙",
        ]
    );
}

#[test]
fn escaped_newlines_do_not_advance_the_line_counter() {
    let toks = lex("\"a\\nb\"\n\"c\"").expect("escaped newline is not a line break");
    let positions: Vec<(usize, usize)> = toks
        .iter()
        .filter(|token| matches!(token.tok, Tok::Str(_)))
        .map(|token| (token.line, token.col))
        .collect();
    assert_eq!(positions, vec![(1, 1), (2, 1)]);
}

#[test]
fn an_unterminated_string_reports_the_position_of_its_opening_quote() {
    let error = lex("x\n  \"abc").expect_err("an unterminated string is an error");
    assert_eq!((error.line, error.col), (2, 3));
    assert!(error.msg.contains("未闭合"), "{error}");
}

#[test]
fn an_unknown_escape_reports_its_position() {
    let error = lex("\"a\\q\"").expect_err("an unknown escape is an error");
    assert_eq!((error.line, error.col), (1, 3));
    assert!(error.msg.contains("\\q"), "{error}");
}

#[test]
fn a_bare_newline_inside_a_string_is_rejected() {
    let error = lex("\"ab\ncd\"").expect_err("a raw newline inside a string is an error");
    assert_eq!((error.line, error.col), (1, 4));
    assert!(error.msg.contains("换行"), "{error}");
}

#[test]
fn every_field_parses_in_any_order_and_across_lines() {
    let spec = parse_source(concat!(
        "source\n",
        "  jurisdiction \"CN\"\n",
        "  text \"中华人民共和国宪法\"\n",
        "  locator \"第三十九条\"\n",
        "  version \"2018\"\n",
        "  effective \"1982-12-04\"\n",
        "  quote \"中华人民共和国公民的住宅不受侵犯。\"\n",
        "  url \"https://www.npc.gov.cn/law?article=39&lang=zh\"\n",
        "  retrieved_at \"2026-11-21\"\n",
        "  hash \"sha256:abc\"\n",
        "  note \"备注\"",
    ))
    .expect("a complete source parses");
    assert_eq!(
        spec,
        SourceSpec {
            text: "中华人民共和国宪法".to_owned(),
            locator: "第三十九条".to_owned(),
            version: "2018".to_owned(),
            effective: Some("1982-12-04".to_owned()),
            note: "备注".to_owned(),
            quote: "中华人民共和国公民的住宅不受侵犯。".to_owned(),
            url: "https://www.npc.gov.cn/law?article=39&lang=zh".to_owned(),
            jurisdiction: "CN".to_owned(),
            retrieved_at: "2026-11-21".to_owned(),
            hash: "sha256:abc".to_owned(),
        }
    );
}

#[test]
fn the_clause_stops_before_the_first_token_that_is_not_a_key() {
    let items = parse(
        "rule r :\n  params p : 公民\n  premise 侵占 p\n  conclude 侵占 p\n  source text \"x\" locator \"y\"\n  unless 侵占 p\n",
    )
    .expect("the unless clause after the source parses");
    let Some(Item::Rule {
        sources, defeaters, ..
    }) = items.into_iter().next()
    else {
        panic!("expected one rule");
    };
    assert_eq!(sources.len(), 1);
    assert_eq!(sources[0].locator, "y");
    assert_eq!(defeaters.len(), 1);
}

#[test]
fn a_repeated_key_is_rejected() {
    let error = parse_source("source text \"x\" text \"y\" locator \"z\"")
        .expect_err("a repeated key is an error");
    assert!(
        error.msg.contains("重复") && error.msg.contains("text"),
        "{error}"
    );
}

#[test]
fn an_unknown_key_is_rejected() {
    let error = parse_source("source bogus \"x\" text \"a\" locator \"b\"")
        .expect_err("an unknown key at the start of a source is an error");
    assert!(
        error.msg.contains("source") && error.msg.contains("bogus"),
        "{error}"
    );

    let error = parse_source("source text \"a\" locator \"b\" bogus \"c\"")
        .expect_err("an unknown key after valid pairs is an error");
    assert!(
        error.to_string().contains("bogus"),
        "the error should name the unknown key: {error}"
    );
}

#[test]
fn missing_or_empty_required_fields_are_rejected() {
    for clause in [
        "source locator \"b\"",
        "source text \"a\"",
        "source text \"\" locator \"b\"",
        "source text \"a\" locator \"\"",
    ] {
        let error =
            parse_source(clause).expect_err("required fields must be present and non-empty");
        let missing =
            if clause.starts_with("source text \"\"") || clause.starts_with("source locator") {
                "text"
            } else {
                "locator"
            };
        assert!(
            error.msg.contains(missing),
            "`{clause}` should mention `{missing}`, got: {error}"
        );
    }
}

#[test]
fn the_old_positional_source_syntax_is_rejected() {
    for clause in [
        "source 宪法 第三十九条",
        "source 刑法 第二十条 (version 2020)",
        "source \"宪法\" \"第三十九条\"",
    ] {
        let error =
            parse_source(clause).expect_err("old positional source syntax must be rejected");
        assert!(
            error.msg.contains("source") || error.msg.contains("期望"),
            "`{clause}` should produce a source syntax error, got: {error}"
        );
    }
}
