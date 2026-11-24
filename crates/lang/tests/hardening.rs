//! Malformed-input and resource-limit tests for the lexer and parser.
//!
//! These tests are deliberately adversarial: every case must end in an
//! ordinary `Err` carrying a position, never in a panic, a stack overflow or a
//! silent success. Each bound is also tested at its exact edge, so the limit
//! is neither off by one nor quietly stricter than documented.

use std_deduce_lang::lexer::MAX_IDENTIFIER_CHARS;
use std_deduce_lang::parser::{parse, MAX_APPLICATION_ARITY, MAX_RULE_BINDERS, MAX_TERM_DEPTH};

/// Return the parse error message, panicking with the input's size when the
/// parser unexpectedly accepts it.
fn parse_error(src: &str) -> String {
    match parse(src) {
        Ok(items) => panic!(
            "malformed input was accepted ({} items, {} bytes)",
            items.len(),
            src.len()
        ),
        Err(error) => error.msg,
    }
}

#[test]
fn an_empty_file_parses_to_no_items() {
    for src in ["", "   \n\t\n", "-- 只有注释，没有声明\n"] {
        let items = parse(src).unwrap_or_else(|e| panic!("empty program must parse: {e}"));
        assert!(items.is_empty(), "empty program must declare nothing");
    }
}

#[test]
fn a_deeply_nested_term_is_rejected() {
    let depth = 2_000;
    let src = format!(
        "axiom 深 : {}Prop{}\n",
        "(".repeat(depth),
        ")".repeat(depth)
    );
    let message = parse_error(&src);
    assert!(
        message.contains("嵌套深度超过上限"),
        "deep nesting must name the depth limit, got: {message}"
    );
}

/// The top-level term is depth 1, so `MAX_TERM_DEPTH - 1` parentheses stay
/// inside the bound and one more is rejected.
#[test]
fn the_term_depth_limit_is_exact() {
    let allowed = MAX_TERM_DEPTH - 1;
    let src = format!(
        "axiom 深 : {}Prop{}\n",
        "(".repeat(allowed),
        ")".repeat(allowed)
    );
    parse(&src).unwrap_or_else(|e| panic!("depth {allowed} must parse: {e}"));

    let src = format!(
        "axiom 深 : {}Prop{}\n",
        "(".repeat(allowed + 1),
        ")".repeat(allowed + 1)
    );
    let message = parse_error(&src);
    assert!(message.contains("嵌套深度超过上限"), "got: {message}");
}

#[test]
fn a_long_arrow_chain_is_rejected() {
    let src = format!("axiom 深 : {}Prop\n", "Prop → ".repeat(2_000));
    let message = parse_error(&src);
    assert!(
        message.contains("嵌套深度超过上限"),
        "a long arrow chain must name the depth limit, got: {message}"
    );
}

#[test]
fn a_long_application_chain_is_rejected() {
    let src = format!("axiom 深 : f {}\n", "a ".repeat(2_000));
    let message = parse_error(&src);
    assert!(
        message.contains("参数数量超过上限"),
        "an over-long application must name its limit, got: {message}"
    );
}

#[test]
fn the_application_arity_limit_is_exact() {
    let args = |count: usize| {
        let mut src = String::from("axiom 深 : f");
        for _ in 0..count {
            src.push_str(" a");
        }
        src.push('\n');
        src
    };
    parse(&args(MAX_APPLICATION_ARITY))
        .unwrap_or_else(|e| panic!("arity {MAX_APPLICATION_ARITY} must parse: {e}"));
    let message = parse_error(&args(MAX_APPLICATION_ARITY + 1));
    assert!(message.contains("参数数量超过上限"), "got: {message}");
}

#[test]
fn an_overlong_identifier_is_rejected() {
    let identifier = "甲".repeat(2_000);
    let src = format!("sort {identifier}\n");
    let message = parse_error(&src);
    assert!(
        message.contains("标识符长度超过上限"),
        "an over-long identifier must name its limit, got: {message}"
    );
}

#[test]
fn the_identifier_length_limit_is_exact() {
    // `sort` plus a space is not part of the identifier.
    let identifier = "甲".repeat(MAX_IDENTIFIER_CHARS);
    let src = format!("sort {identifier}\n");
    parse(&src).unwrap_or_else(|e| panic!("an identifier at the limit must parse: {e}"));

    let identifier = "甲".repeat(MAX_IDENTIFIER_CHARS + 1);
    let src = format!("sort {identifier}\n");
    let message = parse_error(&src);
    assert!(message.contains("标识符长度超过上限"), "got: {message}");
}

#[test]
fn an_unterminated_string_reports_the_opening_position() {
    let error = parse("axiom 命题 : Prop source text \"未闭合")
        .expect_err("an unterminated string must not parse");
    assert!(error.msg.contains("未闭合字符串"), "got: {}", error.msg);
    assert_eq!(error.line, 1);
    assert!(error.col > 1, "the error must point at the opening quote");
}

#[test]
fn a_trailing_backslash_in_a_string_is_rejected() {
    let error = parse("axiom 命题 : Prop source text \"abc\\")
        .expect_err("a trailing escape must not parse");
    assert!(error.msg.contains("未闭合字符串"), "got: {}", error.msg);
}

#[test]
fn raw_control_characters_are_rejected_and_escaped() {
    let error = parse("sort 公\u{0}民\n").expect_err("a raw NUL must not parse");
    assert!(error.msg.contains("无法识别的字符"), "got: {}", error.msg);
    assert!(
        error.msg.contains("\\u{0000}"),
        "the diagnostic must escape the control character, got: {}",
        error.msg
    );
    assert!(
        !error.msg.contains('\u{0}'),
        "the raw control character must not reach the message"
    );
}

#[test]
fn a_control_character_inside_a_string_is_rejected() {
    let error = parse("axiom 命题 : Prop source text \"a\u{1b}b\"\n")
        .expect_err("a raw escape character in a string must not parse");
    assert!(error.msg.contains("裸控制字符"), "got: {}", error.msg);
}

/// The language has line comments only. A `--` with no newline at end of file
/// is a complete comment, not an error: the rest of the file is the comment.
#[test]
fn an_unterminated_line_comment_is_just_a_comment() {
    let items = parse("sort 公民 -- 注释一直写到文件末尾，没有换行")
        .expect("a line comment without a final newline is valid");
    assert_eq!(items.len(), 1, "the declaration before the comment is kept");
}

#[test]
fn a_rule_with_too_many_binders_is_rejected() {
    let params_only = |parameters: usize| {
        let mut src = String::from("rule 长 :\n  params ");
        for index in 0..parameters {
            if index > 0 {
                src.push_str(", ");
            }
            src.push_str(&format!("x{index} : 公民"));
        }
        src.push_str("\n  conclude 结论\n");
        src
    };
    parse(&params_only(MAX_RULE_BINDERS))
        .unwrap_or_else(|e| panic!("{MAX_RULE_BINDERS} parameters must parse: {e}"));
    let message = parse_error(&params_only(MAX_RULE_BINDERS + 1));
    assert!(
        message.contains("参数与前提合计超过上限"),
        "an over-long telescope must name its limit, got: {message}"
    );

    // A rule mixes parameters and premise binders; the bound covers their
    // sum, because the kernel checks them as one telescope.
    let half = MAX_RULE_BINDERS / 2;
    let mixed = |premises: usize| {
        let mut src = String::from("rule 长 :\n  params ");
        for index in 0..half {
            if index > 0 {
                src.push_str(", ");
            }
            src.push_str(&format!("x{index} : 公民"));
        }
        src.push('\n');
        for index in 0..premises {
            src.push_str(&format!("  premise 谓词{index}\n"));
        }
        src.push_str("  conclude 结论\n");
        src
    };
    parse(&mixed(MAX_RULE_BINDERS - half))
        .unwrap_or_else(|e| panic!("a full telescope must parse: {e}"));
    let message = parse_error(&mixed(MAX_RULE_BINDERS - half + 1));
    assert!(
        message.contains("参数与前提合计超过上限"),
        "the mixed telescope must name its limit, got: {message}"
    );
}

/// The limits must not reject ordinary legal formulas: moderate nesting, a
/// moderate application spine and a normal rule still parse.
#[test]
fn ordinary_terms_still_parse() {
    let depth = 20;
    let nested = format!("{}Prop{}", "(".repeat(depth), ")".repeat(depth));
    let src = format!(
        "sort 公民\npred 谓词 : 公民 → Prop\naxiom 深 : {nested}\n\
         axiom 应用 : f a b c d e g h\nrule 正常 :\n  params x : 公民\n  premise 谓词 x\n  conclude 谓词 x\n"
    );
    parse(&src).expect("ordinary terms must stay within the limits");
}
