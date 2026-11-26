//! Surface syntax and typing for calendar dates: the `d"…"` literal, its
//! position-reported errors, the built-in `Date` sort, and the four date
//! operations.

use std_deduce_kernel::builtin;
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{check, Ctx, Date, Env, Expr};
use std_deduce_lang::ast::{Item, Term};
use std_deduce_lang::elab::elab_top;
use std_deduce_lang::lexer::{lex, Tok};
use std_deduce_lang::parser::parse;

/// The term of a `#check <term>` source.
fn checked_term(source: &str) -> Term {
    let items = parse(source).unwrap_or_else(|error| panic!("parse `{source}`: {error}"));
    match items.into_iter().next() {
        Some(Item::Check(term)) => term,
        other => panic!("expected a #check item, got {other:?}"),
    }
}

fn day(value: &str) -> Expr {
    Expr::Date(Date::parse(value).expect("a real calendar day"))
}

#[test]
fn a_date_literal_is_a_token_and_a_term() {
    let tokens = lex(r#"d"2020-05-06""#).expect("the literal lexes");
    assert!(
        matches!(&tokens[0].tok, Tok::Date(date) if date.to_iso() == "2020-05-06"),
        "{:?}",
        tokens[0]
    );
    assert_eq!(tokens[0].line, 1);
    assert_eq!(tokens[0].col, 1);
    assert_eq!(
        checked_term(r#"#check d"2020-05-06""#),
        Term::Date(Date::parse("2020-05-06").expect("a real day"))
    );
}

#[test]
fn a_date_literal_is_an_application_argument() {
    let term = checked_term(r#"#check (addYears d"2020-02-29" 1)"#);
    assert_eq!(
        term,
        Term::App(
            Box::new(Term::App(
                Box::new(Term::Ident("addYears".into())),
                Box::new(Term::Date(Date::parse("2020-02-29").expect("a real day"))),
            )),
            Box::new(Term::Num(1)),
        )
    );
}

#[test]
fn only_the_tight_marker_is_a_date_literal() {
    // A spaced `d "…"` is an identifier followed by a string, and a bare
    // `2020-05-06` is an identifier: neither becomes a date implicitly.
    let tokens = lex(r#"d "2020-05-06""#).expect("the tokens lex");
    assert!(matches!(&tokens[0].tok, Tok::Ident(name) if name == "d"));
    assert!(matches!(&tokens[1].tok, Tok::Str(_)));
    assert!(parse(r#"#check d "2020-05-06""#).is_err());
    assert_eq!(
        checked_term("#check 2020-05-06"),
        Term::Ident("2020-05-06".into())
    );
}

#[test]
fn an_impossible_literal_is_a_lex_error_at_its_position() {
    for (source, needle) in [
        (r#"#check d"2020-02-30""#, "超出 1..29"),
        (r#"#check d"2020-13-01""#, "超出 1..12"),
        (r#"#check d"2021-02-29""#, "超出 1..28"),
        (
            r#"#check d"1899-12-31""#,
            "超出范围 1900-01-01..=9999-12-31",
        ),
        (r#"#check d"2020-5-6""#, "不是 YYYY-MM-DD 格式"),
    ] {
        let error = lex(source).expect_err("the date must be refused");
        assert_eq!(error.line, 1, "{error}");
        assert_eq!(error.col, 8, "the error points at the literal: {error}");
        assert!(error.msg.contains(needle), "{error}");
        assert!(error.msg.contains("日期字面量"), "{error}");
    }
}

#[test]
fn a_date_literal_elaborates_to_the_kernel_literal() {
    let env = Env::new();
    let elaborated =
        elab_top(&env, &checked_term(r#"#check d"2020-05-06""#)).expect("the literal elaborates");
    assert_eq!(elaborated, day("2020-05-06"));
    assert_eq!(print_expr(&elaborated), r#"d"2020-05-06""#);
    // The built-in `Date` sorts the literal, exactly as `Int` sorts a number.
    assert_eq!(
        check::infer(&env, &Ctx::new(), &elaborated).expect("a date has a type"),
        Expr::constant(builtin::DATE)
    );
}

#[test]
fn the_date_operations_have_their_builtin_types() {
    let env = Env::new();
    let ctx = Ctx::new();
    assert_eq!(
        builtin::type_of(builtin::DAYS_BETWEEN).expect("daysBetween is built in"),
        Expr::pi(
            Expr::constant(builtin::DATE),
            Expr::pi(Expr::constant(builtin::DATE), Expr::constant(builtin::INT))
        )
    );
    for operation in [builtin::ADD_DAYS, builtin::ADD_MONTHS, builtin::ADD_YEARS] {
        assert_eq!(
            builtin::type_of(operation).expect("the operation is built in"),
            Expr::pi(
                Expr::constant(builtin::DATE),
                Expr::pi(Expr::constant(builtin::INT), Expr::constant(builtin::DATE))
            )
        );
    }
    // A fully applied date comparison is a proposition; a fully applied
    // integer comparison still is one as well.
    for source in [
        r#"#check (less d"2020-01-01" d"2020-06-01")"#,
        "#check (le 3000 5000)",
    ] {
        let term = elab_top(&env, &checked_term(source)).expect("the comparison elaborates");
        assert_eq!(
            check::infer(&env, &ctx, &term).expect("the comparison is a proposition"),
            Expr::Sort(0)
        );
    }
}

#[test]
fn a_mixed_or_wrong_kind_operand_is_an_explicit_error() {
    let env = Env::new();
    // A date and an integer are different literal kinds: no comparison mixes
    // them, and no date operation accepts a number as a date.
    let mixed = elab_top(&env, &checked_term(r#"#check (less d"2020-01-01" 3000)"#))
        .expect("the comparison elaborates");
    let error = check::infer(&env, &Ctx::new(), &mixed).expect_err("a mixed pair is refused");
    assert!(
        error.to_string().contains("同为 Int 或同为 Date"),
        "{error}"
    );

    let wrong_kind = elab_top(&env, &checked_term("#check (addYears 2020 1)"))
        .expect("the application elaborates");
    let error =
        check::infer(&env, &Ctx::new(), &wrong_kind).expect_err("an integer date is refused");
    assert!(error.to_string().contains("期望 Date"), "{error}");
}

#[test]
fn a_builtin_name_cannot_be_declared_as_a_sort() {
    let mut library = std_deduce_lang::Library::new();
    let error = library
        .load("date-reserved", "sort Date")
        .expect_err("`Date` is reserved");
    assert!(error.to_string().contains("内建"), "{error}");
}
