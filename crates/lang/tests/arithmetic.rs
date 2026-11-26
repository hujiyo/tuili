//! Surface syntax for exact integers and arithmetic: literals, operator
//! precedence, negation, parentheses, dates and the error positions.

use std_deduce_kernel::builtin;
use std_deduce_kernel::{check, Ctx, Expr};
use std_deduce_lang::ast::{Item, Term};
use std_deduce_lang::elab::elab_top;
use std_deduce_lang::lexer::lex;
use std_deduce_lang::parser::{parse, Parser};

/// The term of a `#check <term>` source.
fn checked_term(source: &str) -> Term {
    let items = parse(source).unwrap_or_else(|error| panic!("parse `{source}`: {error}"));
    match items.into_iter().next() {
        Some(Item::Check(term)) => term,
        other => panic!("expected a #check item, got {other:?}"),
    }
}

fn app(function: &str, argument: Term) -> Term {
    Term::App(
        Box::new(Term::Ident(function.to_owned())),
        Box::new(argument),
    )
}

/// `f a b` as nested applications.
fn apply(function: &str, arguments: Vec<Term>) -> Term {
    arguments
        .into_iter()
        .fold(Term::Ident(function.to_owned()), |function, argument| {
            Term::App(Box::new(function), Box::new(argument))
        })
}

#[test]
fn a_bare_literal_is_an_integer_term() {
    assert_eq!(checked_term("#check 5000"), Term::Num(5000));
}

#[test]
fn a_negative_literal_is_folded_at_parse_time() {
    assert_eq!(checked_term("#check -3000"), Term::Num(-3000));
    // The `i64` minimum is writable; its magnitude is checked as a magnitude.
    assert_eq!(
        checked_term("#check -9223372036854775808"),
        Term::Num(i64::MIN)
    );
}

#[test]
fn a_literal_out_of_range_is_a_parse_error_at_its_position() {
    let error = parse("#check 9223372036854775808").expect_err("the literal does not fit i64");
    assert_eq!(error.line, 1);
    assert_eq!(error.col, 8, "the error points at the literal: {error}");
    assert!(error.msg.contains("超出 i64 范围"), "{error}");
    assert!(error.msg.contains("9223372036854775808"), "{error}");
}

#[test]
fn a_decimal_literal_is_refused_at_its_position() {
    // There is no floating point: `3.5` is a lexical error, not a truncated
    // `3`, not a rounded `4`, and not a name.
    let error = lex("#check 3.5").expect_err("a decimal is not an integer");
    assert_eq!(error.line, 1);
    assert_eq!(error.col, 8, "the error points at the literal: {error}");
    assert!(error.msg.contains("没有小数与浮点"), "{error}");
    assert!(error.msg.contains("3.5"), "{error}");

    let mut library = std_deduce_lang::Library::new();
    let error = library
        .load("decimal.std", "sort 人\n#check 3.5\n")
        .expect_err("a theory with a decimal cannot load");
    assert_eq!(
        error.position(),
        Some((2, 8)),
        "the load diagnostic keeps the position: {error}"
    );
    assert!(error.to_string().contains("没有小数与浮点"), "{error}");
}

#[test]
fn multiplication_binds_tighter_than_addition() {
    // `1 + 2 * 3` is `add 1 (mul 2 3)`.
    let term = checked_term("#check 1 + 2 * 3");
    let expected = Term::App(
        Box::new(Term::App(
            Box::new(Term::Ident("add".into())),
            Box::new(Term::Num(1)),
        )),
        Box::new(Term::App(
            Box::new(Term::App(
                Box::new(Term::Ident("mul".into())),
                Box::new(Term::Num(2)),
            )),
            Box::new(Term::Num(3)),
        )),
    );
    assert_eq!(term, expected);
}

#[test]
fn addition_and_subtraction_are_left_associative() {
    // `1 - 2 - 3` is `sub (sub 1 2) 3`, not `sub 1 (sub 2 3)`.
    let term = checked_term("#check 1 - 2 - 3");
    let expected = Term::App(
        Box::new(Term::App(
            Box::new(Term::Ident("sub".into())),
            Box::new(Term::App(
                Box::new(Term::App(
                    Box::new(Term::Ident("sub".into())),
                    Box::new(Term::Num(1)),
                )),
                Box::new(Term::Num(2)),
            )),
        )),
        Box::new(Term::Num(3)),
    );
    assert_eq!(term, expected);
}

#[test]
fn parentheses_override_the_precedence() {
    // `(1 + 2) * 3` is `mul (add 1 2) 3`.
    let term = checked_term("#check (1 + 2) * 3");
    let expected = Term::App(
        Box::new(Term::App(
            Box::new(Term::Ident("mul".into())),
            Box::new(Term::App(
                Box::new(Term::App(
                    Box::new(Term::Ident("add".into())),
                    Box::new(Term::Num(1)),
                )),
                Box::new(Term::Num(2)),
            )),
        )),
        Box::new(Term::Num(3)),
    );
    assert_eq!(term, expected);
}

#[test]
fn a_leading_minus_of_a_non_literal_is_the_built_in_negation() {
    // `-(3 + 2)` is `neg (add 3 2)`; a plain `-3` stays a literal.
    let term = checked_term("#check -(3 + 2)");
    assert_eq!(term, app("neg", checked_term("#check 3 + 2")));
}

#[test]
fn a_negative_argument_is_written_in_parentheses() {
    // `合计 甲 (-3000)`: the parenthesized negative literal is one argument.
    let term = checked_term("#check 合计 甲 (-3000)");
    assert_eq!(
        term,
        apply("合计", vec![Term::Ident("甲".into()), Term::Num(-3000)])
    );
}

#[test]
fn a_binary_minus_without_spaces_stays_an_identifier() {
    // A `-` inside a word is part of the word (as in `CN-HN` or `2020-05-06`),
    // so `3000-2000` lexes as one identifier and fails at elaboration instead
    // of silently becoming a subtraction.
    let tokens = lex("#check 3000-2000").expect("it lexes as one word");
    let kinds: Vec<&std_deduce_lang::lexer::Tok> = tokens.iter().map(|token| &token.tok).collect();
    assert!(
        kinds.iter().any(
            |token| matches!(token, std_deduce_lang::lexer::Tok::Ident(word) if word == "3000-2000")
        ),
        "expected one hyphenated identifier, got {kinds:?}"
    );
    let term = checked_term("#check 3000-2000");
    assert_eq!(term, Term::Ident("3000-2000".into()));

    let mut library = std_deduce_lang::Library::new();
    let error = library
        .load("minus.std", "sort 人\n#check 3000-2000\n")
        .expect_err("an unknown name must fail");
    assert!(error.to_string().contains("未知名称"), "{error}");
}

#[test]
fn a_date_is_still_lexed_as_one_identifier() {
    let tokens = lex("occurred_at 2020-05-06").expect("dates lex as identifiers");
    let kinds: Vec<&std_deduce_lang::lexer::Tok> = tokens.iter().map(|token| &token.tok).collect();
    assert!(
        kinds
            .iter()
            .any(|token| matches!(token, std_deduce_lang::lexer::Tok::Ident(date) if date == "2020-05-06")),
        "expected the date as one identifier, got {kinds:?}"
    );
}

#[test]
fn arithmetic_terms_elaborate_to_the_built_in_constants() {
    let env = std_deduce_kernel::Env::new();
    let term = checked_term("#check 3000 + 2000");
    let expression = elab_top(&env, &term).expect("the built-ins resolve");
    assert_eq!(
        expression,
        Expr::apps(
            Expr::constant(builtin::ADD),
            [Expr::Num(3000), Expr::Num(2000)]
        )
    );
    assert_eq!(
        check::infer(&env, &Ctx::new(), &expression).expect("it types"),
        Expr::constant(builtin::INT)
    );
}

#[test]
fn comparisons_are_written_in_prefix_form() {
    let env = std_deduce_kernel::Env::new();
    let term = checked_term("#check (less 3000 5000)");
    let expression = elab_top(&env, &term).expect("less resolves");
    assert_eq!(
        expression,
        Expr::apps(
            Expr::constant(builtin::LESS),
            [Expr::Num(3000), Expr::Num(5000)]
        )
    );
    check::check(&env, &Ctx::new(), &expression, &Expr::Sort(0))
        .expect("a comparison is a proposition");
}

#[test]
fn an_unknown_operator_character_is_a_lexical_error_with_a_position() {
    let error = lex("#check 1 / 2").expect_err("`/` is not an operator");
    assert_eq!(error.line, 1);
    assert_eq!(error.col, 10, "the error points at the character: {error}");
    assert!(error.msg.contains('/'), "{error}");
}

#[test]
fn a_rule_conclusion_may_contain_a_sum() {
    // The whole chain has to load: the built-in `add` is resolvable inside a
    // rule telescope, and a literal is accepted where the predicate expects the
    // `金额` alias of `Int`.
    let source = r#"
sort 人
def 金额 : Type := Int
pred 医疗费 : 人 → 金额 → Prop
pred 误工费 : 人 → 金额 → Prop
pred 合计 : 人 → 金额 → Prop
obj 甲 : 人
rule 赔偿合计 :
  params p : 人, a : 金额, b : 金额
  premise 医疗费 p a
  premise 误工费 p b
  conclude 合计 p (a + b)
  source text "测试" locator "夹具"
"#;
    let mut library = std_deduce_lang::Library::new();
    library.load("sum.std", source).expect("the rule loads");
}

#[test]
fn an_operand_of_the_wrong_type_is_refused_at_load() {
    let source = r#"
sort 人
def 金额 : Type := Int
obj 甲 : 人
#check (3000 + 甲)
"#;
    let mut library = std_deduce_lang::Library::new();
    let error = library
        .load("wrong-operand.std", source)
        .expect_err("an individual is not an integer");
    assert!(error.to_string().contains("类型不匹配"), "{error}");
}

#[test]
fn a_type_level_numeral_still_parses() {
    // `Type 3` writes a numeral, which the lexer now emits as a number token.
    let items = parse("#check Type 3").expect("Type 3 parses");
    match items.into_iter().next() {
        Some(Item::Check(Term::Type(Some(3)))) => {}
        other => panic!("expected Type 3, got {other:?}"),
    }
}

#[test]
fn a_unique_argument_position_still_parses() {
    let items =
        parse("sort 人\npred 合计 : 人 → Int → Prop\nunique 合计 2\n").expect("unique parses");
    assert_eq!(items.len(), 3, "sort, pred and unique: {items:?}");
    // The parser only records the surface position; the loader turns it into a
    // zero-based index.
    let mut parser = Parser::new(lex("unique 合计 2").expect("it lexes"));
    let items = parser.program().expect("it parses");
    match items.into_iter().next() {
        Some(Item::Unique { pred, index, .. }) => {
            assert_eq!(pred, "合计");
            assert_eq!(index, 2);
        }
        other => panic!("expected a unique item, got {other:?}"),
    }
}
