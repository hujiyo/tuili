//! `interpret` declarations: the line-oriented syntax, what the loader keeps,
//! and what it refuses.
//!
//! An interpretation is loaded as an opaque constant whose type is
//! `from → to`. It is deliberately inert: this file asserts that loading one
//! creates no rule and no fact, so a later branch has to opt into a semantics
//! instead of inheriting one by accident.

use std_deduce_kernel::{DeclKind, Expr, InterpretationDirection};
use std_deduce_lang::ast::Item;
use std_deduce_lang::parser::parse;
use std_deduce_lang::Library;

/// A namespaced module with two propositions and one complete interpretation.
const MODULE: &str = r#"
namespace a
pred a.P : Prop
pred a.Q : Prop
interpret a.i : a.P → a.Q
  direction narrow
  source text "宪法" locator "第三十九条" version "2018"
"#;

fn load(src: &str) -> Result<Library, String> {
    let mut lib = Library::new();
    lib.load("test.std", src)
        .map(|_| lib)
        .map_err(|e| e.to_string())
}

fn load_error(src: &str) -> String {
    load(src).expect_err("the load must fail")
}

/// The one interpretation in `lib`, as the loader stored it.
fn only_interpretation(lib: &Library) -> &std_deduce_kernel::env::Interpretation {
    let all = lib.env.interpretations();
    assert_eq!(all.len(), 1, "expected exactly one interpretation");
    match &all[0].kind {
        DeclKind::Interpretation(interpretation) => interpretation,
        other => panic!("expected an interpretation, got {other:?}"),
    }
}

#[test]
fn the_parser_builds_a_complete_interpretation_item() {
    let items = parse(MODULE).expect("the complete syntax must parse");
    let item = items
        .iter()
        .find(|item| matches!(item, Item::Interpretation { .. }))
        .expect("the parser must build an interpretation item");
    let Item::Interpretation {
        name,
        from,
        to,
        direction,
        sources,
    } = item
    else {
        unreachable!()
    };
    assert_eq!(name, "a.i");
    assert_eq!(*direction, InterpretationDirection::Narrow);
    assert_eq!(sources.len(), 1);
    assert_eq!(sources[0].text, "宪法");
    assert_eq!(sources[0].locator, "第三十九条");
    assert_eq!(sources[0].version, "2018");
    // Both sides are application terms, not `term`s that swallow an arrow.
    assert!(matches!(from, std_deduce_lang::ast::Term::Ident(name) if name == "a.P"));
    assert!(matches!(to, std_deduce_lang::ast::Term::Ident(name) if name == "a.Q"));
}

#[test]
fn a_complete_interpretation_loads_as_an_opaque_constant() {
    let lib = load(MODULE).expect("the interpretation must load");
    let decl = lib
        .env
        .get("a.i")
        .expect("the interpretation is in the ledger");
    assert!(matches!(decl.kind, DeclKind::Interpretation(_)));
    assert!(
        matches!(decl.ty, std_deduce_kernel::Expr::Pi { .. }),
        "the recorded type must be `from → to`: {:?}",
        decl.ty
    );
    let interpretation = only_interpretation(&lib);
    assert_eq!(interpretation.name.as_ref(), "a.i");
    assert_eq!(interpretation.direction, InterpretationDirection::Narrow);
    assert_eq!(interpretation.sources.len(), 1);
    assert_eq!(interpretation.sources[0].text, "宪法");
    assert_eq!(interpretation.sources[0].locator, "第三十九条");
    assert_eq!(interpretation.sources[0].version, "2018");
    // The two sides are stored in their declared order. A swap or a dropped
    // side would leave the same Pi shape, so compare the actual expressions.
    assert_eq!(interpretation.from, Expr::constant("a.P"));
    assert_eq!(interpretation.to, Expr::constant("a.Q"));
    assert_eq!(
        decl.ty,
        Expr::pi(Expr::constant("a.P"), Expr::constant("a.Q")),
        "the recorded type must be `from → to`, not the reverse or a bare side"
    );
    // The declaration-level provenance is the same source list, so a future
    // reader of `Decl.sources` cannot see an empty interpretation.
    assert_eq!(decl.sources.len(), 1);
    assert_eq!(decl.sources[0].text, "宪法");
    assert_eq!(decl.sources[0].locator, "第三十九条");
    assert_eq!(decl.sources[0].version, "2018");

    // Loading an interpretation must not manufacture a rule or a fact: this
    // step only registers the declaration, nothing consumes it.
    assert!(
        lib.env.rules().is_empty(),
        "an interpretation is not a rule"
    );
    assert!(
        !lib.env
            .iter()
            .any(|decl| matches!(decl.kind, DeclKind::Fact { .. })),
        "an interpretation is not a fact"
    );
}

#[test]
fn every_direction_keyword_is_accepted_and_preserved() {
    for (keyword, direction) in [
        ("literal", InterpretationDirection::Literal),
        ("expand", InterpretationDirection::Expand),
        ("narrow", InterpretationDirection::Narrow),
        ("analogy", InterpretationDirection::Analogy),
    ] {
        let src = format!(
            "pred P : Prop\npred Q : Prop\n\
             interpret 解释 : P → Q\n  direction {keyword}\n\
             \x20 source text \"测试\" locator \"一\" version \"2020\"\n"
        );
        let lib = load(&src).unwrap_or_else(|error| panic!("direction {keyword}: {error}"));
        assert_eq!(only_interpretation(&lib).direction, direction);
    }
}

#[test]
fn a_missing_direction_is_refused() {
    let src = "pred P : Prop\npred Q : Prop\n\
               interpret 解释 : P → Q\n\
               \x20 source text \"测试\" locator \"一\" version \"2020\"\n";
    let error = load_error(src);
    assert!(error.contains("`interpret 解释`"), "got: {error}");
    assert!(error.contains("direction"), "got: {error}");
    assert!(error.contains("没有默认"), "got: {error}");
}

#[test]
fn a_missing_source_is_refused() {
    let src = "pred P : Prop\npred Q : Prop\n\
               interpret 解释 : P → Q\n  direction literal\n";
    let error = load_error(src);
    assert!(error.contains("`interpret 解释`"), "got: {error}");
    assert!(error.contains("source"), "got: {error}");
    assert!(error.contains("至少有一条"), "got: {error}");
}

#[test]
fn a_missing_component_error_names_the_interpretation() {
    for (src, side) in [
        ("pred P : Prop\ninterpret 解释 :\n", "from"),
        ("pred P : Prop\ninterpret 解释 : P →\n", "to"),
    ] {
        let error = load_error(src);
        assert!(error.contains("`interpret 解释`"), "for {side}: {error}");
        assert!(
            error.contains(side),
            "the error must say which side failed ({side}): {error}"
        );
    }
}

#[test]
fn a_header_line_clause_is_refused() {
    // `direction` on the header line.
    let src = "pred P : Prop\npred Q : Prop\n\
               interpret 解释 : P → Q direction literal\n\
               \x20 source text \"测试\" locator \"一\" version \"2020\"\n";
    let error = load_error(src);
    assert!(error.contains("`interpret 解释`"), "got: {error}");
    assert!(error.contains("direction"), "got: {error}");
    assert!(error.contains("必须另起一行"), "got: {error}");

    // `source` on the header line. `to` is application-level, so the parser
    // must stop at the clause keyword instead of taking it as an argument.
    let src = "pred P : Prop\npred Q : Prop\n\
               interpret 解释 : P → Q source text \"测试\" locator \"一\" version \"2020\"\n\
               \x20 direction literal\n";
    let error = load_error(src);
    assert!(error.contains("`interpret 解释`"), "got: {error}");
    assert!(error.contains("source"), "got: {error}");
    assert!(error.contains("必须另起一行"), "got: {error}");

    // The same rule applies before the arrow: the reserved clause keyword is
    // never silently read as an application argument.
    let src = "pred P : Prop\npred Q : Prop\n\
               interpret 解释 : P direction literal → Q\n\
               \x20 source text \"测试\" locator \"一\" version \"2020\"\n";
    let error = load_error(src);
    assert!(error.contains("`interpret 解释`"), "got: {error}");
    assert!(error.contains("direction"), "got: {error}");
    assert!(error.contains("必须另起一行"), "got: {error}");
}

#[test]
fn an_arrow_in_a_component_must_be_parenthesized() {
    let src = "pred P : Prop\npred Q : Prop\n\
               interpret 解释 : P → Q → P\n  direction literal\n\
               \x20 source text \"测试\" locator \"一\" version \"2020\"\n";
    let error = load_error(src);
    assert!(error.contains("`interpret 解释`"), "got: {error}");
    assert!(error.contains("括号"), "got: {error}");

    // The same component is accepted once the arrow is parenthesized.
    let parenthesized = "pred P : Prop\npred Q : Prop\n\
                         interpret 解释 : P → (Q → P)\n  direction literal\n\
                         \x20 source text \"测试\" locator \"一\" version \"2020\"\n";
    load(parenthesized).expect("a parenthesized arrow component must load");
}

#[test]
fn a_component_that_is_not_a_proposition_is_refused() {
    // Concept-to-concept is explicitly out of scope for this step.
    let src = "namespace a\nsort a.概念\nobj a.甲 : a.概念\n\
               interpret a.i : a.概念 → a.概念\n  direction literal\n\
               \x20 source text \"测试\" locator \"一\" version \"2020\"\n";
    let error = load_error(src);
    assert!(error.contains("`interpret a.i`"), "got: {error}");
    assert!(error.contains("不是命题"), "got: {error}");
    assert!(error.contains("Sort 0"), "got: {error}");

    // A proposition on the left does not rescue a sort on the right.
    let src = "namespace a\nsort a.概念\npred a.P : Prop\n\
               interpret a.i : a.P → a.概念\n  direction literal\n\
               \x20 source text \"测试\" locator \"一\" version \"2020\"\n";
    let error = load_error(src);
    assert!(error.contains("`interpret a.i`"), "got: {error}");
    assert!(error.contains("不是命题"), "got: {error}");
    assert!(error.contains("to"), "got: {error}");
}

#[test]
fn every_source_field_must_be_non_empty() {
    for (source, what) in [
        ("text \"\" locator \"一\" version \"2020\"", "text"),
        ("text \" \" locator \"一\" version \"2020\"", "text"),
        ("text \"测试\" locator \"\" version \"2020\"", "locator"),
        ("text \"测试\" locator \"一\" version \"\"", "version"),
        ("text \"测试\" locator \"一\" version \" \"", "version"),
    ] {
        let src = format!(
            "pred P : Prop\npred Q : Prop\ninterpret 解释 : P → Q\n\
             \x20 direction literal\n  source {source}\n"
        );
        let error = load_error(&src);
        assert!(
            error.contains("`interpret 解释`"),
            "for {source:?}: {error}"
        );
        assert!(
            error.contains(what),
            "expected the error to name `{what}` for {source:?}: {error}"
        );
        assert!(
            error.contains("非空"),
            "expected a non-empty reason for {source:?}: {error}"
        );
    }
}

#[test]
fn an_unknown_direction_is_refused() {
    let src = "pred P : Prop\npred Q : Prop\n\
               interpret 解释 : P → Q\n  direction sideways\n\
               \x20 source text \"测试\" locator \"一\" version \"2020\"\n";
    let error = load_error(src);
    assert!(error.contains("`interpret 解释`"), "got: {error}");
    assert!(error.contains("sideways"), "got: {error}");
    assert!(
        error.contains("literal") && error.contains("analogy"),
        "the error must list the allowed directions: {error}"
    );
}

#[test]
fn a_duplicate_direction_is_refused() {
    let src = "pred P : Prop\npred Q : Prop\n\
               interpret 解释 : P → Q\n  direction literal\n  direction narrow\n\
               \x20 source text \"测试\" locator \"一\" version \"2020\"\n";
    let error = load_error(src);
    assert!(error.contains("`interpret 解释`"), "got: {error}");
    assert!(error.contains("重复"), "got: {error}");
}

#[test]
fn a_duplicate_interpretation_name_is_refused() {
    let mut lib = load(MODULE).expect("the first load succeeds");
    let before = lib.env.len();
    let src = "namespace a\ninterpret a.i : a.P → a.P\n  direction literal\n\
               \x20 source text \"测试\" locator \"二\" version \"2020\"\n";
    let error = lib
        .load("again.std", src)
        .expect_err("a duplicate interpretation id must be refused")
        .to_string();
    assert!(error.contains("`interpret a.i`"), "got: {error}");
    assert!(error.contains("名称已被占用"), "got: {error}");
    assert_eq!(lib.env.len(), before, "a failed load changed the ledger");
}

#[test]
fn a_case_file_may_declare_an_interpretation() {
    // Outside the closed environment a case/example file may declare its own
    // concepts; the interpretation only needs propositions on both sides.
    let src = "pred P : Prop\npred Q : Prop\n\
               interpret 解释 : P → Q\n  direction analogy\n\
               \x20 source text \"案情\" locator \"一\" version \"2020\"\n";
    let lib = load(src).expect("a case-file interpretation must load");
    assert!(lib.env.get("解释").is_some());
    assert_eq!(
        only_interpretation(&lib).direction,
        InterpretationDirection::Analogy
    );
}
