//! `risk`: a top-level declaration that marks an already declared predicate as
//! belonging to one risk theme.
//!
//! The declaration is metadata. It must name a `pred` and one of the fixed
//! theme keywords, may appear before that predicate in the same file (the same
//! forward-reference rule as `open`), and must not change what the reasoner
//! derives. A predicate carries at most one theme, so a reader can point at
//! exactly one declaration.

use std_deduce_kernel::{name, DeclKind, Expr, RiskTheme};
use std_deduce_lang::ast::Item;
use std_deduce_lang::parser::parse;
use std_deduce_lang::{Library, LoadError};

fn load(src: &str) -> Result<Library, LoadError> {
    let mut lib = Library::new();
    lib.load("test", src).map(|_| lib)
}

fn load_err(src: &str) -> LoadError {
    load(src).expect_err("the source must be refused")
}

#[test]
fn parser_reads_a_risk_declaration_with_its_position() {
    let items = parse("sort 人\nrisk 刑事 故意伤害\n").expect("`risk` must parse");
    assert_eq!(
        items[1],
        Item::Risk {
            theme: "刑事".into(),
            pred: "故意伤害".into(),
            line: 2,
            col: 1,
        }
    );
}

#[test]
fn parser_requires_a_theme_and_a_predicate_name() {
    let error = parse("sort 人\nrisk\n").expect_err("`risk` without a theme must not parse");
    assert_eq!(error.line, 2, "{error}");
    assert!(error.msg.contains("风险类别"), "{error}");

    let error = parse("risk 刑事\n").expect_err("a missing predicate must not parse");
    assert_eq!(error.line, 1, "{error}");
    assert!(error.msg.contains("谓词名"), "{error}");

    let error = parse("risk 刑事 伤害 多余\n").expect_err("trailing tokens must not parse");
    assert_eq!(error.line, 1, "{error}");
    assert!(error.msg.contains("必须是换行"), "{error}");
}

#[test]
fn all_five_themes_load_and_are_reported_by_the_environment() {
    for theme in [
        RiskTheme::Criminal,
        RiskTheme::PersonalSafety,
        RiskTheme::MajorProperty,
        RiskTheme::ApproachingDeadline,
        RiskTheme::ForeignOrImmigration,
    ] {
        let src = format!(
            "sort 人\npred 伤害 : 人 → Prop\nrisk {} 伤害\n",
            theme.keyword()
        );
        let lib = load(&src).expect("a declared theme must load");
        assert_eq!(lib.env.risk_markers(), vec![(name("伤害"), theme)]);
        assert_eq!(
            lib.env
                .get("risk:伤害")
                .expect("the marker is in the ledger")
                .kind,
            DeclKind::Risk {
                theme,
                pred: name("伤害")
            }
        );
        assert!(
            matches!(
                lib.env.get("伤害").expect("the predicate").kind,
                DeclKind::Pred
            ),
            "the target must remain the original predicate"
        );
        assert!(
            !lib.env
                .iter()
                .any(|decl| matches!(decl.kind, DeclKind::Fact { .. })),
            "a risk declaration must not become a fact"
        );
    }
}

/// A marker needs no provenance of its own and is not a claim: it loads without
/// a `source` clause and its constant has type `Type`, never a proposition.
#[test]
fn a_risk_declaration_is_metadata_not_a_proposition() {
    let lib = load("sort 人\npred 伤害 : 人 → Prop\nrisk 刑事 伤害\n").expect("loads");
    let marker = lib.env.get("risk:伤害").expect("the marker");
    assert_eq!(marker.ty, Expr::Sort(1));
    assert!(marker.sources.is_empty());
    assert!(matches!(marker.kind, DeclKind::Risk { .. }));
}

#[test]
fn an_unknown_theme_is_reported_with_position_and_the_allowed_keywords() {
    let error = load_err("sort 人\npred 伤害 : 人 → Prop\nrisk 危险 伤害\n");
    assert_eq!(error.position(), Some((3, 1)), "{error}");
    let msg = error.to_string();
    assert!(msg.contains("`risk 危险 伤害`"), "{msg}");
    assert!(msg.contains("未知风险类别"), "{msg}");
    for keyword in RiskTheme::keywords() {
        assert!(
            msg.contains(keyword),
            "the diagnostic must list {keyword}: {msg}"
        );
    }
}

#[test]
fn an_unknown_risk_target_is_reported_with_name_position_and_reason() {
    let mut lib = Library::new();
    lib.load("base", "sort 人\n").expect("the base loads");
    let before = lib.env.len();
    let error = lib
        .load("bad", "risk 刑事 不存在\n")
        .expect_err("an unknown risk target must be refused");
    assert_eq!(error.position(), Some((1, 1)), "{error}");
    let msg = error.to_string();
    assert!(msg.contains("`risk 刑事 不存在`"), "{msg}");
    assert!(msg.contains("未知谓词"), "{msg}");
    assert_eq!(lib.env.len(), before, "the failed load changed the ledger");
}

#[test]
fn a_risk_target_that_is_not_a_predicate_is_rejected() {
    for (src, line, target) in [
        ("sort 人\nsort 目标\nrisk 刑事 目标\n", 3, "目标"),
        ("sort 人\nobj 甲 : 人\nrisk 刑事 甲\n", 3, "甲"),
        (
            "axiom 假 : Prop\n  source text \"t\" locator \"l\"\nrisk 刑事 假\n",
            3,
            "假",
        ),
        (
            "sort 人\npred P : 人 → Prop\n\
             def 别名 : 人 → Prop := λ (x : 人) := P x\nrisk 刑事 别名\n",
            4,
            "别名",
        ),
    ] {
        let error = load_err(src);
        assert_eq!(
            error.position(),
            Some((line, 1)),
            "for {src:?}, got: {error}"
        );
        let msg = error.to_string();
        assert!(msg.contains(&format!("`risk 刑事 {target}`")), "{msg}");
        assert!(msg.contains("不是谓词"), "{msg}");
    }
}

#[test]
fn marking_the_same_predicate_twice_is_rejected() {
    let error = load_err("sort 人\npred 伤害 : 人 → Prop\nrisk 刑事 伤害\nrisk 人身安全 伤害\n");
    assert_eq!(error.position(), Some((4, 1)), "{error}");
    let msg = error.to_string();
    assert!(msg.contains("`risk 人身安全 伤害`"), "{msg}");
    assert!(msg.contains("已经标记") && msg.contains("重复"), "{msg}");
}

#[test]
fn a_duplicate_marker_across_files_is_rejected_and_the_library_is_unchanged() {
    let mut lib = Library::new();
    lib.load("one", "sort 人\npred 伤害 : 人 → Prop\nrisk 刑事 伤害\n")
        .expect("the first marker loads");
    let before = lib.env.len();

    let error = lib
        .load("two", "risk 刑事 伤害\n")
        .expect_err("a second marker across files must be refused");
    assert_eq!(error.position(), Some((1, 1)), "{error}");
    assert!(error.to_string().contains("已经标记"), "{error}");
    assert_eq!(lib.env.len(), before, "the failed load changed the ledger");
    assert_eq!(
        lib.env.risk_markers(),
        vec![(name("伤害"), RiskTheme::Criminal)]
    );
}

/// `risk` may name a predicate declared later in the same file, like `open`.
#[test]
fn a_namespaced_module_may_mark_a_predicate_declared_later() {
    let lib = load("namespace a\nsort a.人\nrisk 刑事 a.伤害\npred a.伤害 : a.人 → Prop\n")
        .expect("a forward reference in the same file is legal");
    assert_eq!(
        lib.env.risk_markers(),
        vec![(name("a.伤害"), RiskTheme::Criminal)]
    );
    assert_eq!(
        lib.env
            .get("risk:a.伤害")
            .expect("the marker is in the ledger")
            .kind,
        DeclKind::Risk {
            theme: RiskTheme::Criminal,
            pred: name("a.伤害")
        }
    );
}

#[test]
fn a_case_file_may_mark_a_predicate_from_a_loaded_module() {
    let mut lib = Library::new();
    lib.load(
        "module",
        "namespace a\nsort a.人\npred a.伤害 : a.人 → Prop\n",
    )
    .expect("the module loads");
    lib.load("case", "risk 刑事 a.伤害\n")
        .expect("a case file may reference a loaded module");
    assert_eq!(
        lib.env.risk_markers(),
        vec![(name("a.伤害"), RiskTheme::Criminal)]
    );
}

#[test]
fn a_module_risk_reference_must_be_fully_qualified() {
    let error = load_err("namespace a\nsort a.人\npred a.伤害 : a.人 → Prop\nrisk 刑事 伤害\n");
    let msg = error.to_string();
    assert!(msg.contains("`risk 刑事 伤害`"), "{msg}");
    assert!(msg.contains("未限定"), "{msg}");
}

#[test]
fn a_repeated_unknown_target_reports_the_unknown_predicate_not_a_duplicate() {
    // Target validation runs before duplicate detection, so the first fix a
    // reader must make is the one that explains the failure.
    let error = load_err("pred 已知 : Prop\nrisk 刑事 不存在\nrisk 刑事 不存在\n");
    let message = error.to_string();
    assert!(message.contains("未知谓词"), "{message}");
    assert!(!message.contains("重复"), "{message}");
}
