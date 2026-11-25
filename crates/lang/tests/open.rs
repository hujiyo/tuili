//! `open`: a top-level declaration that marks an already declared predicate as
//! an open concept.
//!
//! The declaration is metadata. It must name a `pred`, may appear before that
//! predicate in the same file (falling under the same forward-reference rule as
//! `priority` targets), and must not change what the reasoner derives.

use std_deduce_kernel::{name, DeclKind, Expr};
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
fn parser_reads_an_open_declaration_with_its_position() {
    let items = parse("sort 人\nopen 重大\n").expect("`open` must parse");
    assert_eq!(
        items[1],
        Item::Open {
            pred: "重大".into(),
            line: 2,
            col: 1,
        }
    );
}

#[test]
fn parser_requires_a_predicate_name_after_open() {
    let error = parse("sort 人\nopen\n").expect_err("`open` without a name must not parse");
    assert_eq!(error.line, 2, "{error}");
    assert!(error.msg.contains("谓词名"), "{error}");

    let error = parse("open 重大 别的\n").expect_err("trailing tokens must not parse");
    assert_eq!(error.line, 1, "{error}");
    assert!(error.msg.contains("必须是换行"), "{error}");
}

#[test]
fn an_open_declaration_marks_a_declared_predicate() {
    let lib = load("sort 人\npred 重大 : 人 → Prop\nopen 重大\n")
        .expect("an open concept declaration must load");
    assert_eq!(lib.env.open_predicates(), vec![name("重大")]);
    assert_eq!(
        lib.env
            .get("open:重大")
            .expect("the marker is in the ledger")
            .kind,
        DeclKind::OpenConcept {
            pred: name("重大")
        }
    );
    assert!(
        matches!(
            lib.env.get("重大").expect("the predicate").kind,
            DeclKind::Pred
        ),
        "the target must remain the original predicate"
    );
    assert!(
        !lib.env
            .iter()
            .any(|decl| matches!(decl.kind, DeclKind::Fact { .. })),
        "an open concept declaration must not become a fact"
    );
}

/// A marker needs no provenance of its own and is not a claim: it loads
/// without a `source` clause.
#[test]
fn an_open_declaration_needs_no_source() {
    let lib = load("sort 人\npred 重大 : 人 → Prop\nopen 重大\n").expect("no source is required");
    assert_eq!(lib.env.open_predicates(), vec![name("重大")]);
}

#[test]
fn an_unknown_open_target_is_reported_with_name_position_and_reason() {
    let mut lib = Library::new();
    lib.load("base", "sort 人\n").expect("the base loads");
    let before = lib.env.len();
    let error = lib
        .load("bad", "open 不存在\n")
        .expect_err("an unknown open target must be refused");
    assert_eq!(error.position(), Some((1, 1)), "{error}");
    let msg = error.to_string();
    assert!(msg.contains("`open 不存在`"), "{msg}");
    assert!(msg.contains("未知谓词"), "{msg}");
    assert!(msg.contains("不存在"), "{msg}");
    assert_eq!(lib.env.len(), before, "the failed load changed the ledger");
}

#[test]
fn an_open_target_that_is_not_a_predicate_is_rejected() {
    for (src, line, target) in [
        ("sort 人\nsort 目标\nopen 目标\n", 3, "目标"),
        ("sort 人\nobj 甲 : 人\nopen 甲\n", 3, "甲"),
        ("axiom 假 : Prop\n  source text \"t\" locator \"l\"\nopen 假\n", 3, "假"),
        (
            "sort 人\npred P : 人 → Prop\n\
             def 别名 : 人 → Prop := λ (x : 人) := P x\nopen 别名\n",
            4,
            "别名",
        ),
        (
            "sort 人\npred P : 人 → Prop\n\
             rule 规则 :\n  params x : 人\n  premise P x\n  conclude P x\n  source text \"t\" locator \"l\"\n\
             open 规则\n",
            8,
            "规则",
        ),
    ] {
        let error = load_err(src);
        assert_eq!(error.position(), Some((line, 1)), "for {src:?}, got: {error}");
        let msg = error.to_string();
        assert!(msg.contains(&format!("`open {target}`")), "{msg}");
        assert!(msg.contains("不是谓词"), "{msg}");
    }
}

#[test]
fn opening_the_same_predicate_twice_is_rejected() {
    let error = load_err("sort 人\npred 重大 : 人 → Prop\nopen 重大\nopen 重大\n");
    assert_eq!(error.position(), Some((4, 1)), "{error}");
    let msg = error.to_string();
    assert!(msg.contains("`open 重大`"), "{msg}");
    assert!(msg.contains("已经标记") && msg.contains("重复"), "{msg}");
}

#[test]
fn a_duplicate_marker_across_files_is_rejected_and_the_library_is_unchanged() {
    let mut lib = Library::new();
    lib.load("one", "sort 人\npred 重大 : 人 → Prop\nopen 重大\n")
        .expect("the first marker loads");
    let before = lib.env.len();

    let error = lib
        .load("two", "open 重大\n")
        .expect_err("a second marker across files must be refused");
    assert_eq!(error.position(), Some((1, 1)), "{error}");
    assert!(error.to_string().contains("已经标记"), "{error}");
    assert_eq!(lib.env.len(), before, "the failed load changed the ledger");
    assert_eq!(lib.env.open_predicates(), vec![name("重大")]);
}

/// `open` may name a predicate declared later in the same file, like a
/// `priority` target: the loader validates against the completed environment.
#[test]
fn a_namespaced_module_may_open_a_predicate_declared_later() {
    let lib = load("namespace a\nsort a.人\nopen a.重大\npred a.重大 : a.人 → Prop\n")
        .expect("a forward reference in the same file is legal");
    assert_eq!(lib.env.open_predicates(), vec![name("a.重大")]);
    assert_eq!(
        lib.env
            .get("open:a.重大")
            .expect("the marker is in the ledger")
            .kind,
        DeclKind::OpenConcept {
            pred: name("a.重大")
        }
    );
}

#[test]
fn a_case_file_may_open_a_predicate_from_a_loaded_module() {
    let mut lib = Library::new();
    lib.load(
        "module",
        "namespace a\nsort a.人\npred a.重大 : a.人 → Prop\n",
    )
    .expect("the module loads");
    lib.load("case", "open a.重大\n")
        .expect("a case file may reference a loaded module");
    assert_eq!(lib.env.open_predicates(), vec![name("a.重大")]);
}

#[test]
fn a_module_open_reference_must_be_fully_qualified() {
    let error = load_err("namespace a\nsort a.人\npred a.重大 : a.人 → Prop\nopen 重大\n");
    let msg = error.to_string();
    assert!(msg.contains("`open 重大`"), "{msg}");
    assert!(msg.contains("未限定"), "{msg}");
}

/// The marker is inert: it declares no proposition, so no derivation can cite
/// it. The environment method is the only reader needed by the declaration
/// layer.
#[test]
fn an_open_declaration_is_metadata_not_a_proposition() {
    let lib = load("sort 人\npred 重大 : 人 → Prop\nopen 重大\n").expect("loads");
    let marker = lib.env.get("open:重大").expect("the marker");
    // `Sort 1` is `Type`: the marker is metadata, not a proposition, so the
    // kernel can never treat it as an asserted claim.
    assert_eq!(marker.ty, Expr::Sort(1));
    assert!(marker.sources.is_empty());
    assert!(matches!(marker.kind, DeclKind::OpenConcept { .. }));
}

#[test]
fn a_repeated_unknown_target_reports_the_unknown_predicate_not_a_duplicate() {
    // Target validation runs before duplicate detection, so the first fix a
    // reader must make is the one that actually explains the failure.
    let error = load_err("pred 已知 : Prop\nopen 不存在\nopen 不存在\n");
    let message = error.to_string();
    assert!(message.contains("未知谓词"), "{message}");
    assert!(!message.contains("重复"), "{message}");
}
