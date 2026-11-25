//! The declaration layer for burden of proof and standards of proof.
//!
//! `burden` / `standard` describe who must prove a rule's positive
//! requirements; `exception_burden` / `exception_standard` do the same for the
//! rule's `unless` clauses. All four are optional metadata: an omitted clause
//! stays `None`, it is never defaulted to the claimant or to the preponderance
//! standard, and it takes no part in reasoning (that is asserted end to end in
//! `crates/cli/tests/burden.rs`).

use std_deduce_kernel::{Burden, DeclKind, Standard};
use std_deduce_lang::ast::Item;
use std_deduce_lang::parser::{parse, ParseError};
use std_deduce_lang::Library;

/// A well-typed rule whose body can be extended with the clauses under test.
/// The last line of `PREFIX` is the rule's `conclude`, so appended clauses are
/// part of the same rule block.
const PREFIX: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 免责 : 公民 → Prop
obj 张三 : 公民
rule 规则 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
"#;

const SOURCE_LINE: &str = "  source text \"测试\" locator \"一\"\n";

fn source_with(extra: &str) -> String {
    format!("{PREFIX}{SOURCE_LINE}{extra}")
}

fn rule_item(extra: &str) -> Item {
    let mut items = parse(&source_with(extra)).expect("the rule must parse");
    items.pop().expect("the program is not empty")
}

fn parse_error(extra: &str) -> ParseError {
    parse(&source_with(extra)).expect_err("the clause must be rejected")
}

type Pleading = (
    Option<Burden>,
    Option<Standard>,
    Option<Burden>,
    Option<Standard>,
);

fn pleading(item: Item) -> Pleading {
    let Item::Rule {
        burden,
        standard,
        exception_burden,
        exception_standard,
        ..
    } = item
    else {
        panic!("the last item must be the rule");
    };
    (burden, standard, exception_burden, exception_standard)
}

/// The four fields of the rule declaration in the loaded ledger.
fn loaded_pleading(lib: &Library) -> Pleading {
    let decl = lib.env.get("规则").expect("the rule must be in the ledger");
    let DeclKind::Rule(rule) = &decl.kind else {
        panic!("`规则` must be a rule");
    };
    (
        rule.burden,
        rule.standard,
        rule.exception_burden,
        rule.exception_standard,
    )
}

#[test]
fn each_burden_value_parses() {
    for (written, expected) in [
        ("claimant", Burden::Claimant),
        ("respondent", Burden::Respondent),
        ("court", Burden::Court),
    ] {
        let (burden, standard, exception_burden, exception_standard) =
            pleading(rule_item(&format!("  burden {written}\n")));
        assert_eq!(burden, Some(expected), "burden {written}");
        assert_eq!(standard, None);
        assert_eq!(exception_burden, None);
        assert_eq!(exception_standard, None);
    }
}

#[test]
fn each_standard_value_parses() {
    for (written, expected) in [
        ("preponderance", Standard::Preponderance),
        ("clear_and_convincing", Standard::ClearAndConvincing),
        ("beyond_reasonable_doubt", Standard::BeyondReasonableDoubt),
    ] {
        let (burden, standard, exception_burden, exception_standard) =
            pleading(rule_item(&format!("  standard {written}\n")));
        assert_eq!(standard, Some(expected), "standard {written}");
        assert_eq!(burden, None);
        assert_eq!(exception_burden, None);
        assert_eq!(exception_standard, None);
    }
}

#[test]
fn each_exception_burden_value_parses() {
    for (written, expected) in [
        ("claimant", Burden::Claimant),
        ("respondent", Burden::Respondent),
        ("court", Burden::Court),
    ] {
        let (burden, standard, exception_burden, exception_standard) =
            pleading(rule_item(&format!("  exception_burden {written}\n")));
        assert_eq!(
            exception_burden,
            Some(expected),
            "exception_burden {written}"
        );
        assert_eq!(burden, None);
        assert_eq!(standard, None);
        assert_eq!(exception_standard, None);
    }
}

#[test]
fn each_exception_standard_value_parses() {
    for (written, expected) in [
        ("preponderance", Standard::Preponderance),
        ("clear_and_convincing", Standard::ClearAndConvincing),
        ("beyond_reasonable_doubt", Standard::BeyondReasonableDoubt),
    ] {
        let (burden, standard, exception_burden, exception_standard) =
            pleading(rule_item(&format!("  exception_standard {written}\n")));
        assert_eq!(
            exception_standard,
            Some(expected),
            "exception_standard {written}"
        );
        assert_eq!(burden, None);
        assert_eq!(standard, None);
        assert_eq!(exception_burden, None);
    }
}

#[test]
fn all_four_clauses_parse_together_in_any_order() {
    let (burden, standard, exception_burden, exception_standard) = pleading(rule_item(concat!(
        "  exception_standard clear_and_convincing\n",
        "  standard beyond_reasonable_doubt\n",
        "  burden court\n",
        "  exception_burden respondent\n",
    )));
    assert_eq!(burden, Some(Burden::Court));
    assert_eq!(standard, Some(Standard::BeyondReasonableDoubt));
    assert_eq!(exception_burden, Some(Burden::Respondent));
    assert_eq!(exception_standard, Some(Standard::ClearAndConvincing));
}

#[test]
fn omitted_clauses_stay_none() {
    assert_eq!(pleading(rule_item("")), (None, None, None, None));
}

#[test]
fn the_loader_carries_the_declared_pleading_into_the_rule() {
    let mut lib = Library::new();
    lib.load(
        "test.std",
        &source_with(concat!(
            "  burden respondent\n",
            "  standard clear_and_convincing\n",
            "  unless 免责 p\n",
            "  exception_burden claimant\n",
            "  exception_standard beyond_reasonable_doubt\n",
        )),
    )
    .expect("the declared rule must load");
    assert_eq!(
        loaded_pleading(&lib),
        (
            Some(Burden::Respondent),
            Some(Standard::ClearAndConvincing),
            Some(Burden::Claimant),
            Some(Standard::BeyondReasonableDoubt),
        )
    );
}

#[test]
fn the_loader_keeps_undeclared_pleading_as_none() {
    let mut lib = Library::new();
    lib.load("test.std", &source_with(""))
        .expect("a rule without pleading clauses must load");
    assert_eq!(loaded_pleading(&lib), (None, None, None, None));
}

#[test]
fn an_unknown_burden_value_is_rejected_with_the_allowed_set() {
    for field in ["burden", "exception_burden"] {
        let error = parse_error(&format!("  {field} plaintiff\n"));
        let message = error.msg;
        assert!(
            message.contains("规则 `规则`"),
            "the error must name the rule: {message}"
        );
        assert!(
            message.contains(field),
            "the error must name the field `{field}`: {message}"
        );
        assert!(
            message.contains("`plaintiff`"),
            "the error must quote the rejected value: {message}"
        );
        for allowed in ["claimant", "respondent", "court"] {
            assert!(
                message.contains(allowed),
                "the error must list `{allowed}`: {message}"
            );
        }
    }
}

#[test]
fn an_unknown_standard_value_is_rejected_with_the_allowed_set() {
    for field in ["standard", "exception_standard"] {
        let error = parse_error(&format!("  {field} probable\n"));
        let message = error.msg;
        assert!(
            message.contains("规则 `规则`"),
            "the error must name the rule: {message}"
        );
        assert!(
            message.contains(field),
            "the error must name the field `{field}`: {message}"
        );
        assert!(
            message.contains("`probable`"),
            "the error must quote the rejected value: {message}"
        );
        for allowed in [
            "preponderance",
            "clear_and_convincing",
            "beyond_reasonable_doubt",
        ] {
            assert!(
                message.contains(allowed),
                "the error must list `{allowed}`: {message}"
            );
        }
    }
}

#[test]
fn a_missing_value_is_rejected_with_the_field_and_allowed_set() {
    for (field, allowed) in [
        ("burden", ["claimant", "respondent", "court"].as_slice()),
        ("standard", ["preponderance"].as_slice()),
        ("exception_burden", ["claimant"].as_slice()),
        ("exception_standard", ["preponderance"].as_slice()),
    ] {
        let error = parse_error(&format!("  {field}\n"));
        let message = error.msg;
        assert!(
            message.contains("规则 `规则`") && message.contains(field),
            "the error must name the rule and the field `{field}`: {message}"
        );
        assert!(
            message.contains("缺少取值"),
            "the error must say the value is missing: {message}"
        );
        for name in allowed {
            assert!(
                message.contains(name),
                "the error must list `{name}`: {message}"
            );
        }
    }
}

#[test]
fn a_repeated_clause_is_rejected_at_its_own_keyword() {
    for (field, value) in [
        ("burden", "claimant"),
        ("standard", "preponderance"),
        ("exception_burden", "respondent"),
        ("exception_standard", "clear_and_convincing"),
    ] {
        // Both lines are at the same indentation, so the duplicate error must
        // point at the second clause's keyword: line 13, column 3.
        let error = parse_error(&format!("  {field} {value}\n  {field} {value}\n"));
        assert!(
            error.msg.contains("重复") && error.msg.contains(field),
            "the error must say `{field}` is repeated: {}",
            error.msg
        );
        assert!(
            error.msg.contains("规则 `规则`"),
            "the error must name the rule: {}",
            error.msg
        );
        assert_eq!(
            (error.line, error.col),
            (13, 3),
            "the duplicate must be reported at the second `{field}`: {error}"
        );
    }
}

#[test]
fn exception_clauses_without_any_unless_are_rejected_at_load() {
    for extra in [
        "  exception_burden respondent\n",
        "  exception_standard clear_and_convincing\n",
    ] {
        let error = Library::new()
            .load("test.std", &source_with(extra))
            .expect_err("an exception clause without an exception must be refused")
            .to_string();
        assert!(
            error.contains("`rule 规则`") && error.contains("unless"),
            "the error must name the rule and the missing exception: {error}"
        );
    }
}

#[test]
fn exception_clauses_load_when_the_rule_has_unless() {
    let mut lib = Library::new();
    lib.load(
        "test.std",
        &source_with("  unless 免责 p\n  exception_burden respondent\n"),
    )
    .expect("an exception clause on a rule with `unless` must load");
    assert_eq!(loaded_pleading(&lib).2, Some(Burden::Respondent));
}
