//! Reasoner-level applicability integration: an inapplicable rule never fires,
//! its candidate stays visible in a gap, an event time is the reference point
//! even at a later as-of date, and unchecked/undecidable rules keep their old
//! firing behaviour while the verdict is recorded.

use std_deduce_kernel::Expr;
use std_deduce_lang::Library;
use std_deduce_reason::{Applicability, InapplicableReason, MissingInput, Reasoner};

fn load(src: &str) -> Library {
    let mut lib = Library::new();
    lib.load("test", src)
        .unwrap_or_else(|e| panic!("load: {e}"));
    lib
}

fn reasoner<'a>(lib: &'a Library, as_of: Option<&str>, jurisdiction: Option<&str>) -> Reasoner<'a> {
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.set_session_scope(as_of, jurisdiction);
    r.saturate().unwrap();
    r
}

fn goal(head: &str, arg: &str) -> Expr {
    Expr::apps(Expr::constant(head), [Expr::constant(arg)])
}

const LATE_RULE: &str = r#"
sort 人
pred 起算 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 事实 : 起算 甲
  source text "案件材料" locator "第一页"
  occurred_at 2019-05-01
rule 二〇二一年规则 :
  params x : 人
  premise 起算 x
  conclude 结论 x
  effective 2021-01-01
  source text "测试法" locator "第一条"
"#;

#[test]
fn an_inapplicable_rule_never_fires_and_the_gap_still_lists_it() {
    let lib = load(LATE_RULE);
    let r = reasoner(&lib, None, None);
    let target = goal("结论", "甲");
    assert!(!r.knows(&target), "an inapplicable rule must not conclude");

    let tree = r.gap_tree(&target);
    let candidate = tree
        .candidates
        .iter()
        .find(|candidate| candidate.rule.as_ref() == "二〇二一年规则")
        .expect("the excluded rule is still a candidate");
    match &candidate.applicability {
        Applicability::Inapplicable {
            reason: InapplicableReason::NotYetInForce { dates, .. },
            basis,
        } => {
            assert_eq!(dates, &["2019-05-01"]);
            assert_eq!(basis.dates.len(), 1);
            assert!(!basis.dates[0].covered);
        }
        other => panic!("expected a not-yet-in-force exclusion, got {other:?}"),
    }
}

const OLD_RULE: &str = r#"
sort 人
pred 起算 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 合同 : 起算 甲
  source text "合同" locator "第一条"
  occurred_at 2019-05-01
rule 旧法 :
  params x : 人
  premise 起算 x
  conclude 结论 x
  effective 1999-01-01
  repealed 2021-01-01
  source text "旧法" locator "第一条"
"#;

#[test]
fn an_old_rule_governs_an_old_event_even_at_a_later_asof() {
    let lib = load(OLD_RULE);
    let target = goal("结论", "甲");
    let r = reasoner(&lib, Some("2026-01-01"), None);
    assert!(
        r.knows(&target),
        "the event time decides, not the query date"
    );
    let d = r.derivation_for(&target).expect("a derivation");
    let root = d.root.expect("a root");
    let std_deduce_reason::Node::RuleApplication { applicability, .. } = &d.nodes[root] else {
        panic!("the root is a rule application");
    };
    let Applicability::Applicable { basis } = applicability else {
        panic!("expected applicable, got {applicability:?}");
    };
    assert_eq!(basis.dates.len(), 1);
    assert_eq!(basis.dates[0].date, "2019-05-01");
    assert!(!basis.dates[0].query_date_fallback);
}

const UNSCOPED_RULE: &str = r#"
sort 人
pred 起算 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 事实 : 起算 甲
  source text "案件材料" locator "第一页"
rule 规则 :
  params x : 人
  premise 起算 x
  conclude 结论 x
  source text "测试法" locator "第一条"
"#;

#[test]
fn an_unscoped_rule_fires_but_is_recorded_as_unchecked() {
    let lib = load(UNSCOPED_RULE);
    let r = reasoner(&lib, None, None);
    let target = goal("结论", "甲");
    assert!(r.knows(&target), "an unchecked rule keeps firing");
    let verdict = r
        .rule_applicability()
        .into_iter()
        .find(|(rule, _)| rule.as_ref() == "规则")
        .map(|(_, verdict)| verdict)
        .expect("every rule is judged");
    assert!(matches!(
        verdict,
        Applicability::Unchecked {
            missing: MissingInput::RuleHasNoScope,
            ..
        }
    ));
    assert!(verdict.allows_firing());
}

const NO_OCCURRENCE_RULE: &str = r#"
sort 人
pred 起算 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 事实 : 起算 甲
  source text "案件材料" locator "第一页"
rule 二〇二一年规则 :
  params x : 人
  premise 起算 x
  conclude 结论 x
  effective 2021-01-01
  source text "测试法" locator "第一条"
"#;

#[test]
fn moving_the_asof_date_moves_the_fallback_verdict() {
    let lib = load(NO_OCCURRENCE_RULE);
    let target = goal("结论", "甲");

    // No event time and no as-of: unchecked, old firing behaviour.
    let plain = reasoner(&lib, None, None);
    assert!(plain.knows(&target));
    let verdict = plain
        .rule_applicability()
        .into_iter()
        .find(|(rule, _)| rule.as_ref() == "二〇二一年规则")
        .map(|(_, verdict)| verdict);
    assert!(matches!(
        verdict,
        Some(Applicability::Unchecked {
            missing: MissingInput::NoCaseDate,
            ..
        })
    ));

    // Before the rule starts: the fallback date is outside, inapplicable.
    let before = reasoner(&lib, Some("2019-06-01"), None);
    assert!(!before.knows(&target));
    let tree = before.gap_tree(&target);
    assert!(matches!(
        tree.candidates[0].applicability,
        Applicability::Inapplicable {
            reason: InapplicableReason::NotYetInForce { .. },
            ..
        }
    ));

    // Inside the range: applicable, with the as-of fallback recorded.
    let inside = reasoner(&lib, Some("2022-01-01"), None);
    assert!(inside.knows(&target));
    let verdict = inside
        .rule_applicability()
        .into_iter()
        .find(|(rule, _)| rule.as_ref() == "二〇二一年规则")
        .map(|(_, verdict)| verdict);
    let Applicability::Applicable { basis } = verdict.expect("a verdict") else {
        panic!("expected applicable");
    };
    assert!(basis.dates[0].query_date_fallback);
    assert_eq!(basis.dates[0].date, "2022-01-01");
}

const TERRITORY_RULE: &str = r#"
sort 人
pred 行为 : 人 → Prop
pred 北京规则适用 : 人 → Prop
obj 甲 : 人
axiom 事实 : 行为 甲
  source text "案件材料" locator "第一页"
  occurred_in CN-HN
rule 北京规则 :
  params x : 人
  premise 行为 x
  conclude 北京规则适用 x
  jurisdiction CN
  territory CN-BJ
  source text "北京市条例" locator "第一条"
"#;

#[test]
fn a_territory_mismatch_excludes_the_rule() {
    let lib = load(TERRITORY_RULE);
    let r = reasoner(&lib, None, Some("CN"));
    let target = goal("北京规则适用", "甲");
    assert!(!r.knows(&target));
    let tree = r.gap_tree(&target);
    assert!(matches!(
        tree.candidates[0].applicability,
        Applicability::Inapplicable {
            reason: InapplicableReason::TerritoryMismatch { ref places, .. },
            ..
        } if places == &["CN-HN"]
    ));
}
