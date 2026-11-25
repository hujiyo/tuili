//! Reasoner-level applicability integration: an inapplicable rule never fires,
//! its candidate stays visible in a gap, and unchecked/undecidable rules keep
//! their old firing behaviour while the verdict is recorded.

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
            reason: InapplicableReason::NotYetInForce { day, .. },
        } => assert_eq!(day, "2019-05-01"),
        other => panic!("expected a not-yet-in-force exclusion, got {other:?}"),
    }

    // The scan records the skipped rule instead of looking complete.
    let scan = r.issues();
    assert!(
        scan.inapplicable
            .iter()
            .any(|rule| rule.as_ref() == "二〇二一年规则"),
        "{:?}",
        scan.inapplicable
    );

    let verdicts = r.rule_applicability();
    let verdict = verdicts
        .iter()
        .find(|(rule, _)| rule.as_ref() == "二〇二一年规则")
        .map(|(_, verdict)| verdict)
        .expect("every rule is judged");
    assert!(!verdict.allows_firing());
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
    assert_eq!(
        verdict,
        Applicability::Unchecked {
            missing: MissingInput::RuleHasNoScope
        }
    );
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
fn moving_the_asof_date_moves_the_verdict_and_the_conclusion() {
    let lib = load(NO_OCCURRENCE_RULE);
    let target = goal("结论", "甲");

    // No date to compare: unchecked, old behaviour.
    let plain = reasoner(&lib, None, None);
    assert!(plain.knows(&target));
    assert_eq!(
        plain
            .rule_applicability()
            .into_iter()
            .find(|(rule, _)| rule.as_ref() == "二〇二一年规则")
            .map(|(_, verdict)| verdict),
        Some(Applicability::Unchecked {
            missing: MissingInput::NoCaseDate
        })
    );

    // Before the rule starts: inapplicable, no conclusion.
    let before = reasoner(&lib, Some("2019-06-01"), None);
    assert!(!before.knows(&target));
    let tree = before.gap_tree(&target);
    assert!(matches!(
        tree.candidates[0].applicability,
        Applicability::Inapplicable {
            reason: InapplicableReason::NotYetInForce { .. }
        }
    ));

    // Inside the range: applicable, no warning state.
    let inside = reasoner(&lib, Some("2022-01-01"), None);
    assert!(inside.knows(&target));
    assert_eq!(
        inside
            .rule_applicability()
            .into_iter()
            .find(|(rule, _)| rule.as_ref() == "二〇二一年规则")
            .map(|(_, verdict)| verdict),
        Some(Applicability::Applicable)
    );
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
    let verdict = r
        .rule_applicability()
        .into_iter()
        .find(|(rule, _)| rule.as_ref() == "北京规则")
        .map(|(_, verdict)| verdict)
        .expect("every rule is judged");
    assert_eq!(
        verdict,
        Applicability::Inapplicable {
            reason: InapplicableReason::TerritoryMismatch {
                rule: "CN-BJ".into(),
                case: "CN-HN".into(),
            }
        }
    );
}
