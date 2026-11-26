//! Certificate-layer tests for the version 7 applicability records.
//!
//! These tests build certificates by hand against a loaded environment and
//! call `cert::check` directly. They pin the checker's own contract: a
//! recomputed verdict, basis or reason that differs from the record is
//! rejected, a premise proved by a derived conclusion still reads the
//! environment's occurrence for its proposition, and a gap candidate's held
//! premises are reconstructed from its bindings rather than trusted.

use std_deduce_cert::{
    check, judge_applicability, ApplicabilityAnchor, ApplicabilityVerdict, Assumption, Binding,
    CertExpr, Certificate, EnvironmentIdentity, EnvironmentRecord, Explicit, ExplicitText,
    FactIdentity, GapCandidate, Metadata, Node, RuleApplicability,
};
use std_deduce_kernel::{name, Env};
use std_deduce_lang::Library;

const EVENT_TIME_ENV: &str = r#"
sort 人
pred 行为 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 事实 : 行为 甲
  source text "材料" locator "一"
  occurred_at 2019-05-01
  occurred_in CN-HN
rule 规则 :
  params x : 人
  premise 行为 x
  conclude 结论 x
  effective 1999-01-01
  repealed 2021-01-01
  jurisdiction CN
  territory CN-HN
  source text "旧法" locator "第一条"
"#;

const NO_EVENT_TIME_ENV: &str = r#"
sort 人
pred 行为 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 事实 : 行为 甲
  source text "材料" locator "一"
rule 规则 :
  params x : 人
  premise 行为 x
  conclude 结论 x
  effective 2021-01-01
  source text "新法" locator "第一条"
"#;

/// A fact registered with an occurrence, a rule deriving the same proposition
/// from another fact, and a scoped rule consuming it.
const DERIVED_PREMISE_ENV: &str = r#"
sort 人
pred 其他 : 人 → Prop
pred 行为 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 其他事实 : 其他 甲
  source text "材料" locator "一"
axiom 行为登记 : 行为 甲
  source text "材料" locator "二"
  occurred_at 2019-05-01
rule 派生行为 :
  params x : 人
  premise 其他 x
  conclude 行为 x
  source text "派生法" locator "第一条"
rule 后规 :
  params x : 人
  premise 行为 x
  conclude 结论 x
  effective 2021-01-01
  source text "新法" locator "第一条"
"#;

/// The same environment without registering `行为 甲`; the derivation still
/// proves it, but no occurrence exists for its proposition.
const PURE_DERIVED_ENV: &str = r#"
sort 人
pred 其他 : 人 → Prop
pred 行为 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 其他事实 : 其他 甲
  source text "材料" locator "一"
rule 派生行为 :
  params x : 人
  premise 其他 x
  conclude 行为 x
  source text "派生法" locator "第一条"
rule 后规 :
  params x : 人
  premise 行为 x
  conclude 结论 x
  effective 2021-01-01
  source text "新法" locator "第一条"
"#;

const CANDIDATE_ENV: &str = r#"
sort 人
pred 行为 : 人 → Prop
pred 结论 : 人 → Prop
pred 别的 : 人 → Prop
obj 甲 : 人
axiom 行为事实 : 行为 甲
  source text "材料" locator "一"
  occurred_at 2019-05-01
axiom 无关事实 : 别的 甲
  source text "材料" locator "二"
  occurred_at 2023-01-01
rule 后规 :
  params x : 人
  premise 行为 x
  conclude 结论 x
  effective 2021-01-01
  source text "新法" locator "第一条"
"#;

fn env_from(src: &str) -> Env {
    let mut library = Library::new();
    library
        .load("cert-applicability", src)
        .expect("test theory loads");
    library.env
}

fn recorded_identity(as_of: Option<&str>, jurisdiction: Option<&str>) -> EnvironmentIdentity {
    let mut record = EnvironmentRecord::empty();
    record.as_of = ExplicitText::from(as_of.map(ToOwned::to_owned));
    record.jurisdiction = ExplicitText::from(jurisdiction.map(ToOwned::to_owned));
    EnvironmentIdentity::Recorded(record)
}

fn atom(predicate: &str, object: &str) -> CertExpr {
    CertExpr::App {
        func: Box::new(CertExpr::Const {
            name: predicate.to_owned(),
        }),
        arg: Box::new(CertExpr::Const {
            name: object.to_owned(),
        }),
    }
}

fn constant(text: &str) -> CertExpr {
    CertExpr::Const {
        name: text.to_owned(),
    }
}

fn assumption(
    proposition: CertExpr,
    occurred_at: Explicit<String>,
    occurred_in: Explicit<String>,
) -> Assumption {
    Assumption {
        proposition,
        identity: FactIdentity::UserAsserted,
        sources: Vec::new(),
        label: None,
        occurred_at,
        occurred_in,
    }
}

fn binding(parameter: &str, value: CertExpr) -> Binding {
    Binding {
        parameter: parameter.to_owned(),
        value,
    }
}

fn recorded(env: &Env, rule: &str, anchor: &ApplicabilityAnchor) -> RuleApplicability {
    let declaration = env.get(&name(rule)).expect("the rule exists");
    judge_applicability(&declaration.scope, anchor)
}

fn rule_node(
    rule: &str,
    conclusion: CertExpr,
    premises: Vec<usize>,
    bindings: Vec<Binding>,
    applicability: RuleApplicability,
) -> Node {
    Node::RuleApplication {
        rule: rule.to_owned(),
        conclusion,
        premises,
        bindings,
        sources: Vec::new(),
        applicability: Box::new(applicability),
    }
}

fn certificate(
    environment: EnvironmentIdentity,
    assumptions: Vec<Assumption>,
    nodes: Vec<Node>,
    root: Option<usize>,
) -> Certificate {
    Certificate {
        format_version: std_deduce_cert::FormatVersion::CURRENT,
        environment,
        assumptions,
        interpretations: Vec::new(),
        nodes,
        root,
        alternatives: Vec::new(),
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Metadata::default(),
    }
}

/// The event-time certificate: one registered fact and one applicable rule
/// step, with the session jurisdiction recorded in the environment identity.
fn event_time_certificate(env: &Env) -> Certificate {
    let anchor = ApplicabilityAnchor {
        as_of: None,
        jurisdiction: Some("CN".to_owned()),
        event_dates: vec!["2019-05-01".to_owned()],
        event_places: vec!["CN-HN".to_owned()],
        ..ApplicabilityAnchor::default()
    };
    certificate(
        recorded_identity(None, Some("CN")),
        vec![assumption(
            atom("行为", "甲"),
            Explicit::some("2019-05-01".to_owned()),
            Explicit::some("CN-HN".to_owned()),
        )],
        vec![
            Node::Assumption { assumption: 0 },
            rule_node(
                "规则",
                atom("结论", "甲"),
                vec![0],
                vec![binding("x", constant("甲"))],
                recorded(env, "规则", &anchor),
            ),
        ],
        Some(1),
    )
}

fn reject(cert: &Certificate, env: &Env) -> std_deduce_cert::CheckError {
    check(env, cert).expect_err("the certificate must be rejected")
}

fn assert_rejected_at(cert: &Certificate, env: &Env, needle: &str) -> std_deduce_cert::CheckError {
    let error = reject(cert, env);
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains(needle), "{error}");
    error
}

#[test]
fn a_valid_event_time_record_passes() {
    let env = env_from(EVENT_TIME_ENV);
    let certificate = event_time_certificate(&env);
    let report = check(&env, &certificate).expect("the valid applicability record passes");
    assert!(report.root_proved);
}

#[test]
fn a_flipped_verdict_is_rejected() {
    let env = env_from(EVENT_TIME_ENV);
    let mut certificate = event_time_certificate(&env);
    let Node::RuleApplication { applicability, .. } = &mut certificate.nodes[1] else {
        panic!("node 1 is a rule application");
    };
    applicability.verdict = ApplicabilityVerdict::Unchecked;
    let error = assert_rejected_at(&certificate, &env, "适用性记录");
    assert!(error.message.contains("unchecked"), "{error}");
    assert!(error.message.contains("applicable"), "{error}");
}

#[test]
fn a_changed_basis_date_is_rejected() {
    let env = env_from(EVENT_TIME_ENV);
    let mut certificate = event_time_certificate(&env);
    let Node::RuleApplication { applicability, .. } = &mut certificate.nodes[1] else {
        panic!("node 1 is a rule application");
    };
    applicability.basis.dates[0].date = "2019-05-02".to_owned();
    let error = assert_rejected_at(&certificate, &env, "dates[0].date");
    assert!(error.message.contains("2019-05-02"), "{error}");
}

#[test]
fn a_changed_scope_text_is_rejected() {
    let env = env_from(EVENT_TIME_ENV);
    let mut certificate = event_time_certificate(&env);
    let Node::RuleApplication { applicability, .. } = &mut certificate.nodes[1] else {
        panic!("node 1 is a rule application");
    };
    applicability.basis.scope.effective_from = Explicit::some("2000-01-01".to_owned());
    let error = assert_rejected_at(&certificate, &env, "effective_from");
    assert!(error.message.contains("规则范围"), "{error}");
}

#[test]
fn a_changed_fallback_date_is_rejected() {
    let env = env_from(NO_EVENT_TIME_ENV);
    let anchor = ApplicabilityAnchor {
        as_of: Some("2022-01-01".to_owned()),
        missing_event_date: true,
        missing_event_place: true,
        ..ApplicabilityAnchor::default()
    };
    let mut certificate = certificate(
        recorded_identity(Some("2022-01-01"), None),
        vec![assumption(
            atom("行为", "甲"),
            Explicit::none(),
            Explicit::none(),
        )],
        vec![
            Node::Assumption { assumption: 0 },
            rule_node(
                "规则",
                atom("结论", "甲"),
                vec![0],
                vec![binding("x", constant("甲"))],
                recorded(&env, "规则", &anchor),
            ),
        ],
        Some(1),
    );
    check(&env, &certificate).expect("the fallback record passes as declared");
    let Node::RuleApplication { applicability, .. } = &mut certificate.nodes[1] else {
        panic!("node 1 is a rule application");
    };
    applicability.basis.dates[0].date = "2022-02-02".to_owned();
    applicability.basis.session.as_of = Explicit::some("2022-02-02".to_owned());
    let error = reject(&certificate, &env);
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("as_of"), "{error}");
}

#[test]
fn an_unchecked_verdict_cannot_be_flipped_to_applicable() {
    let env = env_from(EVENT_TIME_ENV);
    let mut certificate = event_time_certificate(&env);
    // The same instance without a session jurisdiction: the date and place
    // are present, but the rule's jurisdiction cannot be compared.
    let anchor = ApplicabilityAnchor {
        event_dates: vec!["2019-05-01".to_owned()],
        event_places: vec!["CN-HN".to_owned()],
        ..ApplicabilityAnchor::default()
    };
    let unchecked = recorded(&env, "规则", &anchor);
    assert_eq!(unchecked.verdict, ApplicabilityVerdict::Unchecked);
    certificate.environment = recorded_identity(None, None);
    let Node::RuleApplication { applicability, .. } = &mut certificate.nodes[1] else {
        panic!("node 1 is a rule application");
    };
    **applicability = unchecked;
    check(&env, &certificate).expect("the unchecked record is self-consistent");
    let Node::RuleApplication { applicability, .. } = &mut certificate.nodes[1] else {
        panic!("node 1 is a rule application");
    };
    applicability.verdict = ApplicabilityVerdict::Applicable;
    applicability.reason = Explicit::none();
    let error = assert_rejected_at(&certificate, &env, "适用性记录");
    assert!(error.message.contains("unchecked"), "{error}");
    assert!(error.message.contains("applicable"), "{error}");
}

#[test]
fn an_assumption_occurrence_date_must_match_the_environment() {
    let env = env_from(EVENT_TIME_ENV);
    let certificate = certificate(
        recorded_identity(None, None),
        vec![assumption(
            atom("行为", "甲"),
            Explicit::some("2019-05-01".to_owned()),
            Explicit::some("CN-HN".to_owned()),
        )],
        vec![Node::Assumption { assumption: 0 }],
        Some(0),
    );
    check(&env, &certificate).expect("the matching occurrence passes");
    let mut certificate = certificate;
    certificate.assumptions[0].occurred_at = Explicit::some("2019-05-02".to_owned());
    let error = reject(&certificate, &env);
    assert!(
        error.message.contains("事件时间") && error.message.contains("2019-05-02"),
        "{error}"
    );
}

#[test]
fn an_assumption_occurrence_place_must_match_the_environment() {
    let env = env_from(EVENT_TIME_ENV);
    let mut certificate = certificate(
        recorded_identity(None, None),
        vec![assumption(
            atom("行为", "甲"),
            Explicit::some("2019-05-01".to_owned()),
            Explicit::some("CN-HN".to_owned()),
        )],
        vec![Node::Assumption { assumption: 0 }],
        Some(0),
    );
    certificate.assumptions[0].occurred_in = Explicit::some("CN-BJ".to_owned());
    let error = reject(&certificate, &env);
    assert!(
        error.message.contains("事件时间/地点") && error.message.contains("CN-BJ"),
        "{error}"
    );
}

#[test]
fn an_assumption_null_occurrence_cannot_drop_a_registered_date() {
    let env = env_from(EVENT_TIME_ENV);
    let mut certificate = certificate(
        recorded_identity(None, None),
        vec![assumption(
            atom("行为", "甲"),
            Explicit::some("2019-05-01".to_owned()),
            Explicit::some("CN-HN".to_owned()),
        )],
        vec![Node::Assumption { assumption: 0 }],
        Some(0),
    );
    certificate.assumptions[0].occurred_at = Explicit::none();
    let error = reject(&certificate, &env);
    assert!(error.message.contains("不一致"), "{error}");
}

/// The P0 channel: a rule step whose premise is proved by a derived
/// conclusion must still read the occurrence the environment registers for
/// that premise proposition.
#[test]
fn a_derived_premise_still_reads_the_registered_occurrence() {
    let env = env_from(DERIVED_PREMISE_ENV);
    let certificate = derived_premise_certificate(&env, true);
    let error = reject(&certificate, &env);
    assert_eq!(error.node, Some(2), "{error}");
    assert!(error.message.contains("适用性记录"), "{error}");
    assert!(error.message.contains("inapplicable"), "{error}");
}

/// The same shape without any registration for `行为 甲`: no occurrence
/// exists, so an unchecked no-case-date record is correct and passes. The
/// checker must not silently become stricter than the reasoner.
#[test]
fn a_pure_derived_premise_without_a_registered_fact_stays_unchecked() {
    let env = env_from(PURE_DERIVED_ENV);
    let certificate = derived_premise_certificate(&env, false);
    let report = check(&env, &certificate).expect("an unregistered premise is missing input");
    assert!(report.root_proved);
}

/// Build the derived-premise certificate. `registered` selects whether the
/// environment registers `行为 甲` with an occurrence (the env itself supplies
/// that fact); the certificate never lists it as an assumption.
fn derived_premise_certificate(env: &Env, _registered: bool) -> Certificate {
    // The record is the same in both environments: the premise proposition
    // `行为 甲` has no event input (the checker used to stop here at the
    // premise node's kind). Only the environment decides whether the
    // registered occurrence makes the recomputation disagree.
    let no_input = ApplicabilityAnchor {
        missing_event_date: true,
        missing_event_place: true,
        ..ApplicabilityAnchor::default()
    };
    let unscoped = recorded(env, "派生行为", &no_input);
    let after_rule = recorded(env, "后规", &no_input);
    certificate(
        recorded_identity(None, None),
        vec![assumption(
            atom("其他", "甲"),
            Explicit::none(),
            Explicit::none(),
        )],
        vec![
            Node::Assumption { assumption: 0 },
            rule_node(
                "派生行为",
                atom("行为", "甲"),
                vec![0],
                vec![binding("x", constant("甲"))],
                unscoped,
            ),
            rule_node(
                "后规",
                atom("结论", "甲"),
                vec![1],
                vec![binding("x", constant("甲"))],
                after_rule,
            ),
        ],
        Some(2),
    )
}

fn candidate_record(env: &Env, event_dates: &[&str]) -> RuleApplicability {
    let anchor = ApplicabilityAnchor {
        event_dates: event_dates.iter().map(|date| (*date).to_owned()).collect(),
        // The registered held fact records an occurrence date but no place.
        missing_event_place: true,
        ..ApplicabilityAnchor::default()
    };
    recorded(env, "后规", &anchor)
}

fn gap_candidate_certificate(held: Vec<CertExpr>, applicability: RuleApplicability) -> Certificate {
    certificate(
        recorded_identity(None, None),
        Vec::new(),
        vec![Node::Gap {
            proposition: atom("结论", "甲"),
            axiom_candidates: Vec::new(),
            candidates: vec![GapCandidate {
                rule: "后规".to_owned(),
                bindings: vec![binding("x", constant("甲"))],
                held,
                missing: Vec::new(),
                blocked_by: Vec::new(),
                sources: Vec::new(),
                applicability,
            }],
            note: None,
        }],
        Some(0),
    )
}

#[test]
fn a_valid_gap_candidate_recomputes_from_its_held_premises() {
    let env = env_from(CANDIDATE_ENV);
    let held = vec![atom("行为", "甲")];
    let applicability = candidate_record(&env, &["2019-05-01"]);
    let certificate = gap_candidate_certificate(held, applicability);
    let report = check(&env, &certificate).expect("the candidate record recomputes");
    assert!(!report.root_proved);
}

#[test]
fn a_forged_candidate_verdict_is_rejected() {
    let env = env_from(CANDIDATE_ENV);
    let held = vec![atom("行为", "甲")];
    let mut applicability = candidate_record(&env, &["2019-05-01"]);
    applicability.verdict = ApplicabilityVerdict::Applicable;
    applicability.reason = Explicit::none();
    applicability.basis.dates[0].date = "2023-01-01".to_owned();
    applicability.basis.dates[0].covered = true;
    let certificate = gap_candidate_certificate(held, applicability);
    let error = reject(&certificate, &env);
    assert_eq!(error.node, Some(0), "{error}");
    assert!(error.message.contains("候选规则"), "{error}");
    assert!(error.message.contains("applicable"), "{error}");
    assert!(error.message.contains("inapplicable"), "{error}");
}

#[test]
fn a_candidate_cannot_swap_in_an_unrelated_held_premise() {
    let env = env_from(CANDIDATE_ENV);
    let mut anchor = ApplicabilityAnchor::default();
    anchor.event_dates.push("2023-01-01".to_owned());
    let applicability = recorded(&env, "后规", &anchor);
    let certificate = gap_candidate_certificate(vec![atom("别的", "甲")], applicability);
    let error = reject(&certificate, &env);
    assert_eq!(error.node, Some(0), "{error}");
    assert!(
        error.message.contains("既未把它列为已持有") || error.message.contains("已持有前提列表"),
        "{error}"
    );
}

#[test]
fn a_candidate_with_a_tampered_date_is_rejected() {
    let env = env_from(CANDIDATE_ENV);
    let held = vec![atom("行为", "甲")];
    let mut applicability = candidate_record(&env, &["2019-05-01"]);
    applicability.basis.dates[0].date = "2023-01-01".to_owned();
    let certificate = gap_candidate_certificate(held, applicability);
    let error = reject(&certificate, &env);
    assert_eq!(error.node, Some(0), "{error}");
    assert!(error.message.contains("dates[0].date"), "{error}");
}
