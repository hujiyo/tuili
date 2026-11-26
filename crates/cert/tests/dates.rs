//! Certificate-level calendar dates: the `date` expression, the recorded
//! `computed` form of a date step, and the checker's recomputation of the
//! built-in date operations.
//!
//! The certificates here are built by hand, so the checker is tested on its own
//! contract rather than on the reasoner's output. The end-to-end path (a
//! generated certificate, a tampered copy, the CLI) is tested in
//! `crates/cli/tests/dates.rs`.

use std_deduce_cert::{
    check, expression_key, ApplicabilityBasis, ApplicabilityReason, ApplicabilityReasonKind,
    ApplicabilityVerdict, Assumption, Binding, CertDate, CertExpr, Certificate,
    EnvironmentIdentity, Explicit, FactIdentity, FormatVersion, Node, RuleApplicability,
};
use std_deduce_kernel::Env;
use std_deduce_lang::Library;

/// One rule that steps a start day by three years, and one guarded rule that
/// compares that deadline with a query day. Both conclude with dates, so their
/// instances really compute something.
const THEORY: &str = r#"
sort 人
pred 起算 : 人 → Date → Prop
pred 截止 : 人 → Date → Prop
pred 查询日 : Date → Prop
pred 逾期 : 人 → Prop
obj 甲 : 人
rule 截止日 :
  params p : 人, d : Date
  premise 起算 p d
  conclude 截止 p (addYears d 3)
  source text "测试" locator "夹具"
rule 逾期认定 :
  params p : 人, d : Date, today : Date
  premise 起算 p d
  premise 查询日 today
  guard (less (addYears d 3) today)
  conclude 逾期 p
  source text "测试" locator "夹具二"
"#;

fn env() -> Env {
    let mut library = Library::new();
    library
        .load("cert-dates", THEORY)
        .expect("test theory loads");
    library.env
}

fn constant(name: &str) -> CertExpr {
    CertExpr::Const {
        name: name.to_owned(),
    }
}

fn num(value: i64) -> CertExpr {
    CertExpr::Num { value }
}

fn day(value: &str) -> CertExpr {
    CertExpr::Date {
        value: CertDate::parse(value).expect("a real calendar day"),
    }
}

fn app(function: CertExpr, arg: CertExpr) -> CertExpr {
    CertExpr::App {
        func: Box::new(function),
        arg: Box::new(arg),
    }
}

fn apply(function: &str, arguments: Vec<CertExpr>) -> CertExpr {
    arguments.into_iter().fold(constant(function), app)
}

/// `起算 甲 d"2020-05-06"` and `查询日 d"2024-01-02"`.
fn assumption(proposition: CertExpr) -> Assumption {
    Assumption {
        proposition,
        identity: FactIdentity::UserAsserted,
        sources: Vec::new(),
        label: None,
        occurred_at: Explicit::none(),
        occurred_in: Explicit::none(),
    }
}

fn unscoped_applicability() -> Box<RuleApplicability> {
    Box::new(RuleApplicability {
        verdict: ApplicabilityVerdict::Unchecked,
        basis: ApplicabilityBasis::default(),
        reason: Explicit::some(ApplicabilityReason::new(
            ApplicabilityReasonKind::RuleHasNoScope,
        )),
    })
}

fn bindings(values: Vec<(&str, CertExpr)>) -> Vec<Binding> {
    values
        .into_iter()
        .map(|(parameter, value)| Binding {
            parameter: parameter.to_owned(),
            value,
        })
        .collect()
}

fn certificate(nodes: Vec<Node>, root: usize, assumptions: Vec<Assumption>) -> Certificate {
    Certificate {
        format_version: FormatVersion::CURRENT,
        environment: EnvironmentIdentity::Unrecorded,
        assumptions,
        interpretations: Vec::new(),
        nodes,
        root: Some(root),
        alternatives: Vec::new(),
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Default::default(),
    }
}

fn date_node(conclusion: CertExpr, computed: Option<CertExpr>) -> Node {
    Node::RuleApplication {
        guards: Vec::new(),
        rule: "截止日".to_owned(),
        conclusion,
        computed,
        premises: vec![0],
        bindings: bindings(vec![("p", constant("甲")), ("d", day("2020-05-06"))]),
        sources: Vec::new(),
        applicability: unscoped_applicability(),
    }
}

/// The `截止 甲 d"2023-05-06"` step, with its pre-evaluation form recorded.
fn deadline_certificate() -> Certificate {
    let start = apply("起算", vec![constant("甲"), day("2020-05-06")]);
    let computed = apply(
        "截止",
        vec![
            constant("甲"),
            apply("addYears", vec![day("2020-05-06"), num(3)]),
        ],
    );
    certificate(
        vec![
            Node::Assumption { assumption: 0 },
            date_node(
                apply("截止", vec![constant("甲"), day("2023-05-06")]),
                Some(computed),
            ),
        ],
        1,
        vec![assumption(start)],
    )
}

#[test]
fn a_date_serializes_as_a_canonical_day_string() {
    let expression = day("2020-05-06");
    let json = serde_json::to_string(&expression).expect("a date serializes");
    assert_eq!(json, r#"{"kind":"date","value":"2020-05-06"}"#);
    let parsed: CertExpr = serde_json::from_str(&json).expect("a date parses");
    assert_eq!(parsed, expression);
}

#[test]
fn an_impossible_or_out_of_range_date_is_rejected_at_parse() {
    for value in [
        "2020-02-30",
        "2020-13-01",
        "2021-02-29",
        "2020-5-6",
        "1899-12-31",
        "0000-01-01",
        "9999-12-32",
        "今日",
    ] {
        let text = format!(r#"{{"kind":"date","value":"{value}"}}"#);
        let parsed: Result<CertExpr, _> = serde_json::from_str(&text);
        assert!(parsed.is_err(), "`{value}` must not parse as a date");
    }
    // The value field is mandatory and a non-string is refused.
    assert!(serde_json::from_str::<CertExpr>(r#"{"kind":"date"}"#).is_err());
    assert!(serde_json::from_str::<CertExpr>(r#"{"kind":"date","value":20200506}"#).is_err());
    assert!(
        serde_json::from_str::<CertExpr>(r#"{"kind":"date","value":"2020-05-06","extra":1}"#)
            .is_err(),
        "unknown fields are refused"
    );
}

#[test]
fn a_date_key_is_distinct_from_a_day_named_constant_and_an_integer() {
    let date = std_deduce_kernel::Date::parse("2020-05-06").expect("a real day");
    assert_ne!(
        expression_key(&std_deduce_kernel::Expr::Date(date)),
        expression_key(&std_deduce_kernel::Expr::constant("2020-05-06"))
    );
    assert_ne!(
        expression_key(&std_deduce_kernel::Expr::Date(date)),
        expression_key(&std_deduce_kernel::Expr::Num(2020))
    );
    assert_eq!(
        expression_key(&std_deduce_kernel::Expr::Date(date)),
        expression_key(&std_deduce_kernel::Expr::Date(date))
    );
}

#[test]
fn a_date_step_is_accepted_when_the_computed_form_matches() {
    let cert = deadline_certificate();
    check(&env(), &cert).expect("the date step is recomputed and accepted");
}

#[test]
fn a_date_step_without_the_computed_form_is_rejected() {
    // The instance evaluates `addYears d"2020-05-06" 3` into a day, so the
    // pre-evaluation form is required: without it the recorded day would be the
    // only trace of the computation.
    let mut cert = deadline_certificate();
    if let Node::RuleApplication { computed, .. } = &mut cert.nodes[1] {
        *computed = None;
    }
    let error = check(&env(), &cert).expect_err("a missing date step must be refused");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.to_string().contains("没有记录未求值形式"), "{error}");
}

#[test]
fn a_tampered_date_operand_is_rejected() {
    let mut cert = deadline_certificate();
    if let Node::RuleApplication { computed, .. } = &mut cert.nodes[1] {
        *computed = Some(apply(
            "截止",
            vec![
                constant("甲"),
                apply("addYears", vec![day("2020-05-07"), num(3)]),
            ],
        ));
    }
    let error = check(&env(), &cert).expect_err("a changed operand must be refused");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(
        error.to_string().contains("算术步骤与规则不一致"),
        "{error}"
    );
}

#[test]
fn a_swapped_date_operation_is_rejected() {
    let mut cert = deadline_certificate();
    if let Node::RuleApplication { computed, .. } = &mut cert.nodes[1] {
        *computed = Some(apply(
            "截止",
            vec![
                constant("甲"),
                apply("addMonths", vec![day("2020-05-06"), num(3)]),
            ],
        ));
    }
    let error = check(&env(), &cert).expect_err("a swapped operation must be refused");
    assert!(error.to_string().contains("addMonths"), "{error}");
    assert!(error.to_string().contains("addYears"), "{error}");
}

#[test]
fn a_tampered_conclusion_day_is_rejected() {
    let mut cert = deadline_certificate();
    if let Node::RuleApplication { conclusion, .. } = &mut cert.nodes[1] {
        *conclusion = apply("截止", vec![constant("甲"), day("2023-05-07")]);
    }
    let error = check(&env(), &cert).expect_err("a changed day must be refused");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.to_string().contains("2023-05-07"), "{error}");
    assert!(error.to_string().contains("addYears"), "{error}");
}

#[test]
fn a_date_step_that_leaves_the_range_is_an_error() {
    // The recorded step computes `9999-12-31 + 1 year`, which the kernel
    // refuses. The checker reports the overflow instead of accepting a day the
    // kernel would never produce.
    let start = apply("起算", vec![constant("甲"), day("9999-12-31")]);
    let cert = certificate(
        vec![
            Node::Assumption { assumption: 0 },
            Node::RuleApplication {
                guards: Vec::new(),
                rule: "截止日".to_owned(),
                conclusion: apply("截止", vec![constant("甲"), day("2023-05-06")]),
                computed: Some(apply(
                    "截止",
                    vec![
                        constant("甲"),
                        apply("addYears", vec![day("9999-12-31"), num(3)]),
                    ],
                )),
                premises: vec![0],
                bindings: bindings(vec![("p", constant("甲")), ("d", day("9999-12-31"))]),
                sources: Vec::new(),
                applicability: unscoped_applicability(),
            },
        ],
        1,
        vec![assumption(start)],
    );
    let error = check(&env(), &cert).expect_err("the overflow must be reported");
    assert!(error.to_string().contains("日期运算溢出"), "{error}");
}

#[test]
fn a_guard_over_dates_is_recomputed() {
    // `逾期认定` is guarded by a date comparison. The record carries the
    // declared guard, the substituted form and the judged truth value; the
    // checker re-evaluates the comparison itself.
    let guarded = |holds: bool, instance_day: &str| Node::RuleApplication {
        rule: "逾期认定".to_owned(),
        conclusion: apply("逾期", vec![constant("甲")]),
        computed: None,
        premises: vec![0, 1],
        bindings: bindings(vec![
            ("p", constant("甲")),
            ("d", day("2020-05-06")),
            ("today", day(instance_day)),
        ]),
        guards: vec![std_deduce_cert::model::GuardRecord {
            index: 0,
            expression: apply(
                "less",
                vec![
                    apply("addYears", vec![constant("?d"), num(3)]),
                    constant("?today"),
                ],
            ),
            instance: apply(
                "less",
                vec![
                    apply("addYears", vec![day("2020-05-06"), num(3)]),
                    day(instance_day),
                ],
            ),
            holds: Explicit::some(holds),
        }],
        sources: Vec::new(),
        applicability: unscoped_applicability(),
    };
    let start = apply("起算", vec![constant("甲"), day("2020-05-06")]);
    let query = apply("查询日", vec![day("2024-01-02")]);
    let cert = certificate(
        vec![
            Node::Assumption { assumption: 0 },
            Node::Assumption { assumption: 1 },
            guarded(true, "2024-01-02"),
        ],
        2,
        vec![assumption(start), assumption(query)],
    );
    check(&env(), &cert).expect("the date guard holds and is recomputed");

    // Flipping the recorded truth value is refused.
    let mut flipped = cert.clone();
    if let Node::RuleApplication { guards, .. } = &mut flipped.nodes[2] {
        guards[0].holds = Explicit::some(false);
    }
    let error = check(&env(), &flipped).expect_err("a flipped guard must be refused");
    assert_eq!(error.node, Some(2), "{error}");
    assert!(error.to_string().contains("守卫"), "{error}");

    // Changing the instance's day changes the verdict: the record no longer
    // matches what the environment declaration and the bindings produce.
    let mut edited = cert.clone();
    if let Node::RuleApplication { guards, .. } = &mut edited.nodes[2] {
        guards[0].instance = apply(
            "less",
            vec![
                apply("addYears", vec![day("2020-05-06"), num(3)]),
                day("2023-01-02"),
            ],
        );
    }
    let error = check(&env(), &edited).expect_err("a changed guard day must be refused");
    assert!(error.to_string().contains("按绑定得到的形态"), "{error}");
}
