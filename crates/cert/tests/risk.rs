//! Risk-theme derivation from the environment's `risk` markers and a
//! certificate's root proof graph.
//!
//! The judgement is structural: a theme applies when a proposition reachable
//! from the certificate's root has a marked predicate as its kernel predicate
//! head. These tests pin the five themes, the root-reachability boundary, the
//! `def`-alias normalization, the gap root, and the evidence text that names the
//! proposition, the theme, the declaring `risk` line and the rule's sources.

use std_deduce_cert::{
    derive_risk, ApplicabilityBasis, ApplicabilityReason, ApplicabilityReasonKind,
    ApplicabilityVerdict, Assumption, Binding, CertExpr, Certificate, EnvironmentIdentity,
    Explicit, FactIdentity, FormatVersion, Node, RuleApplicability, Source,
};
use std_deduce_kernel::{Decl, DeclKind, Env, Expr, RiskTheme};
use std_deduce_lang::Library;

fn constant(name: &str) -> CertExpr {
    CertExpr::Const {
        name: name.to_owned(),
    }
}

fn app(func: CertExpr, arg: CertExpr) -> CertExpr {
    CertExpr::App {
        func: Box::new(func),
        arg: Box::new(arg),
    }
}

fn atom(predicate: &str, object: &str) -> CertExpr {
    app(constant(predicate), constant(object))
}

fn assumption(proposition: CertExpr, identity: FactIdentity) -> Assumption {
    Assumption {
        proposition,
        identity,
        sources: Vec::new(),
        label: None,
        occurred_at: Explicit::none(),
        occurred_in: Explicit::none(),
    }
}

fn applicability() -> Box<RuleApplicability> {
    Box::new(RuleApplicability {
        verdict: ApplicabilityVerdict::Unchecked,
        basis: ApplicabilityBasis::default(),
        reason: Explicit::some(ApplicabilityReason::new(
            ApplicabilityReasonKind::RuleHasNoScope,
        )),
    })
}

fn source(text: &str, locator: &str) -> Source {
    Source {
        text: text.to_owned(),
        locator: locator.to_owned(),
        version: String::new(),
        effective: None,
        note: String::new(),
        quote: String::new(),
        url: String::new(),
        jurisdiction: String::new(),
        retrieved_at: String::new(),
        hash: String::new(),
    }
}

fn rule(name: &str, conclusion: CertExpr, premises: Vec<usize>, sources: Vec<Source>) -> Node {
    Node::RuleApplication {
        rule: name.to_owned(),
        conclusion,
        premises,
        bindings: Vec::<Binding>::new(),
        sources,
        applicability: applicability(),
    }
}

fn certificate(assumptions: Vec<Assumption>, nodes: Vec<Node>, root: Option<usize>) -> Certificate {
    Certificate {
        format_version: FormatVersion::CURRENT,
        environment: EnvironmentIdentity::Unrecorded,
        assumptions,
        interpretations: Vec::new(),
        nodes,
        root,
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Default::default(),
    }
}

/// An environment declaring `pred 违法 : 人 → Prop`, the unmarked
/// `pred 触发 : 人 → Prop`, `obj 甲 : 人` and the requested `risk` markers.
fn env_with(markers: &[(&str, RiskTheme)]) -> Env {
    let mut source =
        String::from("sort 人\npred 违法 : 人 → Prop\npred 触发 : 人 → Prop\nobj 甲 : 人\n");
    for (predicate, theme) in markers {
        source.push_str(&format!("risk {} {predicate}\n", theme.keyword()));
    }
    let mut library = Library::new();
    library
        .load("cert-risk", &source)
        .expect("test theory loads");
    library.env
}

#[test]
fn all_five_themes_are_declared_and_print_their_own_warning() {
    let themes = [
        (RiskTheme::Criminal, "刑事"),
        (RiskTheme::PersonalSafety, "人身安全"),
        (RiskTheme::MajorProperty, "重大财产"),
        (RiskTheme::ApproachingDeadline, "临近期限"),
        (RiskTheme::ForeignOrImmigration, "涉外或移民"),
    ];
    for (theme, keyword) in themes {
        assert_eq!(theme.keyword(), keyword);
        assert_eq!(RiskTheme::parse(keyword), Some(theme));
        let env = env_with(&[("违法", theme)]);
        let certificate = certificate(
            vec![assumption(atom("违法", "甲"), FactIdentity::UserAsserted)],
            vec![Node::Assumption { assumption: 0 }],
            Some(0),
        );
        let report = derive_risk(&env, &certificate).unwrap();
        assert!(report.is_high_risk(), "{keyword} must be high risk");
        assert_eq!(report.themes(), &[theme]);
        let warning = report.warning_line().expect("a warning line");
        assert_eq!(
            warning,
            format!("高风险题材：涉及{keyword}；建议尽快咨询执业律师。")
        );
    }
}

#[test]
fn a_derivation_without_any_marker_is_not_high_risk() {
    let env = env_with(&[]);
    let certificate = certificate(
        vec![assumption(atom("违法", "甲"), FactIdentity::UserAsserted)],
        vec![Node::Assumption { assumption: 0 }],
        Some(0),
    );
    let report = derive_risk(&env, &certificate).unwrap();
    assert!(!report.is_high_risk());
    assert!(report.themes().is_empty());
    assert_eq!(report.warning_line(), None);
}

#[test]
fn evidence_names_the_proposition_the_theme_and_the_rule_with_its_source() {
    let env = env_with(&[("违法", RiskTheme::Criminal)]);
    let certificate = certificate(
        vec![assumption(atom("触发", "甲"), FactIdentity::Stipulated)],
        vec![
            Node::Assumption { assumption: 0 },
            rule(
                "处罚规则",
                atom("违法", "甲"),
                vec![0],
                vec![source("测试法", "第一条")],
            ),
        ],
        Some(1),
    );
    let report = derive_risk(&env, &certificate).unwrap();
    let evidence = report.evidence(RiskTheme::Criminal);
    assert_eq!(evidence.len(), 1, "{evidence:?}");
    let line = &evidence[0];
    assert!(line.contains("命题「违法 甲」"), "{line}");
    assert!(line.contains("由规则「处罚规则」推出"), "{line}");
    assert!(line.contains("其谓词「违法」"), "{line}");
    assert!(line.contains("被声明为风险题材「刑事」"), "{line}");
    assert!(line.contains("（声明 `risk 刑事 违法`）"), "{line}");
    assert!(line.contains("出处：「测试法第一条」"), "{line}");
}

#[test]
fn a_themed_fact_states_its_identity_and_sources() {
    let env = env_with(&[("违法", RiskTheme::Criminal)]);
    let mut entry = assumption(atom("违法", "甲"), FactIdentity::Verified);
    entry.sources = vec![source("判决", "第一页")];
    let certificate = certificate(
        vec![entry],
        vec![Node::Assumption { assumption: 0 }],
        Some(0),
    );
    let report = derive_risk(&env, &certificate).unwrap();
    let line = &report.evidence(RiskTheme::Criminal)[0];
    assert!(line.contains("是事实〔法院查明〕"), "{line}");
    assert!(line.contains("出处：「判决第一页」"), "{line}");
}

#[test]
fn a_themed_proposition_on_an_unrelated_branch_is_not_high_risk() {
    let env = env_with(&[("违法", RiskTheme::Criminal)]);
    // Node 1 proves the themed proposition, but the root (node 2) does not use
    // it. The certificate lists the whole fixed point, so relevance must follow
    // the root's proof graph.
    let certificate = certificate(
        vec![
            assumption(atom("违法", "甲"), FactIdentity::UserAsserted),
            assumption(atom("触发", "甲"), FactIdentity::UserAsserted),
        ],
        vec![
            Node::Assumption { assumption: 0 },
            rule("无关规则", atom("违法", "甲"), vec![0], Vec::new()),
            Node::Assumption { assumption: 1 },
        ],
        Some(2),
    );
    let report = derive_risk(&env, &certificate).expect("an unrelated branch is not an error");
    assert!(!report.is_high_risk());
}

#[test]
fn a_def_alias_of_the_themed_predicate_is_recognised() {
    // `def 别名 := 违法` unfolds to the marked predicate during normalization,
    // so a rule that concludes the alias is about the same theme.
    let source = "sort 人\npred 违法 : 人 → Prop\n\
                  def 别名 : 人 → Prop := λ (x : 人) := 违法 x\n\
                  obj 甲 : 人\nrisk 刑事 违法\n\
                  axiom 甲违法 : 违法 甲\n  source text \"案情\" locator \"一\"\n";
    let mut library = Library::new();
    library.load("cert-risk-alias", source).expect("loads");
    let env = library.env;
    let certificate = certificate(
        vec![assumption(atom("违法", "甲"), FactIdentity::UserAsserted)],
        vec![
            Node::Assumption { assumption: 0 },
            rule("别名规则", atom("别名", "甲"), vec![0], Vec::new()),
        ],
        Some(1),
    );
    let report = derive_risk(&env, &certificate).unwrap();
    assert!(report.is_high_risk());
    assert_eq!(report.themes(), &[RiskTheme::Criminal]);
    let line = &report.evidence(RiskTheme::Criminal)[0];
    assert!(line.contains("命题「别名 甲」"), "{line}");
    assert!(line.contains("被声明为风险题材「刑事」"), "{line}");
}

#[test]
fn a_gap_root_still_reports_its_theme() {
    let env = env_with(&[("违法", RiskTheme::PersonalSafety)]);
    let certificate = certificate(
        Vec::new(),
        vec![Node::Gap {
            proposition: atom("违法", "甲"),
            candidates: Vec::new(),
            axiom_candidates: Vec::new(),
            note: None,
        }],
        Some(0),
    );
    let report = derive_risk(&env, &certificate).unwrap();
    assert!(report.is_high_risk());
    let line = &report.evidence(RiskTheme::PersonalSafety)[0];
    assert!(line.contains("目标「违法 甲」未获证明"), "{line}");
}

#[test]
fn the_same_certificate_derives_byte_identical_text_twice() {
    let env = env_with(&[("违法", RiskTheme::Criminal)]);
    let certificate = certificate(
        vec![assumption(atom("违法", "甲"), FactIdentity::UserAsserted)],
        vec![Node::Assumption { assumption: 0 }],
        Some(0),
    );
    let first = derive_risk(&env, &certificate).unwrap();
    let second = derive_risk(&env, &certificate).unwrap();
    assert_eq!(first, second);
    assert_eq!(first.warning_line(), second.warning_line());
    assert_eq!(
        first.evidence(RiskTheme::Criminal),
        second.evidence(RiskTheme::Criminal)
    );
}

#[test]
fn two_conflicting_markers_for_one_predicate_are_an_error() {
    let env = env_with(&[("违法", RiskTheme::Criminal)]);
    let mut env = env;
    let marker = Decl {
        name: std_deduce_kernel::name("risk:违法:duplicate"),
        kind: DeclKind::Risk {
            theme: RiskTheme::PersonalSafety,
            pred: std_deduce_kernel::name("违法"),
        },
        ty: Expr::Sort(1),
        sources: Vec::new(),
        scope: Default::default(),
        occurred_at: None,
        occurred_in: None,
        index: 0,
    };
    env.insert(marker, &std_deduce_kernel::Ctx::new())
        .expect("the second marker inserts; the derivation must refuse it");
    let certificate = certificate(
        vec![assumption(atom("违法", "甲"), FactIdentity::UserAsserted)],
        vec![Node::Assumption { assumption: 0 }],
        Some(0),
    );
    let error = derive_risk(&env, &certificate)
        .expect_err("two themes for one predicate must not be silently resolved");
    assert!(error.contains("重复的 risk 标记"), "{error}");
}

#[test]
fn a_rule_whose_conclusion_head_is_themed_but_is_not_reachable_is_ignored() {
    // A themed `rule_application` node exists, but the root is an unthemed
    // assumption and never cites it: the certificate lists it as part of the
    // fixed point, not as part of this conclusion's proof.
    let env = env_with(&[("违法", RiskTheme::ForeignOrImmigration)]);
    let certificate = certificate(
        vec![assumption(atom("触发", "甲"), FactIdentity::UserAsserted)],
        vec![
            Node::Assumption { assumption: 0 },
            rule("外部规则", atom("违法", "甲"), vec![0], Vec::new()),
        ],
        Some(0),
    );
    let report = derive_risk(&env, &certificate).unwrap();
    assert!(!report.is_high_risk());
}
