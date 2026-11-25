//! Certificate interpretation checks, independent of the reasoner.
//!
//! The certificate lists the enabled interpretations it cites, a node applies
//! one to a premise, and a conflict may name an interpretation as its witness.
//! These tests hand-build certificates against a real loaded environment, so a
//! forged table, index, direction, source or conclusion is rejected by
//! `cert::check` / `cert::kernel_proof` rather than trusted.

use std_deduce_cert::{
    check, kernel_proof, ApplicabilityBasis, ApplicabilityReason, ApplicabilityReasonKind,
    ApplicabilityVerdict, Assumption, CertExpr, Certificate, Conflict, EnvironmentIdentity,
    Explicit, FactIdentity, FormatVersion, Interpretation, InterpretationDirection, Metadata, Node,
    Provenance, Resolution, RuleApplicability, Source, UnresolvedReason,
};
use std_deduce_kernel::env::DeclKind;
use std_deduce_kernel::{name, Expr};
use std_deduce_lang::Library;

const ENV: &str = r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred R : 人 → Prop
pred S : 人 → Prop
obj 张三 : 人
contrary Q R
axiom 事实P : P 张三
  source text "案情" locator "一"
interpret i1 : P 张三 → Q 张三
  direction literal
  source text "解释" locator "一" version "2020"
interpret i2 : R 张三 → S 张三
  direction analogy
  source text "解释" locator "二" version "2020"
interpret i3 : P 张三 → Q 张三
  direction expand
  source text "解释" locator "三" version "2020"
interpret i4 : Q 张三 → R 张三
  direction narrow
  source text "解释" locator "四" version "2020"
rule 规则R :
  conclude R 张三
  source text "规则" locator "一"
rule 规则S :
  premise Q 张三
  conclude S 张三
  source text "规则" locator "二"
"#;

fn load() -> Library {
    let mut lib = Library::new();
    lib.load("interpret.std", ENV)
        .unwrap_or_else(|error| panic!("load: {error}"));
    lib
}

fn atom(pred: &str) -> Expr {
    Expr::apps(Expr::constant(pred), [Expr::constant("张三")])
}

fn cert_expr(pred: &str) -> CertExpr {
    CertExpr::try_from(&atom(pred)).expect("the expression is encodable")
}

fn interpretation(lib: &Library, id: &str) -> Interpretation {
    let decl = lib.env.get(&name(id)).expect("the declaration exists");
    let DeclKind::Interpretation(declared) = &decl.kind else {
        panic!("`{id}` is not an interpretation");
    };
    Interpretation {
        id: id.to_owned(),
        direction: InterpretationDirection::from(&declared.direction),
        from: CertExpr::try_from(&declared.from).expect("from is encodable"),
        to: CertExpr::try_from(&declared.to).expect("to is encodable"),
        sources: declared.sources.iter().map(Source::from).collect(),
    }
}

fn fact_assumption(lib: &Library, id: &str) -> Assumption {
    let decl = lib.env.get(&name(id)).expect("the fact exists");
    let DeclKind::Fact { identity } = &decl.kind else {
        panic!("`{id}` is not a fact");
    };
    Assumption {
        proposition: CertExpr::try_from(&decl.ty).expect("the proposition is encodable"),
        identity: FactIdentity::from(identity),
        sources: decl.sources.iter().map(Source::from).collect(),
        label: Some(id.to_owned()),
        occurred_at: Explicit::none(),
        occurred_in: Explicit::none(),
    }
}

/// The record of a rule declared without any scope.
fn unscoped_applicability() -> Box<RuleApplicability> {
    Box::new(RuleApplicability {
        verdict: ApplicabilityVerdict::Unchecked,
        basis: ApplicabilityBasis::default(),
        reason: Explicit::some(ApplicabilityReason::new(
            ApplicabilityReasonKind::RuleHasNoScope,
        )),
    })
}

fn certificate(lib: &Library) -> Certificate {
    Certificate {
        format_version: FormatVersion::CURRENT,
        environment: EnvironmentIdentity::none(),
        assumptions: vec![fact_assumption(lib, "事实P")],
        interpretations: vec![interpretation(lib, "i1")],
        nodes: vec![
            Node::Assumption { assumption: 0 },
            Node::InterpretationApplication {
                interpretation: 0,
                premise: 0,
                conclusion: cert_expr("Q"),
            },
        ],
        root: Some(1),
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Metadata::default(),
    }
}

fn reject(cert: &Certificate) -> String {
    let lib = load();
    check(&lib.env, cert)
        .expect_err("the certificate must be rejected")
        .to_string()
}

#[test]
fn a_v6_interpretation_application_checks_and_proves() {
    let lib = load();
    let cert = certificate(&lib);
    let report = check(&lib.env, &cert).expect("the certificate is legal");
    assert!(report.root_proved);
    assert_eq!(report.nodes_checked, 2);
    let kernel = kernel_proof(&lib.env, &cert).expect("the kernel proof is legal");
    assert!(kernel.root_proved);
    assert!(
        kernel.steps.is_empty(),
        "an interpretation is not a rule step"
    );
}

#[test]
fn an_interpretation_the_environment_does_not_declare_is_rejected() {
    let lib = load();
    let mut cert = certificate(&lib);
    cert.interpretations[0].id = "不存在".to_owned();
    let error = reject(&cert);
    assert!(error.contains("没有声明"), "{error}");
}

#[test]
fn a_direction_that_differs_from_the_declaration_is_rejected() {
    let lib = load();
    let mut cert = certificate(&lib);
    cert.interpretations[0].direction = InterpretationDirection::Analogy;
    let error = reject(&cert);
    assert!(error.contains("方向"), "{error}");
}

#[test]
fn a_source_that_differs_from_the_declaration_is_rejected() {
    let lib = load();
    let mut cert = certificate(&lib);
    cert.interpretations[0].sources[0].locator = "伪造条号".to_owned();
    let error = reject(&cert);
    assert!(error.contains("来源"), "{error}");
}

#[test]
fn from_and_to_are_compared_by_kernel_conversion_with_the_environment() {
    let lib = load();
    let mut cert = certificate(&lib);
    cert.interpretations[0].from = cert_expr("Q");
    let error = reject(&cert);
    assert!(error.contains("from"), "{error}");

    let mut cert = certificate(&lib);
    cert.interpretations[0].to = cert_expr("P");
    cert.nodes[1] = Node::InterpretationApplication {
        interpretation: 0,
        premise: 0,
        conclusion: cert_expr("P"),
    };
    let error = reject(&cert);
    assert!(error.contains("to"), "{error}");
}

#[test]
fn a_missing_or_out_of_range_interpretation_index_is_rejected() {
    let lib = load();
    let mut cert = certificate(&lib);
    cert.nodes[1] = Node::InterpretationApplication {
        interpretation: 9,
        premise: 0,
        conclusion: cert_expr("Q"),
    };
    let error = reject(&cert);
    assert!(error.contains("不存在的解释"), "{error}");

    let mut cert = certificate(&lib);
    cert.interpretations.clear();
    let error = reject(&cert);
    assert!(error.contains("不存在的解释"), "{error}");
}

#[test]
fn the_premise_must_prove_from_and_must_be_earlier() {
    let lib = load();
    let mut cert = certificate(&lib);
    cert.nodes[1] = Node::InterpretationApplication {
        interpretation: 0,
        premise: 1,
        conclusion: cert_expr("Q"),
    };
    let error = reject(&cert);
    assert!(error.contains("之前的节点"), "{error}");

    // A second assumption proves `Q`, not `from` (`P`).
    let mut cert = certificate(&lib);
    cert.assumptions.push(Assumption {
        proposition: cert_expr("Q"),
        identity: FactIdentity::UserAsserted,
        sources: Vec::new(),
        label: None,
        occurred_at: Explicit::none(),
        occurred_in: Explicit::none(),
    });
    cert.nodes = vec![
        Node::Assumption { assumption: 0 },
        Node::Assumption { assumption: 1 },
        Node::InterpretationApplication {
            interpretation: 0,
            premise: 1,
            conclusion: cert_expr("Q"),
        },
    ];
    cert.root = Some(2);
    let error = reject(&cert);
    assert!(error.contains("from 是"), "{error}");
}

#[test]
fn the_conclusion_must_be_the_declarations_to() {
    let lib = load();
    let mut cert = certificate(&lib);
    cert.nodes[1] = Node::InterpretationApplication {
        interpretation: 0,
        premise: 0,
        conclusion: cert_expr("P"),
    };
    let error = check(&lib.env, &cert)
        .expect_err("a wrong conclusion is rejected")
        .to_string();
    assert!(error.contains("to 是"), "{error}");
    let error = kernel_proof(&lib.env, &cert)
        .expect_err("the kernel proof uses the declared `to`")
        .to_string();
    assert!(error.contains("结论"), "{error}");
}

#[test]
fn an_entry_that_nothing_references_is_rejected() {
    let lib = load();
    let mut cert = certificate(&lib);
    cert.interpretations.push(interpretation(&lib, "i2"));
    let error = reject(&cert);
    assert!(error.contains("没有被任何"), "{error}");
}

#[test]
fn two_enabled_interpretations_may_not_license_equivalent_conclusions() {
    let lib = load();
    let mut cert = certificate(&lib);
    cert.interpretations.push(interpretation(&lib, "i3"));
    cert.nodes.push(Node::InterpretationApplication {
        interpretation: 1,
        premise: 0,
        conclusion: cert_expr("Q"),
    });
    cert.root = Some(2);
    let error = reject(&cert);
    assert!(error.contains("等价"), "{error}");
}

#[test]
fn the_interpretations_table_is_sorted_by_id() {
    let lib = load();
    let mut cert = certificate(&lib);
    // `i2` sorts after `i1`; put it first and reference both.
    cert.interpretations = vec![interpretation(&lib, "i2"), interpretation(&lib, "i1")];
    cert.assumptions.push(Assumption {
        proposition: cert_expr("R"),
        identity: FactIdentity::UserAsserted,
        sources: Vec::new(),
        label: None,
        occurred_at: Explicit::none(),
        occurred_in: Explicit::none(),
    });
    cert.nodes = vec![
        Node::Assumption { assumption: 0 },
        Node::Assumption { assumption: 1 },
        Node::InterpretationApplication {
            interpretation: 0,
            premise: 1,
            conclusion: cert_expr("S"),
        },
        Node::InterpretationApplication {
            interpretation: 1,
            premise: 0,
            conclusion: cert_expr("Q"),
        },
    ];
    cert.root = Some(3);
    let error = reject(&cert);
    assert!(error.contains("排序"), "{error}");
}

/// A certificate whose conflict edges are interpretation vs rule.
fn conflict_certificate(lib: &Library) -> Certificate {
    let mut cert = certificate(lib);
    cert.conflicts = vec![Conflict {
        left: cert_expr("Q"),
        right: cert_expr("R"),
        left_by: Provenance::Interpretation { interpretation: 0 },
        right_by: Provenance::Rules {
            rules: vec!["规则R".to_owned()],
        },
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::NoPriority,
        },
    }];
    // Keep the root out of the conflict so the check exercises the conflict
    // record rather than failing the root.
    cert.root = Some(0);
    cert
}

#[test]
fn an_interpretation_conflict_witness_is_validated() {
    let lib = load();
    let cert = conflict_certificate(&lib);
    let report = check(&lib.env, &cert).expect("the interpretation witness is well-formed");
    assert!(report.root_proved);
    kernel_proof(&lib.env, &cert).expect("the kernel proof passes");

    let mut forged = conflict_certificate(&lib);
    forged.conflicts[0].left_by = Provenance::Interpretation { interpretation: 7 };
    let error = check(&lib.env, &forged)
        .expect_err("an out-of-range interpretation witness is rejected")
        .to_string();
    assert!(error.contains("不存在的解释 7"), "{error}");

    let mut forged = conflict_certificate(&lib);
    forged.conflicts[0].left = cert_expr("R");
    let error = check(&lib.env, &forged)
        .expect_err("a witness whose `to` differs is rejected")
        .to_string();
    assert!(error.contains("to"), "{error}");

    let mut forged = conflict_certificate(&lib);
    forged.conflicts[0].resolution = Resolution::Unresolved {
        reason: UnresolvedReason::UnknownWitnesses,
    };
    let error = check(&lib.env, &forged)
        .expect_err("an interpretation witness is never a lost rule witness")
        .to_string();
    assert!(error.contains("解释"), "{error}");
}

#[test]
fn a_fact_against_an_interpretation_is_a_defeat_or_an_unresolved_claim() {
    let lib = load();
    let mut cert = conflict_certificate(&lib);
    // Strict fact `P` on the left, interpretation conclusion `Q` on the
    // right: NoPriority is the wrong record.
    cert.assumptions.push(fact_assumption(&lib, "事实P"));
    cert.conflicts[0].left = cert_expr("P");
    cert.conflicts[0].left_by = Provenance::Assumption;
    cert.conflicts[0].right = cert_expr("Q");
    cert.conflicts[0].right_by = Provenance::Interpretation { interpretation: 0 };
    let error = check(&lib.env, &cert)
        .expect_err("a fact side cannot be recorded as no priority")
        .to_string();
    assert!(error.contains("没有优先关系"), "{error}");
}

#[test]
fn a_rule_premise_cannot_be_an_interpretation_application() {
    let lib = load();
    let mut cert = certificate(&lib);
    let rule = lib.env.get(&name("规则S")).expect("the rule exists");
    cert.nodes.push(Node::RuleApplication {
        rule: "规则S".to_owned(),
        conclusion: cert_expr("S"),
        // Node 1 is the interpretation application that licenses `Q`, which
        // is this rule's premise. Every step typechecks on its own; only the
        // product invariant "rules do not consume interpretation conclusions"
        // rejects it.
        premises: vec![1],
        bindings: Vec::new(),
        sources: rule.sources.iter().map(Source::from).collect(),
        applicability: unscoped_applicability(),
    });
    cert.root = Some(2);
    let error = reject(&cert);
    assert!(error.contains("规则不消费解释结论"), "{error}");
}

#[test]
fn an_interpretation_cannot_consume_another_interpretation() {
    let lib = load();
    let mut cert = certificate(&lib);
    cert.interpretations = vec![interpretation(&lib, "i1"), interpretation(&lib, "i4")];
    cert.nodes = vec![
        Node::Assumption { assumption: 0 },
        Node::InterpretationApplication {
            interpretation: 0,
            premise: 0,
            conclusion: cert_expr("Q"),
        },
        // `i4` reads `Q`, which only `i1`'s application licenses: an
        // interpretation chain the reasoner can never produce.
        Node::InterpretationApplication {
            interpretation: 1,
            premise: 1,
            conclusion: cert_expr("R"),
        },
    ];
    cert.root = Some(2);
    let error = reject(&cert);
    assert!(error.contains("禁止解释链"), "{error}");
}
