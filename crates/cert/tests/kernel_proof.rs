//! Direct tests for kernel proof terms built from certificates.
//!
//! Every certificate here is constructed by hand from the certificate model.
//! The reasoner is not used: the kernel is the authority on whether a step's
//! proof term has the claimed conclusion.

use std_deduce_cert::{
    check as cert_check, kernel_proof, ApplicabilityBasis, ApplicabilityReason,
    ApplicabilityReasonKind, ApplicabilityVerdict, Assumption, Binding, CertExpr, Certificate,
    EnvironmentIdentity, Explicit, FactIdentity, FormatVersion, Node, RuleApplicability,
};
use std_deduce_kernel::check::check as kernel_check;
use std_deduce_kernel::norm::spine;
use std_deduce_kernel::{Ctx, Env, Expr};
use std_deduce_lang::Library;

const BASIC: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
obj 张三 : 公民
obj 李四 : 公民

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "一"
"#;

const TWO_PREMISES: &str = r#"
sort 公民
sort 证件
pred 持有 : 公民 → 证件 → Prop
pred 有效 : 证件 → Prop
pred 有资格 : 公民 → Prop
obj 张三 : 公民
obj 身份证 : 证件

rule 资格 :
  params p : 公民, z : 证件
  premise 持有 p z
  premise 有效 z
  conclude 有资格 p
  source text "测试" locator "二"
"#;

fn env(source: &str) -> Env {
    let mut library = Library::new();
    library
        .load("cert-kernel-proof", source)
        .expect("test theory loads");
    library.env
}

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

fn binary(predicate: &str, left: &str, right: &str) -> CertExpr {
    app(atom(predicate, left), constant(right))
}

fn premise(proposition: CertExpr) -> Assumption {
    Assumption {
        proposition,
        identity: FactIdentity::UserAsserted,
        sources: Vec::new(),
        label: None,
        occurred_at: Explicit::none(),
        occurred_in: Explicit::none(),
    }
}

/// The record of a rule declared without any scope: unchecked because there is
/// nothing to judge, with an empty basis.
fn unscoped_applicability() -> Box<RuleApplicability> {
    Box::new(RuleApplicability {
        verdict: ApplicabilityVerdict::Unchecked,
        basis: ApplicabilityBasis::default(),
        reason: Explicit::some(ApplicabilityReason::new(
            ApplicabilityReasonKind::RuleHasNoScope,
        )),
    })
}

fn assumption_node(assumption: usize) -> Node {
    Node::Assumption { assumption }
}

fn bindings(entries: Vec<(&str, CertExpr)>) -> Vec<Binding> {
    entries
        .into_iter()
        .map(|(parameter, value)| Binding {
            parameter: parameter.to_owned(),
            value,
        })
        .collect()
}

fn rule_node(
    rule: &str,
    conclusion: CertExpr,
    premises: Vec<usize>,
    entries: Vec<(&str, CertExpr)>,
) -> Node {
    Node::RuleApplication {
        rule: rule.to_owned(),
        conclusion,
        premises,
        bindings: bindings(entries),
        sources: Vec::new(),
        applicability: unscoped_applicability(),
    }
}

fn gap_node(proposition: CertExpr) -> Node {
    Node::Gap {
        proposition,
        axiom_candidates: Vec::new(),
        candidates: Vec::new(),
        note: None,
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

fn assumption_ctx(cert: &Certificate) -> Ctx {
    let mut ctx = Ctx::new();
    for assumption in &cert.assumptions {
        ctx.push(None, Expr::from(&assumption.proposition));
    }
    ctx
}

fn basic_certificate() -> Certificate {
    certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            rule_node(
                "r",
                atom("违法", "张三"),
                vec![0],
                vec![("p", constant("张三"))],
            ),
        ],
        Some(1),
    )
}

#[test]
fn a_legal_certificate_has_a_kernel_checked_root() {
    let env = env(BASIC);
    let cert = basic_certificate();
    let report = kernel_proof(&env, &cert).expect("the legal certificate builds");

    assert!(report.root_proved);
    assert_eq!(report.steps.len(), 1);
    let step = &report.steps[0];
    assert_eq!(step.node, 1);
    assert_eq!(step.rule, "r");
    assert!(step.checked);

    let root = report
        .root_term
        .as_ref()
        .expect("the root has a proof term");
    kernel_check(
        &env,
        &assumption_ctx(&cert),
        root,
        &Expr::from(&atom("违法", "张三")),
    )
    .expect("the root term checks at the conclusion");

    let logical = cert_check(&env, &cert).expect("the logical checker agrees");
    assert!(logical.root_proved);
}

#[test]
fn a_tampered_binding_fails_the_kernel_step() {
    let env = env(BASIC);
    let mut cert = basic_certificate();
    cert.nodes[1] = rule_node(
        "r",
        atom("违法", "张三"),
        vec![0],
        vec![("p", constant("李四"))],
    );

    let error = kernel_proof(&env, &cert).expect_err("binding drift must fail");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("内核"), "{error}");
    assert!(
        cert_check(&env, &cert).is_err(),
        "the logical checker rejects the same drift"
    );
}

#[test]
fn a_gap_root_has_no_proof_term() {
    let env = env(BASIC);
    let cert = certificate(Vec::new(), vec![gap_node(atom("侵占", "张三"))], Some(0));

    let report = kernel_proof(&env, &cert).expect("a gap is not an error");
    assert!(!report.root_proved);
    assert!(
        report.root_term.is_none(),
        "no proof may be invented for a gap"
    );
    assert!(report.steps.is_empty());
}

#[test]
fn an_established_unless_blocker_is_outside_the_kernel_proof() {
    let env = env(BASIC);
    // Both the premise and the blocker are assumed. The monotone proof term is
    // well-typed because `unless` is not part of the rule's kernel type.
    let cert = certificate(
        vec![premise(atom("侵占", "张三")), premise(atom("无辜", "张三"))],
        vec![
            assumption_node(0),
            assumption_node(1),
            rule_node(
                "r",
                atom("违法", "张三"),
                vec![0],
                vec![("p", constant("张三"))],
            ),
        ],
        Some(2),
    );

    let report = kernel_proof(&env, &cert).expect("the monotone skeleton is well-typed");
    assert!(report.root_proved);
    assert!(report.steps[0].checked);

    // The kernel report does not establish the legal conclusion: the
    // independent checker rejects the step because the blocker is proved.
    // Side-condition checking is the separate layer this test leaves intact.
    let logical = cert_check(&env, &cert).expect_err("the established blocker must be rejected");
    assert_eq!(logical.node, Some(2), "{logical}");
    assert!(logical.message.contains("阻断条件"), "{logical}");
}

#[test]
fn two_premises_are_passed_after_the_parameters() {
    let env = env(TWO_PREMISES);
    let cert = certificate(
        vec![
            premise(binary("持有", "张三", "身份证")),
            premise(atom("有效", "身份证")),
        ],
        vec![
            assumption_node(0),
            assumption_node(1),
            rule_node(
                "资格",
                atom("有资格", "张三"),
                vec![0, 1],
                vec![("p", constant("张三")), ("z", constant("身份证"))],
            ),
        ],
        Some(2),
    );

    let report = kernel_proof(&env, &cert).expect("both premises are accepted");
    assert!(report.root_proved);
    let step = &report.steps[0];

    let (head, arguments) = spine(&step.term);
    assert_eq!(head, &Expr::constant("资格"));
    assert_eq!(
        arguments.len(),
        4,
        "two parameters and two premise proofs are applied"
    );
    // Arguments go parameters first, then premises in the rule's own order.
    assert_eq!(arguments[2], &Expr::var(1), "the first premise proof");
    assert_eq!(arguments[3], &Expr::var(0), "the second premise proof");
    kernel_check(
        &env,
        &assumption_ctx(&cert),
        &step.term,
        &Expr::from(&atom("有资格", "张三")),
    )
    .expect("the whole term checks at the conclusion");
}

#[test]
fn a_rule_conclusion_that_is_not_a_proposition_is_located() {
    let env = env(BASIC);
    let mut cert = basic_certificate();
    // `违法` alone is a function `公民 → Prop`, not a proposition.
    cert.nodes[1] = rule_node(
        "r",
        constant("违法"),
        vec![0],
        vec![("p", constant("张三"))],
    );

    let error = kernel_proof(&env, &cert).expect_err("a non-proposition conclusion is rejected");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("结论不是命题"), "{error}");
}

#[test]
fn a_missing_binding_is_located_before_any_term_is_built() {
    let env = env(BASIC);
    let mut cert = basic_certificate();
    cert.nodes[1] = rule_node("r", atom("违法", "张三"), vec![0], Vec::new());

    let error = kernel_proof(&env, &cert).expect_err("an incomplete instance is rejected");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("没有绑定"), "{error}");
}

#[test]
fn a_gap_cannot_be_a_rule_premise() {
    let env = env(BASIC);
    let cert = certificate(
        Vec::new(),
        vec![
            gap_node(atom("侵占", "张三")),
            rule_node(
                "r",
                atom("违法", "张三"),
                vec![0],
                vec![("p", constant("张三"))],
            ),
        ],
        Some(1),
    );

    let error = kernel_proof(&env, &cert).expect_err("a gap proves nothing");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("缺口"), "{error}");
}
