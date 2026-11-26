//! Certificate-level arithmetic: the `num` expression, the recorded `computed`
//! form of a rule step, and the checker's recomputation of both.
//!
//! The certificates here are built by hand, so the checker is tested on its own
//! contract rather than on the reasoner's output. The end-to-end path (a
//! generated certificate, a tampered copy, the CLI) is tested in
//! `crates/cli/tests/arithmetic.rs`.

use std_deduce_cert::{
    check, expression_key, kernel_proof, ApplicabilityBasis, ApplicabilityReason,
    ApplicabilityReasonKind, ApplicabilityVerdict, Assumption, Binding, CertExpr, Certificate,
    EnvironmentIdentity, EnvironmentRecord, Explicit, FactIdentity, FormatVersion, Node,
    RuleApplicability,
};
use std_deduce_kernel::Env;
use std_deduce_lang::Library;

/// The rule that adds two amounts. `a + b` is the built-in `add`. The second
/// rule concludes a proposition the premises already give, so its instance
/// contains no arithmetic and may omit the `computed` record.
const THEORY: &str = r#"
sort 人
def 金额 : Type := Int
pred 医疗费 : 人 → 金额 → Prop
pred 误工费 : 人 → 金额 → Prop
pred 账单 : 人 → 金额 → Prop
pred 合计 : 人 → 金额 → Prop
obj 甲 : 人
rule 赔偿合计 :
  params p : 人, a : 金额, b : 金额
  premise 医疗费 p a
  premise 误工费 p b
  conclude 合计 p (a + b)
  source text "测试" locator "夹具"
rule 账单合计 :
  params p : 人, x : 金额
  premise 账单 p x
  conclude 合计 p x
  source text "测试" locator "夹具二"
"#;

fn env() -> Env {
    let mut library = Library::new();
    library
        .load("cert-arithmetic", THEORY)
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

fn app(function: CertExpr, arg: CertExpr) -> CertExpr {
    CertExpr::App {
        func: Box::new(function),
        arg: Box::new(arg),
    }
}

fn apply(function: &str, arguments: Vec<CertExpr>) -> CertExpr {
    arguments.into_iter().fold(constant(function), app)
}

/// `医疗费 甲 3000`, `误工费 甲 2000`, `合计 甲 5000`.
fn amount(predicate: &str, value: i64) -> CertExpr {
    apply(predicate, vec![constant("甲"), num(value)])
}

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

fn bindings(values: Vec<(&str, CertExpr)>) -> Vec<Binding> {
    values
        .into_iter()
        .map(|(parameter, value)| Binding {
            parameter: parameter.to_owned(),
            value,
        })
        .collect()
}

/// A rule step deriving `合计 甲 5000` from the two amount facts, with the
/// arithmetic step recorded as `合计 甲 (add 3000 2000)`.
fn rule_node(conclusion: CertExpr, computed: Option<CertExpr>) -> Node {
    Node::RuleApplication {
        guards: Vec::new(),
        rule: "赔偿合计".to_owned(),
        conclusion,
        computed,
        premises: vec![0, 1],
        bindings: bindings(vec![
            ("p", constant("甲")),
            ("a", num(3000)),
            ("b", num(2000)),
        ]),
        sources: Vec::new(),
        applicability: unscoped_applicability(),
    }
}

/// The raw instance form: `合计 甲 (add 3000 2000)`.
fn raw_total() -> CertExpr {
    apply(
        "合计",
        vec![constant("甲"), apply("add", vec![num(3000), num(2000)])],
    )
}

fn certificate(node: Node) -> Certificate {
    certificate_with(
        vec![
            assumption(amount("医疗费", 3000)),
            assumption(amount("误工费", 2000)),
        ],
        node,
    )
}

fn certificate_with(assumptions: Vec<Assumption>, node: Node) -> Certificate {
    Certificate {
        format_version: FormatVersion::CURRENT,
        environment: EnvironmentIdentity::Recorded(EnvironmentRecord::empty()),
        assumptions,
        interpretations: Vec::new(),
        nodes: vec![
            Node::Assumption { assumption: 0 },
            Node::Assumption { assumption: 1 },
            node,
        ],
        root: Some(2),
        alternatives: Vec::new(),
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Default::default(),
    }
}

fn legal_certificate() -> Certificate {
    certificate(rule_node(amount("合计", 5000), Some(raw_total())))
}

fn reject(cert: &Certificate) -> String {
    let error = check(&env(), cert).expect_err("the certificate must be rejected");
    assert_eq!(
        error.node,
        Some(2),
        "the arithmetic step's node must be named: {error}"
    );
    error.message
}

#[test]
fn a_recorded_arithmetic_step_is_accepted() {
    let cert = legal_certificate();
    let report = check(&env(), &cert).expect("the arithmetic step is legal");
    assert!(report.root_proved);
    // The kernel layer independently accepts the evaluated conclusion.
    let report = kernel_proof(&env(), &cert).expect("the kernel accepts the step");
    assert!(report.root_proved);
    assert_eq!(report.steps.len(), 1);
}

#[test]
fn a_changed_number_in_the_conclusion_is_rejected() {
    let cert = certificate(rule_node(amount("合计", 9000), Some(raw_total())));
    let message = reject(&cert);
    assert!(message.contains("9000"), "{message}");
    assert!(message.contains("add 3000 2000"), "{message}");
}

#[test]
fn a_swapped_operation_is_rejected() {
    // `mul 3000 2000` is 6000000, so the recorded conclusion 5000 is wrong; the
    // structural comparison with the rule's own conclusion catches the swap
    // even if the numbers were adjusted to fit.
    let computed = apply(
        "合计",
        vec![constant("甲"), apply("mul", vec![num(3000), num(2000)])],
    );
    let cert = certificate(rule_node(amount("合计", 6000000), Some(computed)));
    let message = reject(&cert);
    assert!(message.contains("算术步骤与规则不一致"), "{message}");
    assert!(message.contains("mul 3000 2000"), "{message}");
    assert!(message.contains("add 3000 2000"), "{message}");
}

#[test]
fn a_changed_operand_in_the_computed_form_is_rejected() {
    let computed = apply(
        "合计",
        vec![constant("甲"), apply("add", vec![num(3001), num(2000)])],
    );
    let cert = certificate(rule_node(amount("合计", 5001), Some(computed)));
    let message = reject(&cert);
    assert!(message.contains("add 3001 2000"), "{message}");
    assert!(message.contains("add 3000 2000"), "{message}");
}

#[test]
fn a_computed_form_that_is_not_a_proposition_is_rejected() {
    // The evaluated form must be the closed instance; a bare literal is not.
    let cert = certificate(rule_node(amount("合计", 5000), Some(num(5000))));
    let message = reject(&cert);
    assert!(message.contains("算术步骤与规则不一致"), "{message}");
}

#[test]
fn recorded_bindings_must_match_the_cited_premises() {
    // The premise `医疗费 甲 a` is proved by `医疗费 甲 3000`, so binding
    // `a = 4000` is not this instance: the arithmetic step would compute from a
    // value the premises do not give.
    let node = Node::RuleApplication {
        guards: Vec::new(),
        rule: "赔偿合计".to_owned(),
        conclusion: amount("合计", 6000),
        computed: Some(apply(
            "合计",
            vec![constant("甲"), apply("add", vec![num(4000), num(2000)])],
        )),
        premises: vec![0, 1],
        bindings: bindings(vec![
            ("p", constant("甲")),
            ("a", num(4000)),
            ("b", num(2000)),
        ]),
        sources: Vec::new(),
        applicability: unscoped_applicability(),
    };
    let cert = certificate(node);
    let message = reject(&cert);
    assert!(message.contains("医疗费 甲 4000"), "{message}");
}

#[test]
fn an_arithmetic_step_without_the_computed_form_is_rejected() {
    // The instance really computes `3000 + 2000`; leaving the pre-evaluation
    // form out would leave the recorded `5000` as the only trace of the
    // computation, so the field is required here. The message says exactly
    // that, and the node is named.
    let error = check(&env(), &certificate(rule_node(amount("合计", 5000), None)))
        .expect_err("an unrecorded arithmetic step must be refused");
    assert_eq!(error.node, Some(2), "{error}");
    assert!(
        error.message.contains("含可计算的算术表达式"),
        "{}",
        error.message
    );
    assert!(
        error.message.contains("没有记录未求值形式"),
        "{}",
        error.message
    );
}

#[test]
fn a_step_without_arithmetic_may_omit_the_computed_form() {
    // `账单合计` only passes a value through: `合计 p x` is not an arithmetic
    // expression, so its instance does not change under evaluation and the
    // field stays optional. The checker still rebuilds the instance from the
    // rule and the bindings, so nothing is taken on trust.
    let node = Node::RuleApplication {
        guards: Vec::new(),
        rule: "账单合计".to_owned(),
        conclusion: amount("合计", 5000),
        computed: None,
        premises: vec![0],
        bindings: bindings(vec![("p", constant("甲")), ("x", num(5000))]),
        sources: Vec::new(),
        applicability: unscoped_applicability(),
    };
    let cert = Certificate {
        format_version: FormatVersion::CURRENT,
        environment: EnvironmentIdentity::Recorded(EnvironmentRecord::empty()),
        assumptions: vec![assumption(amount("账单", 5000))],
        interpretations: Vec::new(),
        nodes: vec![Node::Assumption { assumption: 0 }, node],
        root: Some(1),
        alternatives: Vec::new(),
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Default::default(),
    };
    check(&env(), &cert).expect("a step without arithmetic may omit `computed`");
    kernel_proof(&env(), &cert).expect("the kernel accepts the step");

    // The same rule with a wrong conclusion is still refused.
    let mut wrong = cert.clone();
    if let Node::RuleApplication { conclusion, .. } = &mut wrong.nodes[1] {
        *conclusion = amount("合计", 4000);
    }
    let error = check(&env(), &wrong).expect_err("a wrong conclusion is still refused");
    assert_eq!(error.node, Some(1), "{error}");
}

#[test]
fn a_num_literal_serializes_as_an_exact_integer() {
    let cert = legal_certificate();
    let json = cert.to_json().expect("the certificate serializes");
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
    let conclusion = &parsed["nodes"][2]["conclusion"];
    assert_eq!(conclusion["kind"], "app", "{conclusion}");
    let amount_argument = &conclusion["arg"];
    assert_eq!(amount_argument["kind"], "num", "{amount_argument}");
    assert_eq!(amount_argument["value"], 5000, "{amount_argument}");
    assert_eq!(parsed["format_version"], 11);
    let round_trip = Certificate::from_json(&json).expect("an exported certificate parses back");
    assert_eq!(round_trip, cert);
}

#[test]
fn a_num_literal_keeps_its_sign_through_json() {
    let expression = CertExpr::Num { value: -3000 };
    let json = serde_json::to_string(&expression).expect("a literal serializes");
    assert_eq!(json, r#"{"kind":"num","value":-3000}"#);
    let parsed: CertExpr = serde_json::from_str(&json).expect("a literal parses");
    assert_eq!(parsed, expression);
}

#[test]
fn an_out_of_range_or_malformed_num_is_rejected() {
    let too_large: Result<CertExpr, _> =
        serde_json::from_str(r#"{"kind":"num","value":9223372036854775808}"#);
    assert!(too_large.is_err(), "an i64 overflow must be refused");
    let unknown_field: Result<CertExpr, _> =
        serde_json::from_str(r#"{"kind":"num","value":1,"float":1.5}"#);
    assert!(unknown_field.is_err(), "unknown fields are still refused");
    let missing_value: Result<CertExpr, _> = serde_json::from_str(r#"{"kind":"num"}"#);
    assert!(missing_value.is_err(), "the value field is mandatory");
    // There is no float shape: a float value never parses.
    let float: Result<CertExpr, _> = serde_json::from_str(r#"{"kind":"num","value":1.5}"#);
    assert!(float.is_err(), "a literal is an integer, not a float");
}

#[test]
fn a_literal_key_is_distinct_from_a_same_named_constant() {
    use std_deduce_kernel::Expr;
    assert_ne!(
        expression_key(&Expr::Num(3000)),
        expression_key(&Expr::constant("3000"))
    );
    assert_ne!(
        expression_key(&Expr::Num(5)),
        expression_key(&Expr::Num(-5))
    );
    assert_eq!(expression_key(&Expr::Num(5)), expression_key(&Expr::Num(5)));
}

#[test]
fn a_rule_step_without_arithmetic_records_no_computed_field() {
    // A non-arithmetic certificate keeps exactly its old JSON shape: the field
    // is omitted rather than written as `null`, so v11 output stays stable for
    // cases that compute nothing.
    let cert = certificate(Node::RuleApplication {
        guards: Vec::new(),
        rule: "赔偿合计".to_owned(),
        conclusion: amount("合计", 5000),
        computed: None,
        premises: vec![0, 1],
        bindings: bindings(vec![
            ("p", constant("甲")),
            ("a", num(3000)),
            ("b", num(2000)),
        ]),
        sources: Vec::new(),
        applicability: unscoped_applicability(),
    });
    let json = cert.to_json().expect("the certificate serializes");
    assert!(!json.contains("computed"), "{json}");
}

#[test]
fn an_overflowing_computed_step_is_rejected_instead_of_wrapping() {
    // `add i64::MAX 1` cannot be evaluated, so neither the logical layer nor
    // the kernel may accept it. The premises really do provide the two huge
    // numbers, so the step's arithmetic — not the binding — is what overflows.
    let node = Node::RuleApplication {
        guards: Vec::new(),
        rule: "赔偿合计".to_owned(),
        conclusion: amount("合计", 0),
        computed: Some(apply(
            "合计",
            vec![constant("甲"), apply("add", vec![num(i64::MAX), num(1)])],
        )),
        premises: vec![0, 1],
        bindings: bindings(vec![
            ("p", constant("甲")),
            ("a", num(i64::MAX)),
            ("b", num(1)),
        ]),
        sources: Vec::new(),
        applicability: unscoped_applicability(),
    };
    let cert = certificate_with(
        vec![
            assumption(amount("医疗费", i64::MAX)),
            assumption(amount("误工费", 1)),
        ],
        node,
    );
    let error = check(&env(), &cert).expect_err("an overflowing step cannot be checked");
    assert_eq!(error.node, Some(2), "{error}");
    assert!(error.message.contains("溢出"), "{}", error.message);
}

#[test]
fn a_computed_form_without_arithmetic_is_rejected() {
    // `账单合计` only passes a value through: evaluating its instance changes
    // nothing, so a `computed` of the same proposition would print
    // `计算：X = X` and claim a computation the rule never performed.
    let node = Node::RuleApplication {
        rule: "账单合计".to_owned(),
        conclusion: amount("合计", 5000),
        computed: Some(amount("合计", 5000)),
        premises: vec![0],
        bindings: bindings(vec![("p", constant("甲")), ("x", num(5000))]),
        guards: Vec::new(),
        sources: Vec::new(),
        applicability: unscoped_applicability(),
    };
    let cert = Certificate {
        format_version: FormatVersion::CURRENT,
        environment: EnvironmentIdentity::Recorded(EnvironmentRecord::empty()),
        assumptions: vec![assumption(amount("账单", 5000))],
        interpretations: Vec::new(),
        nodes: vec![Node::Assumption { assumption: 0 }, node],
        root: Some(1),
        alternatives: Vec::new(),
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Default::default(),
    };
    let error = check(&env(), &cert).expect_err("the invented computation must be refused");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(
        error.message.contains("该步没有算术，不应记录计算形式"),
        "{}",
        error.message
    );

    // An arithmetic step is no exception when both forms are the same term:
    // then the conclusion was recorded un-evaluated, and no computation
    // separates the two.
    let cert = certificate(rule_node(raw_total(), Some(raw_total())));
    let error = check(&env(), &cert).expect_err("the same form on both sides is refused");
    assert_eq!(error.node, Some(2), "{error}");
    assert!(
        error.message.contains("与计算前形式相同"),
        "{}",
        error.message
    );
}
