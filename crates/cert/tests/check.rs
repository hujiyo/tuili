//! Direct certificate-checker tests.
//!
//! Every certificate here is constructed by hand from the certificate model.
//! The reasoner is not used, and no derivation is converted into a
//! certificate: the checker is tested on its own contract.

use std_deduce_cert::{
    check, Assumption, Binding, CertExpr, Certificate, CheckError, CheckReport, Conflict,
    FormatVersion, Node, ObligationKind, OpenObligation, Provenance, Resolution, Side,
};
use std_deduce_kernel::Env;
use std_deduce_lang::Library;

const THEORY: &str = r#"
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
  source 测试 一
"#;

/// The same rule as `THEORY`, plus an environment axiom that proves its
/// `unless` condition. A certificate may omit the axiom's node; the checker
/// must not.
const AXIOM_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
obj 张三 : 公民

axiom 无辜事实 : 无辜 张三

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source 测试 一
"#;

/// Rules whose premise binder (`premise h : ...`) is referenced by a later
/// premise or by an `unless`.
const DEPENDENT_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
obj 张三 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖阻断 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 违法 张三

rule 依赖前提 :
  premise h : 侵占 张三
  premise e : 佐证 h
  conclude 违法 张三
"#;

fn env_from(name: &str, source: &str) -> Env {
    let mut library = Library::new();
    library.load(name, source).expect("test theory loads");
    library.env
}

fn env() -> Env {
    env_from("cert-check", THEORY)
}

fn axiom_env() -> Env {
    env_from("cert-check-axiom", AXIOM_THEORY)
}

fn dependent_env() -> Env {
    env_from("cert-check-dependent", DEPENDENT_THEORY)
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

fn premise(proposition: CertExpr) -> Assumption {
    Assumption {
        proposition,
        sources: Vec::new(),
        label: None,
    }
}

fn assumption_node(assumption: usize) -> Node {
    Node::Assumption { assumption }
}

fn rule_node(conclusion: CertExpr, premises: Vec<usize>, bindings: Vec<(&str, CertExpr)>) -> Node {
    rule_node_for("r", conclusion, premises, bindings)
}

fn rule_node_for(
    rule: &str,
    conclusion: CertExpr,
    premises: Vec<usize>,
    bindings: Vec<(&str, CertExpr)>,
) -> Node {
    Node::RuleApplication {
        rule: rule.to_owned(),
        conclusion,
        premises,
        bindings: bindings
            .into_iter()
            .map(|(parameter, value)| Binding {
                parameter: parameter.to_owned(),
                value,
            })
            .collect(),
        sources: Vec::new(),
    }
}

fn conflict(left: CertExpr, right: CertExpr, resolution: Resolution) -> Conflict {
    Conflict {
        left,
        right,
        left_by: Provenance::Rules {
            rules: vec!["r".to_owned()],
        },
        right_by: Provenance::Rules {
            rules: vec!["r".to_owned()],
        },
        resolution,
    }
}

fn gap_node(proposition: CertExpr) -> Node {
    Node::Gap {
        proposition,
        candidates: Vec::new(),
        note: None,
    }
}

fn certificate(assumptions: Vec<Assumption>, nodes: Vec<Node>, root: Option<usize>) -> Certificate {
    Certificate {
        format_version: FormatVersion::CURRENT,
        assumptions,
        nodes,
        root,
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Default::default(),
    }
}

fn legal_certificate() -> Certificate {
    certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
        ],
        Some(1),
    )
}

fn reject(cert: &Certificate) -> CheckError {
    check(&env(), cert).expect_err("certificate must be rejected")
}

fn reject_at(cert: &Certificate, node: usize) -> CheckError {
    let error = reject(cert);
    assert_eq!(error.node, Some(node), "{error}");
    error
}

#[test]
fn legal_certificate_passes() {
    let report = check(&env(), &legal_certificate()).expect("legal certificate passes");
    assert_eq!(
        report,
        CheckReport {
            root_proved: true,
            root_is_assumption: false,
            assumption_count: 1,
            conflict_resolved: false,
            requires_human: false,
            priority_sources_checked: false,
            nodes_checked: 2,
        }
    );
}

#[test]
fn assumption_root_is_a_conditional_proof() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![assumption_node(0)],
        Some(0),
    );
    let report = check(&env(), &cert).expect("an assumption root is a legal proof");
    assert_eq!(
        report,
        CheckReport {
            root_proved: true,
            root_is_assumption: true,
            assumption_count: 1,
            conflict_resolved: false,
            requires_human: false,
            priority_sources_checked: false,
            nodes_checked: 1,
        }
    );
}

#[test]
fn premise_count_mismatch_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(
        atom("违法", "张三"),
        Vec::new(),
        vec![("p", constant("张三"))],
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("有 1 个前提"), "{error}");
}

#[test]
fn extra_premise_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(
        atom("违法", "张三"),
        vec![0, 0],
        vec![("p", constant("张三"))],
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("本步引用了 2 个节点"), "{error}");
}

#[test]
fn out_of_range_premise_node_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(atom("违法", "张三"), vec![7], vec![("p", constant("张三"))]);
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("越界"), "{error}");
}

#[test]
fn forward_premise_reference_is_rejected() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            rule_node(atom("违法", "张三"), vec![1], vec![("p", constant("张三"))]),
            assumption_node(0),
        ],
        Some(0),
    );
    let error = reject_at(&cert, 0);
    assert!(error.message.contains("之前的节点"), "{error}");
}

#[test]
fn unknown_rule_is_rejected() {
    let mut cert = legal_certificate();
    let Node::RuleApplication { rule, .. } = &mut cert.nodes[1] else {
        panic!("node 1 is a rule application");
    };
    *rule = "不存在".to_owned();
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("未知规则"), "{error}");
}

#[test]
fn non_rule_declaration_is_rejected() {
    let mut cert = legal_certificate();
    let Node::RuleApplication { rule, .. } = &mut cert.nodes[1] else {
        panic!("node 1 is a rule application");
    };
    *rule = "侵占".to_owned();
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("不是规则"), "{error}");
}

#[test]
fn missing_binding_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(atom("违法", "张三"), vec![0], Vec::new());
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("没有绑定"), "{error}");
}

#[test]
fn unknown_binding_parameter_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(
        atom("违法", "张三"),
        vec![0],
        vec![("p", constant("张三")), ("q", constant("李四"))],
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("不是规则 `r` 的参数"), "{error}");
}

#[test]
fn duplicate_binding_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(
        atom("违法", "张三"),
        vec![0],
        vec![("p", constant("张三")), ("p", constant("李四"))],
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("重复绑定"), "{error}");
}

#[test]
fn unclosed_binding_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(
        atom("违法", "张三"),
        vec![0],
        vec![("p", CertExpr::Var { index: 0 })],
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("不是闭合项"), "{error}");
}

#[test]
fn binding_drift_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(atom("违法", "李四"), vec![0], vec![("p", constant("李四"))]);
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("第 1 个前提实例"), "{error}");
}

#[test]
fn conclusion_mismatch_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(atom("违法", "李四"), vec![0], vec![("p", constant("张三"))]);
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("实例结论"), "{error}");
}

#[test]
fn proved_unless_condition_is_rejected() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三")), premise(atom("无辜", "张三"))],
        vec![
            assumption_node(0),
            assumption_node(1),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
        ],
        Some(2),
    );
    let error = reject_at(&cert, 2);
    assert!(error.message.contains("阻断条件"), "{error}");
}

#[test]
fn unless_proved_later_in_the_certificate_still_blocks() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三")), premise(atom("无辜", "张三"))],
        vec![
            assumption_node(0),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
            assumption_node(1),
        ],
        Some(1),
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("阻断条件"), "{error}");
}

#[test]
fn environment_axiom_blocks_unless_when_the_certificate_omits_its_node() {
    // The same certificate passes when the axiom is absent: only the trimmed
    // proof differs, the environment fact is what the step must see.
    let cert = legal_certificate();
    check(&env(), &cert).expect("without the axiom the certificate passes");

    let error =
        check(&axiom_env(), &cert).expect_err("a trimmed certificate must not drop the blocker");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("阻断条件"), "{error}");
    assert!(error.message.contains("无辜"), "{error}");
}

#[test]
fn unless_that_depends_on_a_premise_binder_is_rejected() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            rule_node_for("依赖阻断", atom("违法", "张三"), vec![0], Vec::new()),
        ],
        Some(1),
    );
    let error = check(&dependent_env(), &cert)
        .expect_err("a blocker that mentions a premise binder is not supported");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("依赖前提暂不支持"), "{error}");
}

#[test]
fn a_later_premise_that_depends_on_a_premise_binder_is_rejected() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三")), premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            assumption_node(1),
            rule_node_for("依赖前提", atom("违法", "张三"), vec![0, 1], Vec::new()),
        ],
        Some(2),
    );
    let error = check(&dependent_env(), &cert)
        .expect_err("a premise that mentions a premise binder is not supported");
    assert_eq!(error.node, Some(2), "{error}");
    assert!(error.message.contains("依赖前提暂不支持"), "{error}");
}

#[test]
fn gap_cannot_be_a_premise() {
    let cert = certificate(
        Vec::new(),
        vec![
            gap_node(atom("侵占", "张三")),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
        ],
        Some(1),
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("缺口"), "{error}");
}

#[test]
fn root_index_out_of_range_is_rejected() {
    let mut cert = legal_certificate();
    cert.root = Some(9);
    let error = reject_at(&cert, 9);
    assert!(error.message.contains("根节点索引越界"), "{error}");
}

#[test]
fn root_may_be_a_gap_and_is_not_proved() {
    let cert = certificate(Vec::new(), vec![gap_node(atom("侵占", "张三"))], Some(0));
    let report = check(&env(), &cert).expect("a gap-only certificate is well-formed");
    assert_eq!(
        report,
        CheckReport {
            root_proved: false,
            root_is_assumption: false,
            assumption_count: 0,
            conflict_resolved: false,
            requires_human: false,
            priority_sources_checked: false,
            nodes_checked: 1,
        }
    );
}

#[test]
fn root_in_an_unresolved_conflict_is_rejected() {
    let mut cert = legal_certificate();
    cert.conflicts.push(conflict(
        atom("违法", "张三"),
        atom("无辜", "张三"),
        Resolution::Unresolved,
    ));
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("未决状态"), "{error}");
    assert!(error.message.contains("冲突"), "{error}");
}

#[test]
fn root_on_the_losing_side_of_a_resolved_conflict_is_rejected() {
    let mut cert = legal_certificate();
    cert.conflicts.push(conflict(
        atom("违法", "张三"),
        atom("无辜", "张三"),
        Resolution::Defeated {
            winner: Side::Right,
        },
    ));
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("败方"), "{error}");
}

#[test]
fn root_on_the_winning_side_of_a_resolved_conflict_is_reported() {
    let mut cert = legal_certificate();
    cert.conflicts.push(conflict(
        atom("违法", "张三"),
        atom("无辜", "张三"),
        Resolution::Defeated { winner: Side::Left },
    ));
    let report = check(&env(), &cert).expect("a winning root is allowed");
    assert!(report.root_proved);
    assert!(report.conflict_resolved);
    assert!(
        !report.priority_sources_checked,
        "the priority source behind the defeat is not validated"
    );
}

#[test]
fn an_unresolved_conflict_about_another_proposition_does_not_reject_the_root() {
    let mut cert = legal_certificate();
    cert.conflicts.push(conflict(
        atom("侵占", "李四"),
        atom("无辜", "李四"),
        Resolution::Unresolved,
    ));
    let report = check(&env(), &cert).expect("only the root's conflicts are adjudicated");
    assert!(!report.conflict_resolved);
}

#[test]
fn open_obligations_do_not_fail_but_require_human() {
    let mut cert = legal_certificate();
    cert.open_obligations.push(OpenObligation {
        id: "ob-1".to_owned(),
        kind: ObligationKind::MissingSource,
        description: "缺少来源".to_owned(),
        nodes: vec![1],
    });
    let report = check(&env(), &cert).expect("open obligations do not fail the check");
    assert!(report.root_proved);
    assert!(report.requires_human);
}

#[test]
fn missing_root_is_not_proved() {
    let mut cert = legal_certificate();
    cert.root = None;
    let report = check(&env(), &cert).expect("a rootless certificate is well-formed");
    assert!(!report.root_proved);
    assert_eq!(report.nodes_checked, 2);
}

#[test]
fn out_of_range_assumption_index_is_rejected() {
    let cert = certificate(Vec::new(), vec![assumption_node(0)], Some(0));
    let error = reject_at(&cert, 0);
    assert!(error.message.contains("不存在的假设"), "{error}");
}

#[test]
fn assumption_must_be_a_proposition() {
    let cert = certificate(
        vec![premise(constant("侵占"))],
        vec![assumption_node(0)],
        Some(0),
    );
    let error = reject_at(&cert, 0);
    assert!(error.message.contains("假设不是命题"), "{error}");
}
