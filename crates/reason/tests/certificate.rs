//! Conversion from reasoner derivations to certificates, checked by the
//! independent certificate layer.

use std::path::Path;

use std_deduce_cert as cert;
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::Expr;
use std_deduce_lang::Library;
use std_deduce_reason::{certificate, Derivation, Node as ReasonNode, PriorityOrder, Reasoner};

fn example(name: &str) -> Library {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(name);
    let src =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let mut lib = Library::new();
    lib.load(name, &src)
        .unwrap_or_else(|e| panic!("load {name}: {e}"));
    lib
}

fn load_sources(name: &str, sources: &[(&str, &str)]) -> Library {
    let mut lib = Library::new();
    for (file, src) in sources {
        lib.load(file, src)
            .unwrap_or_else(|e| panic!("load {name} ({file}): {e}"));
    }
    lib
}

/// The same shape the CLI builds: all derived facts, plus a gap node when the
/// goal is unreachable.
fn derive(lib: &Library, goal: &Expr) -> (Derivation, PriorityOrder) {
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    let mut d = r.derivation();
    if r.knows(goal) {
        d.root = r.root_for(goal);
    } else {
        let ex = r.explain(goal).unwrap();
        let id = d.nodes.len();
        d.nodes.push(ReasonNode::Gap {
            prop: goal.clone(),
            candidates: ex.candidates,
            axiom_candidates: ex.axiom_candidates,
            note: ex.note,
        });
        d.root = Some(id);
    }
    (d, r.priority_order())
}

fn constitution_goal() -> Expr {
    Expr::apps(
        Expr::constant("不受侵犯"),
        [Expr::constant("张三"), Expr::constant("甲宅")],
    )
}

#[test]
fn constitution_certificate_round_trips_and_checks() {
    let lib = example("constitution-39.std");
    let (d, order) = derive(&lib, &constitution_goal());
    assert!(d.root.is_some(), "the goal must be derived");

    let certificate = certificate(&lib.env, &d, &order).expect("the derivation converts");
    // The reasoner records no environment; an exported certificate needs one.
    // This test runs against the theory alone, so an empty record is right.
    let certificate = certificate.with_environment(cert::EnvironmentIdentity::none());
    let pretty = certificate.to_json_pretty().unwrap();
    let decoded = cert::Certificate::from_json(&pretty).expect("the JSON round-trips");
    assert_eq!(decoded, certificate);
    assert_eq!(decoded.to_json_pretty().unwrap(), pretty);

    let report = cert::check(&lib.env, &decoded).expect("the certificate checks");
    assert!(report.root_proved);
    assert_eq!(report.nodes_checked, certificate.nodes.len());
}

#[test]
fn gap_certificate_is_valid_but_the_root_is_not_proved() {
    let lib = example("刑法第二十条-基本.std");
    let goal = Expr::apps(Expr::constant("应当负刑事责任"), [Expr::constant("乙行为")]);
    let (d, order) = derive(&lib, &goal);
    let certificate = certificate(&lib.env, &d, &order).expect("the gap derivation converts");

    let root = certificate.root.expect("a gap certificate has a root");
    let cert::Node::Gap {
        proposition,
        candidates,
        ..
    } = &certificate.nodes[root]
    else {
        panic!("the root of an unreachable goal must be a gap");
    };
    assert_eq!(
        proposition,
        &cert::CertExpr::try_from(&goal).unwrap(),
        "the gap keeps the queried proposition"
    );
    assert!(
        candidates
            .iter()
            .any(|c| c.rule == "防卫过当应负刑责" && !c.missing.is_empty()),
        "the candidate rule and its missing premise must survive conversion"
    );
    assert!(
        certificate.open_obligations.iter().any(|obligation| {
            obligation.kind == cert::ObligationKind::MissingPremise
                && obligation.nodes == vec![root]
        }),
        "a gap becomes a MissingPremise obligation: {:?}",
        certificate.open_obligations
    );

    let report = cert::check(&lib.env, &certificate).expect("a gap certificate is well-formed");
    assert!(!report.root_proved);
}

#[test]
fn conflicts_keep_both_sides_provenance_and_resolution() {
    let lib = example("法律位阶-河南种子案-裁决.std");
    let goal = Expr::apps(
        Expr::constant("应适用"),
        [Expr::constant("种子法"), Expr::constant("汝阳种子公司案")],
    );
    let (d, order) = derive(&lib, &goal);
    assert!(!d.conflicts.is_empty(), "the example records a conflict");

    let certificate = certificate(&lib.env, &d, &order).expect("the derivation converts");
    assert_eq!(certificate.conflicts.len(), d.conflicts.len());

    let conflict = &certificate.conflicts[0];
    let cert::Resolution::Defeated { winner, basis } = &conflict.resolution else {
        panic!("the example has an explicit priority, so the conflict is decided");
    };
    let cert::ResolutionBasis::Priority { edges } = basis else {
        panic!("a same-package defeated_by clause decides it, not an assumption");
    };
    assert_eq!(edges.len(), 1, "{edges:?}");
    assert_eq!(edges[0].winner, "位阶决定应适用");
    assert_eq!(edges[0].loser, "主张适用省条例");
    assert!(matches!(
        &edges[0].origin,
        cert::PriorityOrigin::RuleClause {
            declaring_rule,
            clause: cert::PriorityClause::DefeatedBy,
            ..
        } if declaring_rule == "主张适用省条例"
    ));
    let winning = match winner {
        cert::Side::Left => &conflict.left,
        cert::Side::Right => &conflict.right,
    };
    assert_eq!(
        winning,
        &cert::CertExpr::try_from(&goal).unwrap(),
        "the winning side is the proposition the goal asked for"
    );
    assert!(matches!(conflict.left_by, cert::Provenance::Rules { .. }));
    assert!(matches!(conflict.right_by, cert::Provenance::Rules { .. }));
    assert!(
        !certificate
            .open_obligations
            .iter()
            .any(|obligation| obligation.kind == cert::ObligationKind::UnresolvedConflict),
        "a defeated conflict is decided, so it is not an open obligation"
    );

    let report = cert::check(&lib.env, &certificate).expect("the certificate checks");
    assert!(report.root_proved);
    assert!(report.priority_sources_checked);
    assert_eq!(report.priority_edges_checked, 1);
}

#[test]
fn an_unencodable_expression_is_a_clear_error() {
    if usize::BITS <= 32 {
        return;
    }
    let index = u32::MAX as usize + 1;
    let d = Derivation {
        nodes: vec![ReasonNode::Gap {
            prop: Expr::var(index),
            candidates: Vec::new(),
            axiom_candidates: Vec::new(),
            note: None,
        }],
        root: Some(0),
        alternatives: Vec::new(),
        conflicts: Vec::new(),
        interpretations: Vec::new(),
    };
    let env = std_deduce_kernel::Env::new();
    let error = certificate(&env, &d, &PriorityOrder::default())
        .expect_err("the index does not fit the certificate format");
    assert!(error.contains("节点 0"), "{error}");
    assert!(error.contains("缺口命题"), "{error}");
    assert!(error.contains("de Bruijn"), "{error}");
}

// ------------------------------------------------------------ determinism

/// Two independent packages plus an order package, loaded in either order.
const INDEPENDENT_P: &str = r#"
namespace p
sort p.案件
pred p.应适用 : p.案件 → Prop
pred p.不适用 : p.案件 → Prop
pred p.备注 : p.案件 → Prop
obj p.甲案 : p.案件
obj p.乙案 : p.案件
contrary p.应适用 p.不适用
axiom p.事实甲 : p.备注 p.甲案
  source text "案情" locator "一"
axiom p.事实丙 : p.备注 p.乙案
  source text "案情" locator "三"
rule p.alpha :
  conclude p.应适用 p.甲案
  source text "甲法" locator "一"
rule p.beta :
  conclude p.应适用 p.甲案
  source text "乙法" locator "二"
rule p.拒绝 :
  conclude p.不适用 p.甲案
  source text "丙法" locator "三"
"#;

const INDEPENDENT_Q: &str = r#"
namespace q
sort q.申请
pred q.条件 : q.申请 → Prop
pred q.结论 : q.申请 → Prop
obj q.乙 : q.申请
axiom q.事实乙 : q.条件 q.乙
  source text "丁法" locator "四"
rule q.推导 :
  params x : q.申请
  premise q.条件 x
  conclude q.结论 x
  source text "戊法" locator "五"
"#;

const INDEPENDENT_ORDER: &str = r#"
import p
namespace o
priority p.alpha over p.拒绝 source text "上位法" locator "一"
priority p.beta over p.拒绝 source text "上位法" locator "二"
"#;

#[test]
fn certificate_is_identical_when_independent_packages_load_in_a_different_order() {
    let goal = Expr::apps(Expr::constant("p.应适用"), [Expr::constant("p.甲案")]);
    let first = load_sources(
        "order-p-q",
        &[
            ("p.std", INDEPENDENT_P),
            ("q.std", INDEPENDENT_Q),
            ("o.std", INDEPENDENT_ORDER),
        ],
    );
    let second = load_sources(
        "order-q-p",
        &[
            ("q.std", INDEPENDENT_Q),
            ("p.std", INDEPENDENT_P),
            ("o.std", INDEPENDENT_ORDER),
        ],
    );

    let (d1, order1) = derive(&first, &goal);
    let (d2, order2) = derive(&second, &goal);
    let c1 = certificate(&first.env, &d1, &order1).expect("the first derivation converts");
    let c2 = certificate(&second.env, &d2, &order2).expect("the second derivation converts");
    assert_eq!(
        c1, c2,
        "the certificate depends on the order packages loaded in"
    );
    assert_eq!(format!("{c1:?}"), format!("{c2:?}"));

    // Unique witness choice: of two rules concluding the same fact, the first
    // by name is the one the derivation cites.
    let root = c1.root.expect("the goal is derived");
    let cert::Node::RuleApplication { rule, .. } = &c1.nodes[root] else {
        panic!("the goal is proved by a rule application");
    };
    assert_eq!(rule, "p.alpha");

    // Both declared edges cover the winning side, sorted by winner.
    let cert::Resolution::Defeated {
        basis: cert::ResolutionBasis::Priority { edges },
        ..
    } = &c1.conflicts[0].resolution
    else {
        panic!("the declared priorities decide the conflict");
    };
    assert_eq!(edges.len(), 2, "{edges:?}");
    assert_eq!(edges[0].winner, "p.alpha");
    assert_eq!(edges[1].winner, "p.beta");

    let report = cert::check(&first.env, &c1).expect("the certificate checks");
    assert!(report.root_proved);
    assert!(report.priority_sources_checked);
    assert_eq!(report.priority_edges_checked, 2);
    let second_report = cert::check(&second.env, &c2).expect("the certificate checks either way");
    assert_eq!(
        report, second_report,
        "the load order must not change the report"
    );
}

// ------------------------------------------------------------ descriptions

const CYCLE_CASE: &str = r#"
namespace c
sort c.对象
sort c.选项
pred c.值 : c.对象 → c.选项 → Prop
unique c.值 2
obj c.甲 : c.对象
obj c.选A : c.选项
obj c.选B : c.选项
obj c.选C : c.选项
rule c.A :
  conclude c.值 c.甲 c.选A
  source text "甲法" locator "一"
rule c.B :
  conclude c.值 c.甲 c.选B
  source text "乙法" locator "二"
rule c.C :
  conclude c.值 c.甲 c.选C
  source text "丙法" locator "三"
priority c.A over c.B source text "甲法" locator "一"
priority c.B over c.C source text "乙法" locator "二"
priority c.C over c.A source text "丙法" locator "三"
"#;

const ASSUMPTION_CASE: &str = r#"
sort 申请
pred 该批准 : 申请 → Prop
pred 不该批准 : 申请 → Prop
contrary 该批准 不该批准
obj 甲 : 申请
axiom f1 : 该批准 甲
  source text "甲法" locator "一"
axiom f2 : 不该批准 甲
  source text "乙法" locator "二"
"#;

/// The same standoff with both facts recorded as found by a court.
const STRICT_ASSUMPTION_CASE: &str = r#"
sort 申请
pred 该批准 : 申请 → Prop
pred 不该批准 : 申请 → Prop
contrary 该批准 不该批准
obj 甲 : 申请
axiom f1 : 该批准 甲
  identity verified
  source text "甲法" locator "一"
axiom f2 : 不该批准 甲
  identity verified
  source text "乙法" locator "二"
"#;

fn unresolved_obligation(
    certificate: &cert::Certificate,
    conflict: &std_deduce_reason::Conflict,
) -> String {
    let expected_prefix = format!(
        "冲突未决：「{}」与「{}」（",
        print_expr(&conflict.left),
        print_expr(&conflict.right)
    );
    certificate
        .open_obligations
        .iter()
        .find(|obligation| {
            obligation.kind == cert::ObligationKind::UnresolvedConflict
                && obligation.description.starts_with(&expected_prefix)
        })
        .unwrap_or_else(|| {
            panic!(
                "no unresolved-conflict obligation for the conflict: {:?}",
                certificate.open_obligations
            )
        })
        .description
        .clone()
}

#[test]
fn an_unresolved_conflict_obligation_names_why_it_is_unresolved() {
    // No declared priority between two rule-derived conclusions.
    let lib = example("冲突-互补谓词.std");
    let goal = Expr::apps(Expr::constant("批准"), [Expr::constant("甲")]);
    let (d, order) = derive(&lib, &goal);
    let document = certificate(&lib.env, &d, &order).expect("the derivation converts");
    let conflict = d
        .conflicts
        .iter()
        .find(|conflict| {
            matches!(
                conflict.resolution,
                std_deduce_reason::Resolution::Unresolved { .. }
            )
        })
        .expect("the example records an unresolved conflict");
    let description = unresolved_obligation(&document, conflict);
    assert!(
        description.ends_with("（没有声明任何优先关系）"),
        "{description}"
    );
    let report = cert::check(&lib.env, &document).expect("the certificate checks");
    assert_eq!(report.priority_edges_checked, 0);

    // Declared edges that lie on a cycle.
    let lib = load_sources("cycle-cert", &[("c.std", CYCLE_CASE)]);
    let goal = Expr::apps(
        Expr::constant("c.值"),
        [Expr::constant("c.甲"), Expr::constant("c.选A")],
    );
    let (d, order) = derive(&lib, &goal);
    let document = certificate(&lib.env, &d, &order).expect("the cycle derivation converts");
    let conflict = d
        .conflicts
        .iter()
        .find(|conflict| {
            matches!(
                conflict.resolution,
                std_deduce_reason::Resolution::Unresolved {
                    reason: std_deduce_reason::UnresolvedReason::PriorityUnusable { .. },
                    ..
                }
            )
        })
        .expect("the cycle records an unusable priority");
    let description = unresolved_obligation(&document, conflict);
    assert!(
        description.ends_with("（已有 1 条优先声明，但不足以裁决；其中 1 条落在优先级环内）"),
        "{description}"
    );
    let report = cert::check(&lib.env, &document).expect("the certificate checks");
    assert!(report.priority_sources_checked);
    assert_eq!(report.priority_edges_checked, 3);

    // Two claims (the case file's default identity).
    let lib = load_sources("assumption-cert", &[("case.std", ASSUMPTION_CASE)]);
    let goal = Expr::apps(Expr::constant("该批准"), [Expr::constant("甲")]);
    let (d, order) = derive(&lib, &goal);
    let document = certificate(&lib.env, &d, &order).expect("the assumption derivation converts");
    let conflict = d
        .conflicts
        .iter()
        .find(|conflict| {
            matches!(
                conflict.resolution,
                std_deduce_reason::Resolution::Unresolved {
                    reason: std_deduce_reason::UnresolvedReason::ConflictingAssumptions,
                    ..
                }
            )
        })
        .expect("the axioms conflict");
    let description = unresolved_obligation(&document, conflict);
    assert!(
        description.ends_with("（两侧都只是主张，未经证明，不能判出一方胜出）"),
        "{description}"
    );
    // Both claims are removed from the fact base by the unresolved
    // conflict, but the certificate must still record them as assumptions with
    // their sources: the conflict sides name them.
    for side in [&conflict.left, &conflict.right] {
        let encoded = cert::CertExpr::try_from(side).expect("the conflict side encodes");
        assert!(
            document
                .assumptions
                .iter()
                .any(|assumption| assumption.proposition == encoded),
            "the assumption `{}` must be recorded in the certificate: {:?}",
            print_expr(side),
            document.assumptions
        );
    }
    let report = cert::check(&lib.env, &document).expect("the certificate checks");
    assert_eq!(report.priority_edges_checked, 0);

    // Two strict facts: the same standoff, but neither side is a mere claim.
    let lib = load_sources(
        "strict-assumption-cert",
        &[("case.std", STRICT_ASSUMPTION_CASE)],
    );
    let (d, order) = derive(&lib, &goal);
    let document = certificate(&lib.env, &d, &order).expect("the strict derivation converts");
    let conflict = d
        .conflicts
        .iter()
        .find(|conflict| {
            matches!(
                conflict.resolution,
                std_deduce_reason::Resolution::Unresolved {
                    reason: std_deduce_reason::UnresolvedReason::ConflictingAssumptions,
                    ..
                }
            )
        })
        .expect("the strict facts conflict");
    let description = unresolved_obligation(&document, conflict);
    assert!(
        description.ends_with("（两侧都是严格事实，事实之间没有先后）"),
        "{description}"
    );
    let report = cert::check(&lib.env, &document).expect("the strict certificate checks");
    assert_eq!(report.priority_edges_checked, 0);
}

// -------------------------------------------------------- fact strictness

/// A case file whose fact claims the contrary of what the rule concludes.
fn non_strict_case(identity: &str) -> String {
    format!(
        r#"
sort 申请
pred 符合条件 : 申请 → Prop
pred 该批准 : 申请 → Prop
pred 不该批准 : 申请 → Prop
contrary 该批准 不该批准
obj 甲 : 申请
axiom 条件 : 符合条件 甲
  source text "甲法" locator "一"
axiom 已批准 : 该批准 甲
  identity {identity}
  source text "乙法" locator "二"
rule 拒绝 :
  params x : 申请
  premise 符合条件 x
  conclude 不该批准 x
  source text "丙法" locator "三"
"#
    )
}

/// A claim facing a rule conclusion is unresolved; the certificate records
/// the claim's identity and says in the obligation why it cannot win.
#[test]
fn a_claim_against_a_rule_carries_its_identity_into_the_certificate() {
    for (identity, label) in [("user_asserted", "用户陈述"), ("assumed", "分析假设")] {
        let lib = load_sources(
            "non-strict-cert",
            &[("case.std", &non_strict_case(identity))],
        );
        let goal = Expr::apps(Expr::constant("该批准"), [Expr::constant("甲")]);
        let (d, order) = derive(&lib, &goal);
        let conflict = d
            .conflicts
            .iter()
            .find(|conflict| {
                matches!(
                    conflict.resolution,
                    std_deduce_reason::Resolution::Unresolved {
                        reason: std_deduce_reason::UnresolvedReason::NonStrictFact { .. },
                        ..
                    }
                )
            })
            .expect("the claim and the rule conclusion conflict");
        let document = certificate(&lib.env, &d, &order).expect("the derivation converts");

        let recorded = document
            .assumptions
            .iter()
            .find(|assumption| assumption.label.as_deref() == Some("已批准"))
            .expect("the claim is recorded as an assumption");
        assert_eq!(
            recorded.identity,
            match identity {
                "user_asserted" => cert::FactIdentity::UserAsserted,
                _ => cert::FactIdentity::Assumed,
            }
        );

        let description = unresolved_obligation(&document, conflict);
        assert!(
            description.ends_with(&format!(
                "（「该批准 甲」只是「{label}」，未经证明，不能自动胜过规则结论）"
            )),
            "{description}"
        );

        let report = cert::check(&lib.env, &document).expect("the unresolved claim checks");
        assert!(!report.root_proved);
    }
}

const TWO_RULE_CASE: &str = r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
obj 甲 : 人
axiom 事实 : P 甲
  source text "测试" locator "1"
rule 规则A :
  params x : 人
  premise P x
  conclude Q x
  source text "测试" locator "A"
rule 规则B :
  params x : 人
  premise P x
  conclude Q x
  source text "测试" locator "B"
"#;

/// Two rules derive the same proposition: the derivation keeps both nodes,
/// records them in rule-name order, and the certificate checker accepts both.
#[test]
fn every_independent_witness_of_a_conclusion_is_kept() {
    let lib = load_sources("two-rule-cert", &[("case.std", TWO_RULE_CASE)]);
    let goal = Expr::apps(Expr::constant("Q"), [Expr::constant("甲")]);
    let (d, order) = derive(&lib, &goal);
    let group = d
        .alternatives
        .iter()
        .find(|group| group.proposition == goal)
        .expect("the derived conclusion has a witness group");
    assert_eq!(group.witnesses.len(), 2, "both derivations are kept");
    assert!(!group.truncated);
    let rules: Vec<String> = group
        .witnesses
        .iter()
        .map(|id| match &d.nodes[*id] {
            ReasonNode::RuleApplication { rule, .. } => rule.to_string(),
            other => panic!("a witness is not a rule step: {other:?}"),
        })
        .collect();
    assert_eq!(rules, ["规则A", "规则B"], "witnesses sort by rule name");

    let document = certificate(&lib.env, &d, &order).expect("the two-witness derivation converts");
    let document = document.with_environment(cert::EnvironmentIdentity::none());
    assert_eq!(document.alternatives.len(), 1);
    assert_eq!(document.alternatives[0].witnesses.len(), 2);
    let report = cert::check(&lib.env, &document).expect("both witnesses check");
    assert!(report.root_proved);
}
