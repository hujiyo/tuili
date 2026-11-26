//! Conflict completeness: a certificate may not omit a conflict the
//! environment already registers.
//!
//! Every certificate here is built by hand from the certificate model; the
//! reasoner is not used. The checker must compare the conclusions the root
//! reaches with the environment's facts through the same conflict judgement
//! the reasoner records them with, and refuse a certificate that leaves such a
//! conflict out.

use std_deduce_cert::{
    check, check_display_projection, ApplicabilityBasis, ApplicabilityReason,
    ApplicabilityReasonKind, ApplicabilityVerdict, Assumption, Binding, CertExpr, Certificate,
    Conflict, EnvironmentIdentity, Explicit, FactIdentity, FormatVersion, Node, Provenance,
    Resolution, ResolutionBasis, RuleApplicability, Side, Source, UnresolvedReason,
};
use std_deduce_kernel::env::{DeclKind, Env};
use std_deduce_lang::Library;

/// A universal fact, a strict contrary fact and two rules: `推定有罪` derives
/// the defeated conclusion, `归责` derives a conclusion below it.
const STRICT_THEORY: &str = r#"
sort 人
pred 有罪 : 人 → Prop
pred 无罪 : 人 → Prop
pred 可疑 : 人 → Prop
pred 可罚 : 人 → Prop
contrary 有罪 无罪
obj 张三 : 人
axiom 张三可疑 : 可疑 张三
  source text "材料" locator "第一页"
axiom 张三无罪 : 无罪 张三
  identity verified
  source text "判决书" locator "查明事实"
rule 推定有罪 :
  params p : 人
  premise 可疑 p
  conclude 有罪 p
  source text "示例法" locator "第一条"
rule 归责 :
  params p : 人
  premise 有罪 p
  conclude 可罚 p
  source text "示例法" locator "第二条"
"#;

/// The same shape as [`STRICT_THEORY`], but the contrary fact is only a
/// claim.
const CLAIM_THEORY: &str = r#"
sort 人
pred 有罪 : 人 → Prop
pred 无罪 : 人 → Prop
pred 可疑 : 人 → Prop
pred 可罚 : 人 → Prop
contrary 有罪 无罪
obj 张三 : 人
axiom 张三可疑 : 可疑 张三
  source text "材料" locator "第一页"
axiom 张三无罪 : 无罪 张三
  source text "答辩状" locator "第二页"
rule 推定有罪 :
  params p : 人
  premise 可疑 p
  conclude 有罪 p
  source text "示例法" locator "第一条"
rule 归责 :
  params p : 人
  premise 有罪 p
  conclude 可罚 p
  source text "示例法" locator "第二条"
"#;

/// [`STRICT_THEORY`] with the strict fact replaced by a disputed one.
const DISPUTED_THEORY: &str = r#"
sort 人
pred 有罪 : 人 → Prop
pred 无罪 : 人 → Prop
pred 可疑 : 人 → Prop
contrary 有罪 无罪
obj 张三 : 人
axiom 张三可疑 : 可疑 张三
  source text "材料" locator "第一页"
axiom 张三无罪 : 无罪 张三
  identity disputed
  source text "答辩状" locator "第二页"
rule 推定有罪 :
  params p : 人
  premise 可疑 p
  conclude 有罪 p
  source text "示例法" locator "第一条"
"#;

/// Two individuals: the root's derivation is about 张三, the conflicting
/// conclusion is about 李四 and is not reachable from the root.
const UNREACHABLE_THEORY: &str = r#"
sort 人
pred 有罪 : 人 → Prop
pred 无罪 : 人 → Prop
pred 可疑 : 人 → Prop
contrary 有罪 无罪
obj 张三 : 人
obj 李四 : 人
axiom 张三可疑 : 可疑 张三
  source text "材料" locator "第一页"
axiom 李四可疑 : 可疑 李四
  source text "材料" locator "第二页"
axiom 李四无罪 : 无罪 李四
  identity verified
  source text "判决书" locator "查明事实"
rule 推定有罪 :
  params p : 人
  premise 可疑 p
  conclude 有罪 p
  source text "示例法" locator "第一条"
"#;

/// The contrary predicates are named through a `def` alias: the environment's
/// strict fact is registered as `夫妻`, the rule concludes `非配偶`, and only
/// normalization makes them meet.
const ALIAS_THEORY: &str = r#"
sort 人
pred 配偶 : 人 → 人 → Prop
pred 非配偶 : 人 → 人 → Prop
contrary 配偶 非配偶
def 夫妻 : 人 → 人 → Prop := 配偶
pred 依据 : 人 → Prop
obj 张三 : 人
obj 李四 : 人
axiom 依据事实 : 依据 张三
  source text "材料" locator "第一页"
axiom 夫妻事实 : 夫妻 张三 李四
  identity verified
  source text "判决书" locator "查明事实"
rule 否定配偶 :
  params p : 人
  premise 依据 p
  conclude 非配偶 p 李四
  source text "示例法" locator "第一条"
"#;

/// A `unique` predicate: the same case may carry only one applicable norm.
const UNIQUE_THEORY: &str = r#"
sort 案件
sort 规范
pred 应适用 : 规范 → 案件 → Prop
unique 应适用 1
pred 是本案 : 案件 → Prop
obj 案 : 案件
obj 种子法 : 规范
obj 条例 : 规范
axiom 本案已受理 : 是本案 案
  source text "材料" locator "第一页"
axiom 种子法应适用 : 应适用 种子法 案
  identity verified
  source text "判决书" locator "查明事实"
rule 主张条例 :
  params x : 案件
  premise 是本案 x
  conclude 应适用 条例 x
  source text "示例法" locator "第一条"
"#;

/// A universal fact and a strict contrary fact: only instantiating the
/// universal makes the two meet.
const UNIVERSAL_THEORY: &str = r#"
sort 人
pred 有罪 : 人 → Prop
pred 无罪 : 人 → Prop
contrary 有罪 无罪
obj 张三 : 人
axiom 凡人有罪 : ∀ (x : 人), 有罪 x
  source text "示例法" locator "第一条"
axiom 张三无罪 : 无罪 张三
  identity verified
  source text "判决书" locator "查明事实"
"#;

/// A strict fact and a claim about the same individual, both registered facts.
const STRICT_AND_CLAIM_THEORY: &str = r#"
sort 申请
pred 批准 : 申请 → Prop
pred 不批准 : 申请 → Prop
contrary 批准 不批准
obj 甲 : 申请
axiom 已批准 : 批准 甲
  identity verified
  source text "判决" locator "第一页"
axiom 未批准 : 不批准 甲
  source text "答辩状" locator "第二页"
"#;

/// Two strict facts contradict each other: the honest record is an unresolved
/// conflict, and the case is factually undecided.
const TWO_STRICT_THEORY: &str = r#"
sort 申请
pred 批准 : 申请 → Prop
pred 不批准 : 申请 → Prop
pred 可诉 : 申请 → Prop
contrary 批准 不批准
obj 甲 : 申请
axiom 已批准 : 批准 甲
  identity verified
  source text "判决" locator "第一页"
axiom 未批准 : 不批准 甲
  identity verified
  source text "判决" locator "第二页"
rule 起诉 :
  params x : 申请
  premise 批准 x
  conclude 可诉 x
  source text "示例法" locator "第一条"
"#;

fn env_from(name: &str, source: &str) -> Env {
    let mut library = Library::new();
    library.load(name, source).expect("test theory loads");
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
    app(app(constant(predicate), constant(left)), constant(right))
}

fn fact(proposition: CertExpr, identity: FactIdentity) -> Assumption {
    Assumption {
        proposition,
        identity,
        sources: Vec::new(),
        label: None,
        occurred_at: Explicit::none(),
        occurred_in: Explicit::none(),
    }
}

fn assumption_node(assumption: usize) -> Node {
    Node::Assumption { assumption }
}

/// The applicability record of a rule declared without any scope.
fn unscoped_applicability() -> Box<RuleApplicability> {
    Box::new(RuleApplicability {
        verdict: ApplicabilityVerdict::Unchecked,
        basis: ApplicabilityBasis::default(),
        reason: Explicit::some(ApplicabilityReason::new(
            ApplicabilityReasonKind::RuleHasNoScope,
        )),
    })
}

fn rule_node(
    rule: &str,
    conclusion: CertExpr,
    premises: Vec<usize>,
    bindings: Vec<(&str, CertExpr)>,
) -> Node {
    Node::RuleApplication {
        guards: Vec::new(),
        computed: None,
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
        applicability: unscoped_applicability(),
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
        alternatives: Vec::new(),
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Default::default(),
    }
}

/// The strict layout shared by the fact-versus-conclusion fixtures:
/// `[可疑 -> 有罪 -> 可罚]`, with the defeated side's own fact in the table.
fn strict_nodes() -> Vec<Node> {
    vec![
        assumption_node(0),
        rule_node(
            "推定有罪",
            atom("有罪", "张三"),
            vec![0],
            vec![("p", constant("张三"))],
        ),
        rule_node(
            "归责",
            atom("可罚", "张三"),
            vec![1],
            vec![("p", constant("张三"))],
        ),
    ]
}

fn strict_assumptions() -> Vec<Assumption> {
    vec![
        fact(atom("可疑", "张三"), FactIdentity::UserAsserted),
        fact(atom("无罪", "张三"), FactIdentity::Verified),
    ]
}

/// The recorded defeat of `有罪 张三` by the strict fact `无罪 张三`, with the
/// fact side winning.
fn strict_defeat() -> Conflict {
    Conflict {
        left: atom("有罪", "张三"),
        right: atom("无罪", "张三"),
        left_by: Provenance::Rules {
            rules: vec!["推定有罪".to_owned()],
        },
        right_by: Provenance::Assumption,
        resolution: Resolution::Defeated {
            winner: Side::Right,
            basis: ResolutionBasis::Assumption,
        },
    }
}

fn reject(cert: &Certificate, env: &Env) -> std_deduce_cert::CheckError {
    check(env, cert).expect_err("the certificate must be rejected")
}

/// A rule conclusion that loses to a strict fact, with the conflict omitted,
/// is refused: the certificate must not turn a defeated step into a proof by
/// deleting its record and re-rooting at it.
#[test]
fn a_rule_conclusion_that_loses_to_a_strict_fact_must_record_the_conflict() {
    let env = env_from("conflict-completeness-strict", STRICT_THEORY);
    let cert = certificate(strict_assumptions(), strict_nodes(), Some(1));
    let error = reject(&cert, &env);
    assert_eq!(error.node, Some(1), "{error}");
    let message = &error.message;
    assert!(message.contains("没有记录该冲突"), "{error}");
    assert!(message.contains("有罪 张三"), "{error}");
    assert!(message.contains("无罪 张三"), "{error}");
    assert!(message.contains("法院查明"), "{error}");
}

/// The same certificate with the defeat recorded and adjudicated passes: the
/// conflict is root-reachable through the defeated premise, and the root below
/// it is not itself a conflict side.
#[test]
fn a_recorded_strict_defeat_lets_the_root_through() {
    let env = env_from("conflict-completeness-strict-recorded", STRICT_THEORY);
    let mut cert = certificate(strict_assumptions(), strict_nodes(), Some(2));
    cert.conflicts.push(strict_defeat());
    let report = check(&env, &cert).expect("a correctly recorded defeat checks");
    assert!(report.root_proved);
    assert!(!report.conflict_resolved, "the root is below the conflict");
}

/// A claim against a rule conclusion must be recorded as an unresolved
/// conflict, not silently dropped.
#[test]
fn an_unrecorded_claim_against_a_rule_conclusion_is_rejected() {
    let env = env_from("conflict-completeness-claim", CLAIM_THEORY);
    let cert = certificate(
        vec![fact(atom("可疑", "张三"), FactIdentity::UserAsserted)],
        strict_nodes(),
        Some(1),
    );
    let error = reject(&cert, &env);
    assert_eq!(error.node, Some(1), "{error}");
    let message = &error.message;
    assert!(message.contains("记录为未决冲突"), "{error}");
    assert!(message.contains("用户陈述"), "{error}");
    assert!(message.contains("无罪 张三"), "{error}");
}

/// A recorded unresolved conflict is accepted: the certificate says the node
/// is not asserted, and the report keeps `root_proved` for the root below it.
#[test]
fn a_recorded_unresolved_claim_conflict_lets_the_root_through() {
    let env = env_from("conflict-completeness-claim-recorded", CLAIM_THEORY);
    let mut cert = certificate(
        vec![
            fact(atom("可疑", "张三"), FactIdentity::UserAsserted),
            fact(atom("无罪", "张三"), FactIdentity::UserAsserted),
        ],
        strict_nodes(),
        Some(2),
    );
    cert.conflicts.push(Conflict {
        left: atom("有罪", "张三"),
        right: atom("无罪", "张三"),
        left_by: Provenance::Rules {
            rules: vec!["推定有罪".to_owned()],
        },
        right_by: Provenance::Assumption,
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::NonStrictFact {
                identity: FactIdentity::UserAsserted,
            },
        },
    });
    let report = check(&env, &cert).expect("a correctly recorded unresolved conflict checks");
    assert!(report.root_proved);
}

/// A claim recorded as a defeat would hide an unresolved conflict. The
/// certificate is rejected; the resolution layer refuses the forged basis
/// before the root is read.
#[test]
fn a_claim_conflict_recorded_as_defeated_is_rejected() {
    let env = env_from("conflict-completeness-claim-defeated", CLAIM_THEORY);
    let mut cert = certificate(
        vec![
            fact(atom("可疑", "张三"), FactIdentity::UserAsserted),
            fact(atom("无罪", "张三"), FactIdentity::UserAsserted),
        ],
        strict_nodes(),
        Some(2),
    );
    cert.conflicts.push(Conflict {
        left: atom("有罪", "张三"),
        right: atom("无罪", "张三"),
        left_by: Provenance::Rules {
            rules: vec!["推定有罪".to_owned()],
        },
        right_by: Provenance::Assumption,
        resolution: Resolution::Defeated {
            winner: Side::Left,
            basis: ResolutionBasis::Assumption,
        },
    });
    reject(&cert, &env);
}

/// A disputed fact asserts what the other side claims, so it never takes part
/// in a conflict and cannot block the root.
#[test]
fn a_disputed_fact_does_not_reject_a_reachable_conclusion() {
    let env = env_from("conflict-completeness-disputed", DISPUTED_THEORY);
    let cert = certificate(
        vec![fact(atom("可疑", "张三"), FactIdentity::UserAsserted)],
        strict_nodes()[..2].to_vec(),
        Some(1),
    );
    check(&env, &cert).expect("a disputed fact takes part in no derivation");
}

/// Only the root's proof graph is scanned: a conflicting conclusion on an
/// unrelated branch does not reject the root.
#[test]
fn an_unreachable_conflict_does_not_affect_the_root() {
    let env = env_from("conflict-completeness-unreachable", UNREACHABLE_THEORY);
    let cert = certificate(
        vec![
            fact(atom("可疑", "张三"), FactIdentity::UserAsserted),
            fact(atom("可疑", "李四"), FactIdentity::UserAsserted),
        ],
        vec![
            assumption_node(0),
            rule_node(
                "推定有罪",
                atom("有罪", "张三"),
                vec![0],
                vec![("p", constant("张三"))],
            ),
            assumption_node(1),
            rule_node(
                "推定有罪",
                atom("有罪", "李四"),
                vec![2],
                vec![("p", constant("李四"))],
            ),
        ],
        Some(1),
    );
    check(&env, &cert).expect("the unreachable branch is not the root's proof");
}

/// `def` aliases are normalized before the conflict is judged: `夫妻` reaches
/// `配偶`, which the strict `非配偶` fact contradicts.
#[test]
fn a_def_alias_is_read_before_judging_a_conflict() {
    let env = env_from("conflict-completeness-alias", ALIAS_THEORY);
    let cert = certificate(
        vec![fact(atom("依据", "张三"), FactIdentity::UserAsserted)],
        vec![
            assumption_node(0),
            rule_node(
                "否定配偶",
                binary("非配偶", "张三", "李四"),
                vec![0],
                vec![("p", constant("张三"))],
            ),
        ],
        Some(1),
    );
    let error = reject(&cert, &env);
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("没有记录该冲突"), "{error}");
    assert!(error.message.contains("法院查明"), "{error}");
    // The strict fact is stored normalized: the conflict is found through
    // `配偶`, not through the printed alias alone.
    assert!(error.message.contains("事实「配偶 张三 李四」"), "{error}");
    assert!(error.message.contains("夫妻事实"), "{error}");
}

/// A `unique` argument position conflicts even when the predicates agree: the
/// certificate must record it, and the omitted record is refused.
#[test]
fn a_unique_position_conflict_must_be_recorded() {
    let env = env_from("conflict-completeness-unique", UNIQUE_THEORY);
    let cert = certificate(
        vec![fact(atom("是本案", "案"), FactIdentity::UserAsserted)],
        vec![
            assumption_node(0),
            rule_node(
                "主张条例",
                binary("应适用", "条例", "案"),
                vec![0],
                vec![("x", constant("案"))],
            ),
        ],
        Some(1),
    );
    let error = reject(&cert, &env);
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("没有记录该冲突"), "{error}");
    assert!(error.message.contains("应适用 种子法 案"), "{error}");
    assert!(error.message.contains("法院查明"), "{error}");
}

/// A universal instance is a conclusion like any other: when a strict fact
/// contradicts its substituted conclusion, the conflict must be recorded.
#[test]
fn a_universal_instance_that_loses_to_a_strict_fact_must_record_the_conflict() {
    let env = env_from("conflict-completeness-universal", UNIVERSAL_THEORY);
    let decl = env.get("凡人有罪").expect("the universal fact is declared");
    let DeclKind::Fact { .. } = &decl.kind else {
        panic!("凡人有罪 is a fact declaration");
    };
    let sources: Vec<Source> = decl.sources.iter().map(Source::from).collect();
    let cert = certificate(
        Vec::new(),
        vec![Node::AxiomInstance {
            axiom: "凡人有罪".to_owned(),
            identity: FactIdentity::UserAsserted,
            bindings: vec![Binding {
                parameter: "x".to_owned(),
                value: constant("张三"),
            }],
            conclusion: atom("有罪", "张三"),
            sources,
        }],
        Some(0),
    );
    let error = reject(&cert, &env);
    assert_eq!(error.node, Some(0), "{error}");
    assert!(error.message.contains("没有记录该冲突"), "{error}");
    assert!(error.message.contains("有罪 张三"), "{error}");
    assert!(error.message.contains("无罪 张三"), "{error}");
    assert!(error.message.contains("法院查明"), "{error}");
}

/// A root that is itself an assumption is compared too: a claim root cannot
/// stand when a strict fact contradicts it and the certificate omits the
/// conflict.
#[test]
fn a_root_assumption_must_record_its_conflict() {
    let env = env_from("conflict-completeness-root-assumption", STRICT_THEORY);
    let cert = certificate(
        vec![fact(atom("可疑", "张三"), FactIdentity::UserAsserted)],
        vec![assumption_node(0)],
        Some(0),
    );
    // `可疑 张三` is no one's contrary, so this root is clean.
    check(&env, &cert).expect("an assumption with no contrary is a legal root");
    let contradicted = certificate(
        vec![fact(atom("有罪", "张三"), FactIdentity::UserAsserted)],
        vec![assumption_node(0)],
        Some(0),
    );
    let error = reject(&contradicted, &env);
    assert_eq!(error.node, Some(0), "{error}");
    assert!(error.message.contains("没有记录该冲突"), "{error}");
    assert!(error.message.contains("无罪 张三"), "{error}");
}

/// A claim conflicting with a strict fact is decided by the strict fact. When
/// the root is the strict fact itself, the recorded defeat is accepted and the
/// report says the root conflict was resolved.
#[test]
fn a_strict_fact_that_defeats_a_claim_is_accepted_when_recorded() {
    let env = env_from("conflict-completeness-strict-wins", STRICT_AND_CLAIM_THEORY);
    let mut cert = certificate(
        vec![
            fact(atom("批准", "甲"), FactIdentity::Verified),
            fact(atom("不批准", "甲"), FactIdentity::UserAsserted),
        ],
        vec![assumption_node(0)],
        Some(0),
    );
    cert.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Assumption,
        right_by: Provenance::Assumption,
        resolution: Resolution::Defeated {
            winner: Side::Left,
            basis: ResolutionBasis::Assumption,
        },
    });
    let report = check(&env, &cert).expect("a correctly recorded defeat checks");
    assert!(report.root_proved);
    assert!(report.conflict_resolved);
}

/// Two strict facts have no order. A conclusion that is itself a strict fact
/// conflicts with the other strict fact, so the certificate must record the
/// standoff; omitting it is a missing conflict.
#[test]
fn two_strict_facts_must_record_an_unresolved_conflict() {
    let env = env_from("conflict-completeness-two-strict", TWO_STRICT_THEORY);
    let cert = certificate(
        vec![
            fact(atom("批准", "甲"), FactIdentity::Verified),
            fact(atom("不批准", "甲"), FactIdentity::Verified),
        ],
        vec![assumption_node(0)],
        Some(0),
    );
    let error = reject(&cert, &env);
    assert_eq!(error.node, Some(0), "{error}");
    assert!(error.message.contains("conflicting_assumptions"), "{error}");
    assert!(error.message.contains("没有记录"), "{error}");
    assert!(error.message.contains("不批准 甲"), "{error}");
    assert!(error.message.contains("法院查明"), "{error}");
}

/// The honest record is an unresolved conflict: neither strict fact wins, and
/// the certificate is valid. The root stays a conditional proof; a caller gating
/// on unresolved conflicts (the CLI) reports it as unresolved, not as a clean
/// proof.
#[test]
fn a_recorded_unresolved_conflict_between_two_strict_facts_passes() {
    let env = env_from(
        "conflict-completeness-two-strict-recorded",
        TWO_STRICT_THEORY,
    );
    let mut cert = certificate(
        vec![
            fact(atom("批准", "甲"), FactIdentity::Verified),
            fact(atom("不批准", "甲"), FactIdentity::Verified),
        ],
        vec![assumption_node(0)],
        Some(0),
    );
    cert.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Assumption,
        right_by: Provenance::Assumption,
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::ConflictingAssumptions,
        },
    });
    let report = check(&env, &cert).expect("an honest standoff is a valid certificate");
    assert!(
        report.root_proved,
        "the root is still the recorded assumption"
    );
    assert!(
        !report.conflict_resolved,
        "an unresolved conflict is not a resolved one"
    );
    assert!(
        report.root_conflict_unresolved,
        "the report must tell a renderer not to call this root a proved conclusion"
    );
}

/// Two strict facts cannot be adjudicated: recording one side as the winner is
/// a forged adjudication and the certificate is rejected.
#[test]
fn a_recorded_defeat_between_two_strict_facts_is_rejected() {
    let env = env_from("conflict-completeness-two-strict-defeat", TWO_STRICT_THEORY);
    let mut cert = certificate(
        vec![
            fact(atom("批准", "甲"), FactIdentity::Verified),
            fact(atom("不批准", "甲"), FactIdentity::Verified),
        ],
        vec![assumption_node(0)],
        Some(0),
    );
    cert.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Assumption,
        right_by: Provenance::Assumption,
        resolution: Resolution::Defeated {
            winner: Side::Left,
            basis: ResolutionBasis::Assumption,
        },
    });
    let error = reject(&cert, &env);
    assert!(error.message.contains("两侧都是严格事实"), "{error}");
}

/// The display projection is deliberately weaker than certificate validity: it
/// skips only the certificate-wide conflict-completeness scan. The very object
/// `check` rejects (an unrecorded strict-fact conflict) passes the projection,
/// which is why the projection must never be used to decide whether a
/// certificate is valid.
#[test]
fn the_display_projection_is_not_certificate_validity() {
    let env = env_from("conflict-completeness-projection", STRICT_THEORY);
    let cert = certificate(strict_assumptions(), strict_nodes(), Some(1));
    let error = reject(&cert, &env);
    assert!(error.message.contains("没有记录该冲突"), "{error}");
    let projection = check_display_projection(&env, &cert)
        .expect("the display projection skips only the completeness scan");
    assert!(projection.root_proved);
}
