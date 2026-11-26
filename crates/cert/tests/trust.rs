//! Trust-label derivation from certificate fields only, and the boundaries
//! that keep a gap or an unresolved conflict from being labelled `已验证`.

use std_deduce_cert::{
    derive_trust, ApplicabilityBasis, ApplicabilityReason, ApplicabilityReasonKind,
    ApplicabilityVerdict, Assumption, Binding, CertExpr, Certificate, Conflict,
    EnvironmentIdentity, Explicit, FactIdentity, FormatVersion, Node, ObligationKind,
    OpenObligation, Provenance, Resolution, RuleApplicability, TrustLabel, UnresolvedReason,
};

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

fn rule(conclusion: CertExpr, premises: Vec<usize>) -> Node {
    Node::RuleApplication {
        computed: None,
        rule: "规则甲".to_owned(),
        conclusion,
        premises,
        bindings: Vec::<Binding>::new(),
        sources: Vec::new(),
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
        alternatives: Vec::new(),
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Default::default(),
    }
}

#[test]
fn a_proof_over_only_strict_facts_is_verified_in_the_model() {
    let certificate = certificate(
        vec![assumption(atom("违法", "张三"), FactIdentity::Verified)],
        vec![
            Node::Assumption { assumption: 0 },
            rule(atom("受罚", "张三"), vec![0]),
        ],
        Some(1),
    );
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.labels(), &[TrustLabel::Verified]);
    let summary = report.summary();
    assert!(summary.starts_with("信任：已验证（"), "{summary}");
    assert!(summary.contains("法院查明 1 条"), "{summary}");
    assert!(summary.contains("无未决义务、无未决冲突"), "{summary}");
    assert!(
        summary.contains("这不等同于法律上正确"),
        "the summary must not read as legal correctness: {summary}"
    );
}

#[test]
fn a_claim_in_the_reachable_proof_is_depends_on_assumption() {
    let certificate = certificate(
        vec![
            assumption(atom("违法", "张三"), FactIdentity::UserAsserted),
            assumption(atom("已决", "张三"), FactIdentity::Stipulated),
        ],
        vec![
            Node::Assumption { assumption: 1 },
            Node::Assumption { assumption: 0 },
            rule(atom("受罚", "张三"), vec![0, 1]),
        ],
        Some(2),
    );
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.labels(), &[TrustLabel::DependsOnAssumption]);
    let summary = report.summary();
    assert!(summary.contains("据用户陈述 1 条"), "{summary}");
    assert!(
        summary.contains("同时使用严格事实（法院查明 0 条、双方无争议 1 条）"),
        "a mixed strict/claim proof must say what is the user's: {summary}"
    );
}

#[test]
fn a_claim_outside_the_root_graph_does_not_label_the_root() {
    // The fixed point can list a claim the conclusion never uses. The root's
    // own proof graph is what decides its label.
    let certificate = certificate(
        vec![
            assumption(atom("违法", "张三"), FactIdentity::Verified),
            assumption(atom("另有陈述", "李四"), FactIdentity::UserAsserted),
        ],
        vec![
            Node::Assumption { assumption: 0 },
            Node::Assumption { assumption: 1 },
            rule(atom("受罚", "张三"), vec![0]),
        ],
        Some(2),
    );
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.labels(), &[TrustLabel::Verified]);
}

#[test]
fn an_interpretation_application_is_depends_on_assumption() {
    let mut certificate = certificate(
        vec![assumption(atom("损害", "甲"), FactIdentity::Verified)],
        vec![
            Node::Assumption { assumption: 0 },
            Node::InterpretationApplication {
                interpretation: 0,
                premise: 0,
                conclusion: atom("重大", "甲"),
            },
        ],
        Some(1),
    );
    certificate
        .interpretations
        .push(std_deduce_cert::Interpretation {
            id: "重大解释".to_owned(),
            direction: std_deduce_cert::InterpretationDirection::Literal,
            from: atom("损害", "甲"),
            to: atom("重大", "甲"),
            sources: Vec::new(),
        });
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.labels(), &[TrustLabel::DependsOnAssumption]);
    assert!(
        report.summary().contains("解释应用 1 处"),
        "{}",
        report.summary()
    );
}

#[test]
fn a_gap_root_is_fact_needs_evidence_and_never_verified() {
    let mut certificate = certificate(
        Vec::new(),
        vec![Node::Gap {
            proposition: atom("受罚", "张三"),
            note: None,
            axiom_candidates: Vec::new(),
            candidates: Vec::new(),
        }],
        Some(0),
    );
    certificate.open_obligations.push(OpenObligation {
        id: "gap-0".to_owned(),
        kind: ObligationKind::MissingPremise,
        description: "缺口「受罚 张三」：没有可用的推导".to_owned(),
        nodes: vec![0],
    });
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.labels(), &[TrustLabel::FactNeedsEvidence]);
    assert!(!report.contains(TrustLabel::Verified));
    let summary = report.summary();
    assert!(summary.contains("根为缺口"), "{summary}");
    assert!(summary.contains("缺少前提义务 1 项"), "{summary}");
}

#[test]
fn an_unresolved_conflict_always_makes_dispute_unresolved() {
    let mut certificate = certificate(
        Vec::new(),
        vec![Node::Gap {
            proposition: atom("批准", "甲"),
            note: None,
            axiom_candidates: Vec::new(),
            candidates: Vec::new(),
        }],
        Some(0),
    );
    certificate.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Rules {
            rules: vec!["批准规则".to_owned()],
        },
        right_by: Provenance::Rules {
            rules: vec!["不批准规则".to_owned()],
        },
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::NoPriority,
        },
    });
    certificate.open_obligations.push(OpenObligation {
        id: "conflict-0".to_owned(),
        kind: ObligationKind::UnresolvedConflict,
        description: "冲突未决".to_owned(),
        nodes: Vec::new(),
    });
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.primary(), TrustLabel::DisputeUnresolved);
    assert!(report.contains(TrustLabel::DisputeUnresolved));
    assert!(!report.contains(TrustLabel::Verified));
    assert!(
        !report.contains(TrustLabel::DependsOnAssumption),
        "an unresolved conflict must not be reported as a mere assumption dependency"
    );
    assert!(
        report.summary().contains("未决冲突 1 项"),
        "{}",
        report.summary()
    );
}

#[test]
fn an_open_concept_obligation_requires_lawyer_judgement() {
    let mut certificate = certificate(
        Vec::new(),
        vec![rule(atom("重大", "甲"), Vec::new())],
        Some(0),
    );
    certificate.open_obligations.push(OpenObligation {
        id: "open-concept".to_owned(),
        kind: ObligationKind::OpenConcept,
        description: "开放概念 `重大` 需要人判断".to_owned(),
        nodes: vec![0],
    });
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.primary(), TrustLabel::NeedsLawyerJudgment);
    assert_eq!(report.labels(), &[TrustLabel::NeedsLawyerJudgment]);
    assert!(
        !report.contains(TrustLabel::DisputeUnresolved),
        "an open concept is a semantic judgement, not an unresolved conflict"
    );
    assert!(
        report.summary().contains("开放概念义务 1 项"),
        "{}",
        report.summary()
    );
}

#[test]
fn a_local_extension_obligation_requires_lawyer_judgement() {
    let mut certificate = certificate(
        Vec::new(),
        vec![rule(atom("应赔偿", "甲"), Vec::new())],
        Some(0),
    );
    certificate.open_obligations.push(OpenObligation {
        id: "local-extension".to_owned(),
        kind: ObligationKind::NeedsHumanDetermination,
        description: "规则由案件文件声明".to_owned(),
        nodes: vec![0],
    });
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.primary(), TrustLabel::NeedsLawyerJudgment);
    assert_eq!(report.labels(), &[TrustLabel::NeedsLawyerJudgment]);
    assert!(
        report.summary().contains("案件扩展义务 1 项"),
        "{}",
        report.summary()
    );
    assert!(
        report.summary().contains("local-extension"),
        "{}",
        report.summary()
    );
}

#[test]
fn an_unrelated_unresolved_conflict_does_not_change_the_root_label() {
    // The proved root uses a claim; the certificate records an unresolved
    // conflict on an unrelated branch. The conflict is not root-relevant, so
    // the root is still only `依赖假设`; a claim alone does not turn this into
    // `需律师判断` either.
    let mut certificate = certificate(
        vec![assumption(atom("违法", "张三"), FactIdentity::UserAsserted)],
        vec![
            Node::Assumption { assumption: 0 },
            rule(atom("受罚", "张三"), vec![0]),
        ],
        Some(1),
    );
    certificate.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Rules {
            rules: vec!["批准规则".to_owned()],
        },
        right_by: Provenance::Rules {
            rules: vec!["不批准规则".to_owned()],
        },
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::NoPriority,
        },
    });
    certificate.open_obligations.push(OpenObligation {
        id: "conflict-0".to_owned(),
        kind: ObligationKind::UnresolvedConflict,
        description: "冲突未决".to_owned(),
        nodes: Vec::new(),
    });
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.primary(), TrustLabel::DependsOnAssumption);
    assert_eq!(report.labels(), &[TrustLabel::DependsOnAssumption]);
    assert!(
        !report.contains(TrustLabel::DisputeUnresolved),
        "an unrelated conflict must not become 争点未决"
    );
    assert!(
        !report.contains(TrustLabel::NeedsLawyerJudgment),
        "an unresolved conflict plus a claim must not become 需律师判断"
    );
}

#[test]
fn an_unrelated_unresolved_conflict_does_not_remove_verified() {
    // A strict-fact proof elsewhere in the certificate can carry the same
    // unresolved conflict; only the root's own graph decides its label.
    let mut certificate = certificate(
        vec![assumption(atom("违法", "张三"), FactIdentity::Verified)],
        vec![
            Node::Assumption { assumption: 0 },
            rule(atom("受罚", "张三"), vec![0]),
        ],
        Some(1),
    );
    certificate.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Rules {
            rules: vec!["批准规则".to_owned()],
        },
        right_by: Provenance::Rules {
            rules: vec!["不批准规则".to_owned()],
        },
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::NoPriority,
        },
    });
    certificate.open_obligations.push(OpenObligation {
        id: "conflict-0".to_owned(),
        kind: ObligationKind::UnresolvedConflict,
        description: "冲突未决".to_owned(),
        nodes: Vec::new(),
    });
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.labels(), &[TrustLabel::Verified]);
    assert!(!report.contains(TrustLabel::DisputeUnresolved));
}

#[test]
fn an_unrelated_local_extension_obligation_does_not_need_lawyer() {
    // The obligation names a rule application that is not reachable from the
    // root; it must not turn the root's label into 需律师判断.
    let mut certificate = certificate(
        vec![assumption(atom("违法", "张三"), FactIdentity::Verified)],
        vec![
            Node::Assumption { assumption: 0 },
            rule(atom("受罚", "张三"), vec![0]),
        ],
        Some(1),
    );
    certificate.open_obligations.push(OpenObligation {
        id: "local-extension".to_owned(),
        kind: ObligationKind::NeedsHumanDetermination,
        description: "规则由案件文件声明".to_owned(),
        nodes: vec![99],
    });
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.labels(), &[TrustLabel::Verified]);
    assert!(!report.contains(TrustLabel::NeedsLawyerJudgment));
}

#[test]
fn missing_source_and_other_obligations_map_to_dispute_unresolved() {
    // P2: a proved strict root with only these two obligation kinds must not be
    // `已验证` and must not be an error; it is an unresolved item.
    let mut certificate = certificate(
        vec![assumption(atom("违法", "张三"), FactIdentity::Verified)],
        vec![
            Node::Assumption { assumption: 0 },
            rule(atom("受罚", "张三"), vec![0]),
        ],
        Some(1),
    );
    certificate.open_obligations.push(OpenObligation {
        id: "missing-source".to_owned(),
        kind: ObligationKind::MissingSource,
        description: "缺少来源".to_owned(),
        nodes: Vec::new(),
    });
    certificate.open_obligations.push(OpenObligation {
        id: "other".to_owned(),
        kind: ObligationKind::Other,
        description: "其他未决事项".to_owned(),
        nodes: Vec::new(),
    });
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.primary(), TrustLabel::DisputeUnresolved);
    assert!(!report.contains(TrustLabel::Verified));
    let summary = report.summary();
    assert!(summary.contains("缺少来源 1 项"), "{summary}");
    assert!(summary.contains("其他 1 项"), "{summary}");
}

#[test]
fn a_root_relevant_missing_premise_obligation_maps_to_fact_needs_evidence() {
    let mut certificate = certificate(
        vec![assumption(atom("违法", "张三"), FactIdentity::Verified)],
        vec![
            Node::Assumption { assumption: 0 },
            rule(atom("受罚", "张三"), vec![0]),
        ],
        Some(1),
    );
    certificate.open_obligations.push(OpenObligation {
        id: "gap-0".to_owned(),
        kind: ObligationKind::MissingPremise,
        description: "缺少前提".to_owned(),
        nodes: vec![0],
    });
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.primary(), TrustLabel::FactNeedsEvidence);
    assert!(!report.contains(TrustLabel::Verified));
    assert!(
        report.summary().contains("与根相关的缺少前提义务 1 项"),
        "{}",
        report.summary()
    );
}

#[test]
fn an_unattached_open_concept_is_still_root_relevant() {
    // An empty nodes list is "not localized", never "unrelated": dropping it
    // would silently hide a human judgement.
    let mut certificate = certificate(
        Vec::new(),
        vec![rule(atom("重大", "甲"), Vec::new())],
        Some(0),
    );
    certificate.open_obligations.push(OpenObligation {
        id: "open-concept".to_owned(),
        kind: ObligationKind::OpenConcept,
        description: "开放概念".to_owned(),
        nodes: Vec::new(),
    });
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.labels(), &[TrustLabel::NeedsLawyerJudgment]);
}

#[test]
fn the_summary_is_byte_identical_across_repeated_derivations() {
    let mut certificate = certificate(
        vec![
            assumption(atom("违法", "张三"), FactIdentity::UserAsserted),
            assumption(atom("情节", "张三"), FactIdentity::Assumed),
        ],
        vec![
            Node::Assumption { assumption: 0 },
            Node::Assumption { assumption: 1 },
            rule(atom("受罚", "张三"), vec![0, 1]),
        ],
        Some(2),
    );
    certificate.open_obligations.push(OpenObligation {
        id: "obligation-z".to_owned(),
        kind: ObligationKind::MissingSource,
        description: "缺少来源".to_owned(),
        nodes: Vec::new(),
    });
    certificate.open_obligations.push(OpenObligation {
        id: "obligation-a".to_owned(),
        kind: ObligationKind::Other,
        description: "其他".to_owned(),
        nodes: Vec::new(),
    });
    let first = derive_trust(&certificate).unwrap();
    let second = derive_trust(&certificate).unwrap();
    assert_eq!(first.summary(), second.summary());
    assert_eq!(
        format!("{:?}", first.labels()),
        format!("{:?}", second.labels())
    );
}

#[test]
fn a_missing_root_reports_the_absence_instead_of_verified() {
    let certificate = certificate(Vec::new(), Vec::new(), None);
    let report = derive_trust(&certificate).unwrap();
    assert_eq!(report.primary(), TrustLabel::FactNeedsEvidence);
    assert!(!report.contains(TrustLabel::Verified));
    assert!(
        report.summary().contains("没有根节点"),
        "{}",
        report.summary()
    );
}
