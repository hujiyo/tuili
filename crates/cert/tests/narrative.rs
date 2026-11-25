//! Natural-language rendering: the explanation must say "because … so …",
//! keep the recorded sources and instances, and never invent a fact, a source,
//! an identity or a resolution the certificate does not contain.

use std_deduce_cert::{
    render_narrative, ApplicabilityBasis, ApplicabilityReason, ApplicabilityReasonKind,
    ApplicabilityVerdict, Assumption, Binding, CertExpr, Certificate, Conflict,
    EnvironmentIdentity, Explicit, FactIdentity, FormatVersion, GapCandidate, Node, ObligationKind,
    OpenObligation, PriorityClause, PriorityEdge, PriorityOrigin, Provenance, Resolution,
    ResolutionBasis, RuleApplicability, Side, Source, UnresolvedReason,
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

fn source(text: &str, locator: &str, version: &str, note: &str) -> Source {
    Source {
        text: text.to_owned(),
        locator: locator.to_owned(),
        version: version.to_owned(),
        effective: None,
        note: note.to_owned(),
        quote: String::new(),
        url: String::new(),
        jurisdiction: String::new(),
        retrieved_at: String::new(),
        hash: String::new(),
    }
}

fn assumption(
    proposition: CertExpr,
    identity: FactIdentity,
    sources: Vec<Source>,
    label: Option<&str>,
) -> Assumption {
    Assumption {
        proposition,
        identity,
        sources,
        label: label.map(str::to_owned),
        occurred_at: Explicit::none(),
        occurred_in: Explicit::none(),
    }
}

/// The record of a rule declared without any scope.
/// A gap candidate stores its record inline: the candidate list is already
/// behind a `Vec`.
fn unscoped_candidate_applicability() -> RuleApplicability {
    *unscoped_applicability()
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

fn binding(parameter: &str, value: CertExpr) -> Binding {
    Binding {
        parameter: parameter.to_owned(),
        value,
    }
}

fn rule(
    rule: &str,
    conclusion: CertExpr,
    premises: Vec<usize>,
    bindings: Vec<Binding>,
    sources: Vec<Source>,
) -> Node {
    Node::RuleApplication {
        rule: rule.to_owned(),
        conclusion,
        premises,
        bindings,
        sources,
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
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Default::default(),
    }
}

#[test]
fn renders_a_rule_tree_as_a_because_so_explanation() {
    let certificate = certificate(
        vec![
            assumption(
                atom("侵占", "张三"),
                FactIdentity::UserAsserted,
                vec![source("民法典", "第一条", "2020", "按通常理解")],
                Some("事实一"),
            ),
            assumption(
                atom("侵占", "李四"),
                FactIdentity::Verified,
                vec![source("申请人", "材料", "2024", "")],
                None,
            ),
        ],
        vec![
            Node::Assumption { assumption: 0 },
            Node::Assumption { assumption: 1 },
            rule(
                "规则甲",
                atom("违法", "张三"),
                vec![0, 1],
                vec![
                    binding("p", constant("张三")),
                    binding("q", constant("李四")),
                ],
                vec![source("宪法", "第三十九条", "2018", "按通常理解")],
            ),
        ],
        Some(2),
    );

    let expected = "\
【结论】「违法 张三」由规则推出。

【推理过程】
  1. 据用户陈述，「侵占 张三」成立（这是用户主张，未经独立证明）。
     标签：事实一
     来源：「民法典第一条」（2020）；说明：按通常理解
  2. 根据法院查明，「侵占 李四」成立。
     来源：「申请人材料」（2024）
  3. 因为「侵占 张三」（第 1 条）、「侵占 李四」（第 2 条），根据规则「规则甲」，所以「违法 张三」成立。
     实例：p ↦ 张三，q ↦ 李四
     来源：「宪法第三十九条」（2018）；说明：按通常理解
";
    assert_eq!(render_narrative(&certificate).unwrap(), expected);
}

#[test]
fn every_fact_identity_is_stated_in_plain_words() {
    for (identity, conclusion, step) in [
        (
            FactIdentity::Verified,
            "【结论】根据法院查明，「侵占 张三」成立。",
            "  1. 根据法院查明，「侵占 张三」成立。",
        ),
        (
            FactIdentity::UserAsserted,
            "【结论】据用户陈述，「侵占 张三」成立（这是用户主张，未经独立证明）。",
            "  1. 据用户陈述，「侵占 张三」成立（这是用户主张，未经独立证明）。",
        ),
        (
            FactIdentity::Assumed,
            "【结论】作为分析假设，「侵占 张三」假定成立（未经独立证明）。",
            "  1. 作为分析假设，「侵占 张三」假定成立（未经独立证明）。",
        ),
        (
            FactIdentity::Stipulated,
            "【结论】双方无争议，「侵占 张三」成立。",
            "  1. 双方无争议，「侵占 张三」成立。",
        ),
        (
            FactIdentity::Disputed,
            "【结论】「侵占 张三」是对方争议的事实（不参与推导）。",
            "  1. 「侵占 张三」是对方争议的事实（不参与推导）。",
        ),
    ] {
        let certificate = certificate(
            vec![assumption(
                atom("侵占", "张三"),
                identity,
                vec![source("民法典", "第一条", "2020", "")],
                None,
            )],
            vec![Node::Assumption { assumption: 0 }],
            Some(0),
        );
        let out = render_narrative(&certificate).unwrap();
        assert!(out.contains(conclusion), "{identity:?}\n{out}");
        assert!(out.contains(step), "{identity:?}\n{out}");
    }
}

#[test]
fn a_missing_source_is_reported_instead_of_being_omitted() {
    let certificate = certificate(
        vec![assumption(
            atom("侵占", "张三"),
            FactIdentity::UserAsserted,
            Vec::new(),
            None,
        )],
        vec![
            Node::Assumption { assumption: 0 },
            rule(
                "规则甲",
                atom("违法", "张三"),
                vec![0],
                Vec::new(),
                Vec::new(),
            ),
        ],
        Some(1),
    );

    let expected = "\
【结论】「违法 张三」由规则推出。

【推理过程】
  1. 据用户陈述，「侵占 张三」成立（这是用户主张，未经独立证明）。
     来源：证书未记录来源。
  2. 因为「侵占 张三」（第 1 条），根据规则「规则甲」，所以「违法 张三」成立。
     来源：证书未记录来源。
";
    assert_eq!(render_narrative(&certificate).unwrap(), expected);
}

#[test]
fn a_rule_without_premises_is_stated_without_an_empty_because() {
    let certificate = certificate(
        Vec::new(),
        vec![rule(
            "规则甲",
            atom("违法", "张三"),
            Vec::new(),
            Vec::new(),
            vec![source("宪法", "第三十九条", "2018", "")],
        )],
        Some(0),
    );
    let out = render_narrative(&certificate).unwrap();
    assert!(
        out.contains("  1. 根据规则「规则甲」（该规则没有前提），所以「违法 张三」成立。"),
        "{out}"
    );
}

#[test]
fn renders_a_gap_with_missing_premises_and_an_unless_blocker() {
    let certificate = certificate(
        vec![assumption(
            atom("已决", "甲"),
            FactIdentity::Assumed,
            vec![source("分析备忘", "第二段", "", "")],
            None,
        )],
        vec![Node::Gap {
            proposition: atom("可复议", "甲"),
            note: Some("目标处于冲突中".to_owned()),
            candidates: vec![
                GapCandidate {
                    rule: "规则一".to_owned(),
                    bindings: Vec::new(),
                    held: Vec::new(),
                    missing: vec![atom("不批准", "甲"), atom("批准", "甲")],
                    blocked_by: Vec::new(),
                    sources: vec![source("来源", "一", "", "")],
                    applicability: unscoped_candidate_applicability(),
                },
                GapCandidate {
                    rule: "规则二".to_owned(),
                    bindings: Vec::new(),
                    held: Vec::new(),
                    missing: Vec::new(),
                    blocked_by: vec![atom("已决", "甲")],
                    sources: Vec::new(),
                    applicability: unscoped_candidate_applicability(),
                },
                GapCandidate {
                    rule: "规则三".to_owned(),
                    bindings: Vec::new(),
                    held: Vec::new(),
                    missing: Vec::new(),
                    blocked_by: Vec::new(),
                    sources: Vec::new(),
                    applicability: unscoped_candidate_applicability(),
                },
                GapCandidate {
                    rule: "规则四".to_owned(),
                    bindings: Vec::new(),
                    held: Vec::new(),
                    missing: Vec::new(),
                    blocked_by: vec![atom("其他", "甲")],
                    sources: Vec::new(),
                    applicability: unscoped_candidate_applicability(),
                },
            ],
        }],
        Some(0),
    );

    let out = render_narrative(&certificate).unwrap();
    let expected = "\
【结论】「可复议 甲」未获证明（此处是缺口）。

【缺口】
  · 「可复议 甲」没有可闭合的推导。
  · 说明：目标处于冲突中
  · 候选规则「规则一」：缺少前提「不批准 甲」、「批准 甲」。
     来源：「来源一」
  · 候选规则「规则二」：unless 条件「已决 甲」（分析假设）已成立，故该规则被阻断。
     来源：证书未记录来源。
  · 候选规则「规则三」：证书没有记录它缺少什么。
     来源：证书未记录来源。
  · 候选规则「规则四」：unless 条件「其他 甲」（证书未记录身份）已成立，故该规则被阻断。
     来源：证书未记录来源。
";
    assert_eq!(out, expected);
}

#[test]
fn an_ambiguous_blocker_is_not_attributed_to_a_fact() {
    let certificate = certificate(
        vec![assumption(
            atom("已决", "甲"),
            FactIdentity::Assumed,
            vec![source("分析备忘", "第二段", "", "")],
            None,
        )],
        vec![
            Node::Assumption { assumption: 0 },
            rule(
                "规则乙",
                atom("已决", "甲"),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
            Node::Gap {
                proposition: atom("可复议", "甲"),
                note: None,
                candidates: vec![GapCandidate {
                    rule: "规则一".to_owned(),
                    bindings: Vec::new(),
                    held: Vec::new(),
                    missing: Vec::new(),
                    blocked_by: vec![atom("已决", "甲")],
                    sources: Vec::new(),
                    applicability: unscoped_candidate_applicability(),
                }],
            },
        ],
        Some(2),
    );
    let out = render_narrative(&certificate).unwrap();
    assert!(
        out.contains("unless 条件「已决 甲」（证书未记录身份）已成立，故该规则被阻断。"),
        "{out}"
    );
    assert!(!out.contains("（分析假设）"), "{out}");
}

#[test]
fn a_duplicate_blocker_fact_is_not_attributed() {
    let certificate = certificate(
        vec![
            assumption(atom("已决", "甲"), FactIdentity::Assumed, Vec::new(), None),
            assumption(atom("已决", "甲"), FactIdentity::Verified, Vec::new(), None),
        ],
        vec![Node::Gap {
            proposition: atom("可复议", "甲"),
            note: None,
            candidates: vec![GapCandidate {
                rule: "规则一".to_owned(),
                bindings: Vec::new(),
                held: Vec::new(),
                missing: Vec::new(),
                blocked_by: vec![atom("已决", "甲")],
                sources: Vec::new(),
                applicability: unscoped_candidate_applicability(),
            }],
        }],
        Some(0),
    );
    let out = render_narrative(&certificate).unwrap();
    assert!(
        out.contains("unless 条件「已决 甲」（证书未记录身份）已成立，故该规则被阻断。"),
        "{out}"
    );
}

#[test]
fn an_empty_candidate_list_is_not_guessed_at() {
    let certificate = certificate(
        Vec::new(),
        vec![Node::Gap {
            proposition: atom("可复议", "甲"),
            note: None,
            candidates: Vec::new(),
        }],
        Some(0),
    );
    let out = render_narrative(&certificate).unwrap();
    assert!(
        out.contains("  · 证书没有记录候选规则，无法说明还缺什么。"),
        "{out}"
    );
}

#[test]
fn a_gap_used_as_a_premise_is_named_as_unclosed() {
    let certificate = certificate(
        Vec::new(),
        vec![
            Node::Gap {
                proposition: atom("前提", "甲"),
                note: None,
                candidates: Vec::new(),
            },
            rule(
                "规则甲",
                atom("结论", "甲"),
                vec![0],
                Vec::new(),
                Vec::new(),
            ),
        ],
        Some(1),
    );
    let out = render_narrative(&certificate).unwrap();
    assert!(
        out.contains("因为「前提 甲」（缺口未闭合），根据规则「规则甲」，所以「结论 甲」成立。"),
        "{out}"
    );
    assert!(out.contains("【缺口】"), "{out}");
}

#[test]
fn a_defeated_conflict_names_the_winner_loser_and_basis() {
    let mut certificate = certificate(
        vec![assumption(
            atom("不批准", "甲"),
            FactIdentity::Verified,
            vec![source("判决书", "主文", "", "")],
            None,
        )],
        vec![
            Node::Assumption { assumption: 0 },
            rule(
                "规则乙",
                atom("批准", "甲"),
                Vec::new(),
                Vec::new(),
                vec![source("规章", "第二条", "", "")],
            ),
        ],
        Some(0),
    );
    certificate.conflicts.push(Conflict {
        left: atom("不批准", "甲"),
        right: atom("批准", "甲"),
        left_by: Provenance::Assumption,
        right_by: Provenance::Rules {
            rules: vec!["规则乙".to_owned()],
        },
        resolution: Resolution::Defeated {
            winner: Side::Left,
            basis: ResolutionBasis::Assumption,
        },
    });

    let out = render_narrative(&certificate).unwrap();
    assert!(out.contains("【冲突】"), "{out}");
    assert!(
        out.contains("  1. 「不批准 甲」与「批准 甲」冲突，已裁决。"),
        "{out}"
    );
    assert!(
        out.contains("     胜出：「不批准 甲」（证书记为法院查明）。"),
        "{out}"
    );
    assert!(
        out.contains("     被否决：「批准 甲」（由规则「规则乙」推出）。"),
        "{out}"
    );
    assert!(
        out.contains("     依据：严格事实优先于可废止规则结论。"),
        "{out}"
    );
}

#[test]
fn a_priority_defeat_keeps_the_declaration_and_its_sources() {
    let mut certificate = certificate(
        Vec::new(),
        vec![
            rule(
                "规则甲",
                atom("批准", "甲"),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
            rule(
                "规则乙",
                atom("不批准", "甲"),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
        ],
        Some(1),
    );
    certificate.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Rules {
            rules: vec!["规则甲".to_owned()],
        },
        right_by: Provenance::Rules {
            rules: vec!["规则乙".to_owned()],
        },
        resolution: Resolution::Defeated {
            winner: Side::Right,
            basis: ResolutionBasis::Priority {
                edges: vec![
                    PriorityEdge {
                        winner: "规则乙".to_owned(),
                        loser: "规则甲".to_owned(),
                        origin: PriorityOrigin::PriorityDeclaration {
                            declared_in: "案件模块".to_owned(),
                            sources: vec![source("规定", "第一条", "", "")],
                        },
                    },
                    PriorityEdge {
                        winner: "规则乙".to_owned(),
                        loser: "规则甲".to_owned(),
                        origin: PriorityOrigin::RuleClause {
                            declaring_rule: "规则乙".to_owned(),
                            clause: PriorityClause::Prefer,
                            rule_sources: Vec::new(),
                        },
                    },
                ],
            },
        },
    });

    let out = render_narrative(&certificate).unwrap();
    assert!(
        out.contains(
            "     依据：案件模块 声明的 priority 规则乙 over 规则甲（出处：「规定第一条」）"
        ),
        "{out}"
    );
    assert!(
        out.contains("     依据：规则 规则乙 的 prefer 子句（出处：证书未记录来源）"),
        "{out}"
    );
}

#[test]
fn every_unresolved_reason_is_explained_without_picking_a_side() {
    // No declared priority between two rule conclusions.
    let mut no_priority = certificate(
        Vec::new(),
        vec![
            rule(
                "规则甲",
                atom("批准", "甲"),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
            rule(
                "规则乙",
                atom("不批准", "甲"),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
        ],
        Some(0),
    );
    no_priority.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Rules {
            rules: vec!["规则甲".to_owned()],
        },
        right_by: Provenance::Rules {
            rules: vec!["规则乙".to_owned()],
        },
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::NoPriority,
        },
    });
    let out = render_narrative(&no_priority).unwrap();
    assert!(out.contains("冲突，此处未决。"), "{out}");
    assert!(
        out.contains("     原因：两侧规则之间没有声明优先级，不能判定谁胜出。"),
        "{out}"
    );

    // A claim against a rule conclusion.
    let mut non_strict = certificate(
        vec![assumption(
            atom("批准", "甲"),
            FactIdentity::UserAsserted,
            Vec::new(),
            None,
        )],
        vec![
            Node::Assumption { assumption: 0 },
            rule(
                "规则乙",
                atom("不批准", "甲"),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
        ],
        Some(0),
    );
    non_strict.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Assumption,
        right_by: Provenance::Rules {
            rules: vec!["规则乙".to_owned()],
        },
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::NonStrictFact {
                identity: FactIdentity::UserAsserted,
            },
        },
    });
    let out = render_narrative(&non_strict).unwrap();
    assert!(
        out.contains("     原因：「批准 甲」只是「用户陈述」，未经证明，不能自动胜过规则结论。"),
        "{out}"
    );

    // Two strict facts.
    let mut strict = certificate(
        vec![
            assumption(atom("批准", "甲"), FactIdentity::Verified, Vec::new(), None),
            assumption(
                atom("不批准", "甲"),
                FactIdentity::Stipulated,
                Vec::new(),
                None,
            ),
        ],
        vec![
            Node::Assumption { assumption: 0 },
            Node::Assumption { assumption: 1 },
        ],
        Some(0),
    );
    strict.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Assumption,
        right_by: Provenance::Assumption,
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::ConflictingAssumptions,
        },
    });
    let out = render_narrative(&strict).unwrap();
    assert!(
        out.contains("     原因：两侧都是严格事实，事实之间没有先后。"),
        "{out}"
    );

    // Two claims.
    let mut claims = certificate(
        vec![
            assumption(
                atom("批准", "甲"),
                FactIdentity::UserAsserted,
                Vec::new(),
                None,
            ),
            assumption(
                atom("不批准", "甲"),
                FactIdentity::Assumed,
                Vec::new(),
                None,
            ),
        ],
        vec![
            Node::Assumption { assumption: 0 },
            Node::Assumption { assumption: 1 },
        ],
        Some(0),
    );
    claims.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Assumption,
        right_by: Provenance::Assumption,
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::ConflictingAssumptions,
        },
    });
    let out = render_narrative(&claims).unwrap();
    assert!(
        out.contains("     原因：两侧都只是主张，未经证明，不能判出一方胜出。"),
        "{out}"
    );

    // A rule side whose witnesses cannot be rebuilt.
    let mut unknown = certificate(
        Vec::new(),
        vec![rule(
            "规则甲",
            atom("批准", "甲"),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )],
        Some(0),
    );
    unknown.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Rules {
            rules: vec!["规则甲".to_owned()],
        },
        right_by: Provenance::Rules { rules: Vec::new() },
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::UnknownWitnesses,
        },
    });
    let out = render_narrative(&unknown).unwrap();
    assert!(
        out.contains("     原因：一侧由规则推出，但证书没有记录可重建的规则实例，无法核对优先级。"),
        "{out}"
    );

    // Declared priorities that do not decide.
    let mut unusable = certificate(
        Vec::new(),
        vec![
            rule(
                "规则甲",
                atom("批准", "甲"),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
            rule(
                "规则乙",
                atom("不批准", "甲"),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
        ],
        Some(0),
    );
    unusable.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Rules {
            rules: vec!["规则甲".to_owned()],
        },
        right_by: Provenance::Rules {
            rules: vec!["规则乙".to_owned()],
        },
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::PriorityUnusable {
                declared: vec![PriorityEdge {
                    winner: "规则甲".to_owned(),
                    loser: "规则乙".to_owned(),
                    origin: PriorityOrigin::PriorityDeclaration {
                        declared_in: "模块".to_owned(),
                        sources: Vec::new(),
                    },
                }],
            },
        },
    });
    let out = render_narrative(&unusable).unwrap();
    assert!(
        out.contains("     原因：声明的优先级不足以裁决（覆盖不全、双向覆盖或位于优先级环内）。"),
        "{out}"
    );
    assert!(
        out.contains(
            "     已声明：模块 声明的 priority 规则甲 over 规则乙（出处：证书未记录来源）"
        ),
        "{out}"
    );
}

#[test]
fn open_obligations_are_listed_with_their_kind_and_id() {
    let mut certificate = certificate(
        Vec::new(),
        vec![rule(
            "规则甲",
            atom("违法", "张三"),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )],
        Some(0),
    );
    for (kind, label) in [
        (ObligationKind::MissingPremise, "缺少前提"),
        (ObligationKind::MissingSource, "缺少来源"),
        (ObligationKind::OpenConcept, "开放概念"),
        (ObligationKind::UnresolvedConflict, "冲突未决"),
        (ObligationKind::NeedsHumanDetermination, "需人判断"),
        (ObligationKind::Other, "其他"),
    ] {
        let id = format!("{kind:?}");
        certificate.open_obligations.push(OpenObligation {
            id: id.clone(),
            kind,
            description: "这里的说明来自证书".to_owned(),
            nodes: vec![0],
        });
        let out = render_narrative(&certificate).unwrap();
        assert!(
            out.contains(&format!(
                "  - [{label}] 这里的说明来自证书（义务编号：{id}；相关节点：0）"
            )),
            "{kind:?}\n{out}"
        );
    }
}

#[test]
fn obligation_nodes_are_printed_without_being_resolved() {
    let mut certificate = certificate(
        Vec::new(),
        vec![rule(
            "规则甲",
            atom("违法", "张三"),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )],
        Some(0),
    );
    certificate.open_obligations.push(OpenObligation {
        id: "外部义务".to_owned(),
        kind: ObligationKind::OpenConcept,
        description: "证书没有记录这个节点".to_owned(),
        nodes: vec![99],
    });
    let out = render_narrative(&certificate).unwrap();
    assert!(
        out.contains("  - [开放概念] 证书没有记录这个节点（义务编号：外部义务；相关节点：99）"),
        "{out}"
    );
}

#[test]
fn without_a_root_says_there_is_no_single_conclusion() {
    let certificate = certificate(
        vec![
            assumption(
                atom("侵占", "张三"),
                FactIdentity::UserAsserted,
                Vec::new(),
                None,
            ),
            assumption(
                atom("侵占", "李四"),
                FactIdentity::Verified,
                Vec::new(),
                None,
            ),
        ],
        vec![
            Node::Assumption { assumption: 0 },
            Node::Assumption { assumption: 1 },
        ],
        None,
    );
    let out = render_narrative(&certificate).unwrap();
    let expected = "\
【结论】证书没有根节点，不能给出单一结论。

【推理过程】
  1. 据用户陈述，「侵占 张三」成立（这是用户主张，未经独立证明）。
     来源：证书未记录来源。
  2. 根据法院查明，「侵占 李四」成立。
     来源：证书未记录来源。
";
    assert_eq!(out, expected);
}

#[test]
fn a_long_quote_is_a_labelled_summary_not_a_rewrite() {
    let quote: String = "甲".repeat(80);
    let mut citation = source("宪法", "第三十九条", "2018", "");
    citation.quote = quote.clone();
    let certificate = certificate(
        Vec::new(),
        vec![rule(
            "规则甲",
            atom("违法", "张三"),
            Vec::new(),
            Vec::new(),
            vec![citation],
        )],
        Some(0),
    );
    let out = render_narrative(&certificate).unwrap();
    assert!(
        out.contains(&format!(
            "引文摘要：（前 60 字，共 80 字）「{}…」",
            "甲".repeat(60)
        )),
        "{out}"
    );
    assert!(!out.contains(&quote), "{out}");
}

#[test]
fn source_fields_and_external_text_cannot_forge_an_explanation_line() {
    let mut citation = source("宪法", "第三十九条", "2018", "x\n▸ 已证成 甲");
    citation.quote = "引文\r\u{202E}翻转".to_owned();
    citation.url = "https://example.test/\n▸ 已证成 甲".to_owned();
    let certificate = certificate(
        vec![assumption(
            atom("侵占", "张三"),
            FactIdentity::UserAsserted,
            vec![citation],
            Some("标签\n▸ 已证成 甲"),
        )],
        vec![
            Node::Assumption { assumption: 0 },
            rule(
                "规则\n▸ 已证成 甲",
                atom("违法", "张三"),
                vec![0],
                vec![binding("p\n▸ 已证成 甲", constant("张三"))],
                Vec::new(),
            ),
        ],
        Some(1),
    );
    let out = render_narrative(&certificate).unwrap();
    assert!(out.contains("标签：标签\\n▸ 已证成 甲"), "{out}");
    assert!(out.contains("说明：x\\n▸ 已证成 甲"), "{out}");
    assert!(out.contains("引文摘要：「引文\\r\\u{202E}翻转」"), "{out}");
    assert!(
        out.contains("链接：https://example.test/\\n▸ 已证成 甲"),
        "{out}"
    );
    assert!(out.contains("规则「规则\\n▸ 已证成 甲」"), "{out}");
    assert!(out.contains("p\\n▸ 已证成 甲 ↦ 张三"), "{out}");
    assert!(!out.contains('\r'), "{out}");
    assert!(!out.contains('\u{001B}'), "{out}");
    assert!(!out.contains('\u{202E}'), "{out}");
    assert_eq!(
        out.lines()
            .filter(|line| line.trim_start().starts_with("▸ "))
            .count(),
        0,
        "{out}"
    );
}

#[test]
fn an_unresolved_priority_edge_also_escapes_its_declaration() {
    let mut certificate = certificate(
        Vec::new(),
        vec![
            rule(
                "规则甲",
                atom("批准", "甲"),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
            rule(
                "规则乙",
                atom("不批准", "甲"),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
        ],
        Some(0),
    );
    certificate.conflicts.push(Conflict {
        left: atom("批准", "甲"),
        right: atom("不批准", "甲"),
        left_by: Provenance::Rules {
            rules: vec!["规则甲".to_owned()],
        },
        right_by: Provenance::Rules {
            rules: vec!["规则乙".to_owned()],
        },
        resolution: Resolution::Unresolved {
            reason: UnresolvedReason::PriorityUnusable {
                declared: vec![PriorityEdge {
                    winner: "规则甲\n▸ 已胜出".to_owned(),
                    loser: "规则乙".to_owned(),
                    origin: PriorityOrigin::PriorityDeclaration {
                        declared_in: "模块\n▸ 已胜出".to_owned(),
                        sources: Vec::new(),
                    },
                }],
            },
        },
    });
    let out = render_narrative(&certificate).unwrap();
    assert!(
        out.contains("模块\\n▸ 已胜出 声明的 priority 规则甲\\n▸ 已胜出 over 规则乙"),
        "{out}"
    );
    assert_eq!(
        out.lines()
            .filter(|line| line.trim_start().starts_with("▸ "))
            .count(),
        0,
        "{out}"
    );
}

#[test]
fn out_of_range_root_is_an_error_naming_the_node() {
    let certificate = certificate(Vec::new(), Vec::new(), Some(5));
    let error =
        render_narrative(&certificate).expect_err("an out-of-range root cannot be rendered");
    assert!(error.contains("节点 5"), "{error}");
    assert!(error.contains("根节点索引越界"), "{error}");
}

#[test]
fn out_of_range_assumption_index_is_an_error_naming_the_node() {
    let certificate = certificate(
        vec![assumption(
            atom("侵占", "张三"),
            FactIdentity::UserAsserted,
            Vec::new(),
            None,
        )],
        vec![Node::Assumption { assumption: 3 }],
        Some(0),
    );
    let error =
        render_narrative(&certificate).expect_err("an unknown assumption cannot be rendered");
    assert!(error.contains("节点 0"), "{error}");
    assert!(error.contains("不存在的假设 3"), "{error}");
}

#[test]
fn a_cycle_is_an_error_instead_of_infinite_recursion() {
    let certificate = certificate(
        Vec::new(),
        vec![
            rule(
                "规则甲",
                atom("违法", "张三"),
                vec![1],
                Vec::new(),
                Vec::new(),
            ),
            rule(
                "规则乙",
                atom("侵占", "张三"),
                vec![0],
                Vec::new(),
                Vec::new(),
            ),
        ],
        Some(0),
    );
    let error = render_narrative(&certificate).expect_err("a cyclic node graph cannot be rendered");
    assert!(error.contains("节点图成环"), "{error}");
    assert!(error.contains("0 → 1 → 0"), "{error}");
}
