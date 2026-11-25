//! Trust labels derived from a certificate.
//!
//! The five labels are a **derived view**: they are computed from
//! [`Certificate`] fields only and are never written into the certificate JSON.
//! The labels do not add a certificate field: the format stays at v9, and the
//! witness table is not read as a label source.
//! No renderer guesses a label from printed text, and no label is read from an
//! obligation's description; a rule here is a named condition over the fields
//! below.
//!
//! [`derive_trust`] is the one function that decides every label. Its output is
//! a [`TrustReport`] with the labels in precedence order, the evidence behind
//! each label, and a one-line summary. The mapping is:
//!
//! | label | fields that produce it |
//! |---|---|
//! | [`TrustLabel::Verified`] (`已验证`) | `root` proves a proposition (not a gap, and no gap is reachable from it); every assumption reachable from the root is `verified` or `stipulated`; the proof uses no interpretation application; no **root-relevant** obligation and no **root-relevant** unresolved conflict. The summary names this "模型内" and says it does not mean legally correct; an unrelated branch's obligation or conflict does not remove this label. |
//! | [`TrustLabel::DependsOnAssumption`] (`依赖假设`) | `root` proves a proposition, and its reachable proof graph uses at least one `user_asserted`, `assumed` or `disputed` assumption (including the identity an `axiom_instance` records for the universal fact it instantiates), or at least one [`Node::InterpretationApplication`]. The evidence counts each identity and the interpretation applications, so a mixed strict/claim proof says which facts are the user's. |
//! | [`TrustLabel::FactNeedsEvidence`] (`事实待举证`) | `root` is missing or is a [`Node::Gap`] (or a gap is reachable from a non-gap root), or a root-relevant `MissingPremise` obligation is recorded. The evidence names the root gap, the root gap candidates' missing premises and the relevant `MissingPremise` obligations. |
//! | [`TrustLabel::DisputeUnresolved`] (`争点未决`) | a root-relevant `conflicts` entry has [`crate::Resolution::Unresolved`], a root-relevant `UnresolvedConflict` obligation, or a root-relevant `MissingSource` / `Other` obligation (the certificate still has an unresolved item). Open concepts and case extensions are not this label. |
//! | [`TrustLabel::NeedsLawyerJudgment`] (`需律师判断`) | a root-relevant obligation is `OpenConcept` or `NeedsHumanDetermination` (the `local-extension` case-extension obligation is counted separately). This label means the concept's meaning needs a human, or the rule's source was not audited by this project; it does not absorb an unresolved conflict. |
//!
//! A conflict, obligation or fact is root-relevant only when it is attached to
//! the proof graph below [`Certificate::root`]. A conflict side is relevant
//! when its proposition has the structural key of a proposition on a reachable
//! node, or when its [`Provenance::Rules`] witness is a rule applied on that
//! graph, or when its [`Provenance::Axiom`] witness is a universal fact the
//! graph instantiated, or when its [`Provenance::Interpretation`] witness is an
//! interpretation the graph applied. An assumption identity adds nothing
//! structural: its proposition is already on the graph. A universal instance's
//! recorded identity is counted exactly like an assumption identity, so a
//! proof that instantiates a `user_asserted` universal fact is never labelled
//! `已验证`. The comparison uses
//! [`crate::expression_key`], which ignores binder names but does not normalize
//! with a kernel environment, so the label layer never needs an environment.
//!
//! An obligation with a non-empty `nodes` list is relevant only when one of
//! those nodes is reachable from the root. An empty `nodes` list means the
//! certificate did not localize the obligation; it is treated as relevant
//! rather than silently dropped. `UnresolvedConflict` is the exception because
//! it duplicates a `conflicts` record and carries no nodes: when the certificate
//! records conflicts, those records decide relevance; a lone unattached
//! `UnresolvedConflict` obligation (no `conflicts` entries at all) is relevant.
//!
//! The primary label is the first label a reader should see; it does not make
//! the other labels disappear. A certificate can carry `争点未决` and
//! `需律师判断` at the same time (an unresolved conflict over an open concept),
//! and the summary names every additional label as `另含：…`.
//!
//! A gap root can never be `已验证`; an unresolved conflict always makes
//! `争点未决` appear, even when another label also applies; and a label never
//! asserts legal correctness. `已验证` is explicitly a proof-relative statement:
//! the certificate is valid and used only strict facts, which is still not a
//! claim that a court would reach the same conclusion.

use std::collections::BTreeSet;

use std_deduce_kernel::env::escape_control;
use std_deduce_kernel::Expr;

use crate::expr::CertExpr;
use crate::key::expression_key;
use crate::model::{
    Certificate, Conflict, FactIdentity, Node, NodeId, ObligationKind, OpenObligation, Provenance,
};
use crate::render::validate;

/// The stable identifier of the case-extension obligation the CLI records when
/// a proof applies a rule the case file declared under
/// `--closed-env --allow-case-rules`.
pub const LOCAL_EXTENSION_OBLIGATION_ID: &str = "local-extension";

/// One of the five trust labels.
///
/// The variant order is the report's precedence order: the first label a
/// certificate earns is its primary label.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TrustLabel {
    /// `需律师判断`: an open concept, a human judgement, or a case extension
    /// whose rule source this project did not audit.
    NeedsLawyerJudgment,
    /// `争点未决`: logic cannot decide an unresolved conflict.
    DisputeUnresolved,
    /// `事实待举证`: the root (or the graph below it) is a gap.
    FactNeedsEvidence,
    /// `依赖假设`: the proof rests on a claim or an interpretation.
    DependsOnAssumption,
    /// `已验证`: a proof under strict facts only, with nothing left open.
    Verified,
}

impl TrustLabel {
    /// The Chinese label printed by `:why`, `:explain` and `:labels`.
    pub fn name_zh(self) -> &'static str {
        match self {
            TrustLabel::NeedsLawyerJudgment => "需律师判断",
            TrustLabel::DisputeUnresolved => "争点未决",
            TrustLabel::FactNeedsEvidence => "事实待举证",
            TrustLabel::DependsOnAssumption => "依赖假设",
            TrustLabel::Verified => "已验证",
        }
    }
}

/// The labels a certificate earns, their evidence, and the one-line summary
/// shared by every output command.
///
/// `labels()` returns at least one label; `primary()` is the first one. The
/// evidence for a label is deterministic: it counts certificate fields and
/// sorts obligation ids, so two computations of the same certificate produce
/// byte-identical text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustReport {
    labels: Vec<TrustLabel>,
    evidence: Vec<(TrustLabel, Vec<String>)>,
    root_proved: bool,
    reachable: BTreeSet<NodeId>,
}

impl TrustReport {
    /// Whether the certificate's root is proved.
    ///
    /// This is the same judgement the labels use: the root exists, is not a
    /// gap, and no gap is reachable from it. A report that has to say whether
    /// the conclusion is reachable uses this instead of re-walking the graph.
    pub fn root_proved(&self) -> bool {
        self.root_proved
    }

    /// Every node reachable from the root along premises.
    ///
    /// The set is empty when the certificate has no root. It is the reachable
    /// proof graph the labels are computed over, exposed so a derived report
    /// can distinguish the root's facts and rules from records attached to
    /// other branches without recomputing the walk.
    pub fn reachable_nodes(&self) -> &BTreeSet<NodeId> {
        &self.reachable
    }

    /// The label that comes first in precedence order.
    pub fn primary(&self) -> TrustLabel {
        self.labels
            .first()
            .copied()
            .expect("derive_trust always produces at least one label")
    }

    /// Every label, in precedence order.
    pub fn labels(&self) -> &[TrustLabel] {
        &self.labels
    }

    /// Whether this report contains `label`.
    pub fn contains(&self, label: TrustLabel) -> bool {
        self.labels.contains(&label)
    }

    /// The evidence lines for `label`, or an empty slice when the label does
    /// not apply.
    pub fn evidence(&self, label: TrustLabel) -> &[String] {
        self.evidence
            .iter()
            .find(|(entry, _)| *entry == label)
            .map(|(_, lines)| lines.as_slice())
            .unwrap_or(&[])
    }

    /// The one-line summary `:why` and `:explain` print near their result line.
    ///
    /// The primary label's evidence is joined with `；`; every other label is
    /// named as `另含：…`, so an unresolved conflict stays visible even when
    /// `需律师判断` is the primary label.
    pub fn summary(&self) -> String {
        let mut details = self.evidence(self.primary()).to_vec();
        if self.labels.len() > 1 {
            let others = self.labels[1..]
                .iter()
                .map(|label| label.name_zh())
                .collect::<Vec<_>>()
                .join("、");
            details.push(format!("另含：{others}"));
        }
        if details.is_empty() {
            format!("信任：{}", self.primary().name_zh())
        } else {
            format!(
                "信任：{}（{}）",
                self.primary().name_zh(),
                details.join("；")
            )
        }
    }
}

/// Derive every trust label of `certificate` from its own fields.
///
/// This is the single function that defines the labels. The module
/// documentation lists the field-to-label mapping; this function only reads the
/// certificate, never an environment, a reasoner or printed text. An invalid
/// node reference or a cyclic proof graph is an error naming the node; it is
/// not rounded down to a label.
pub fn derive_trust(certificate: &Certificate) -> Result<TrustReport, String> {
    validate(certificate)?;

    // Walk the proof graph below the root. The certificate lists facts and
    // obligations used by the whole fixed point, so an unrelated claim, gap,
    // conflict or case extension must not make the root's label conditional.
    let mut reachable: BTreeSet<NodeId> = BTreeSet::new();
    let root_is_gap = certificate
        .root
        .and_then(|root| certificate.nodes.get(root))
        .is_some_and(|node| matches!(node, Node::Gap { .. }));
    if let Some(root) = certificate.root {
        let mut pending = vec![root];
        while let Some(id) = pending.pop() {
            if !reachable.insert(id) {
                continue;
            }
            match &certificate.nodes[id] {
                Node::Assumption { .. } => {}
                Node::RuleApplication { premises, .. } => {
                    pending.extend(premises.iter().copied());
                }
                Node::InterpretationApplication { premise, .. } => {
                    pending.push(*premise);
                }
                Node::AxiomInstance { .. } | Node::Gap { .. } => {}
            }
        }
    }

    // The structural facts that decide whether a certificate-wide record is
    // about the root: every proposition stated on a reachable node, the rules
    // those nodes apply, and the interpretations they apply. A conflict side
    // is relevant when its proposition is one of these statements or when its
    // rule/interpretation witness is one of these steps.
    let mut reachable_assumptions: BTreeSet<usize> = BTreeSet::new();
    let mut reachable_gaps: Vec<NodeId> = Vec::new();
    let mut interpretation_applications = 0usize;
    let mut reachable_propositions: BTreeSet<String> = BTreeSet::new();
    let mut reachable_rules: BTreeSet<String> = BTreeSet::new();
    let mut reachable_interpretations: BTreeSet<usize> = BTreeSet::new();
    let mut reachable_axioms: BTreeSet<String> = BTreeSet::new();
    let mut axiom_identities: Vec<FactIdentity> = Vec::new();
    for id in &reachable {
        match &certificate.nodes[*id] {
            Node::Assumption { assumption } => {
                reachable_assumptions.insert(*assumption);
            }
            Node::RuleApplication {
                rule, conclusion, ..
            } => {
                reachable_propositions.insert(expression_key(&Expr::from(conclusion)));
                reachable_rules.insert(rule.clone());
            }
            Node::InterpretationApplication {
                interpretation,
                conclusion,
                ..
            } => {
                interpretation_applications += 1;
                reachable_propositions.insert(expression_key(&Expr::from(conclusion)));
                reachable_interpretations.insert(*interpretation);
            }
            Node::AxiomInstance {
                axiom,
                identity,
                conclusion,
                ..
            } => {
                reachable_propositions.insert(expression_key(&Expr::from(conclusion)));
                reachable_axioms.insert(axiom.clone());
                axiom_identities.push(*identity);
            }
            Node::Gap { proposition, .. } => {
                reachable_propositions.insert(expression_key(&Expr::from(proposition)));
                reachable_gaps.push(*id);
            }
        }
    }
    for index in &reachable_assumptions {
        let entry = certificate.assumptions.get(*index).ok_or_else(|| {
            format!(
                "根推导引用了不存在的假设 {index}：证书只有 {} 条假设",
                certificate.assumptions.len()
            )
        })?;
        reachable_propositions.insert(expression_key(&Expr::from(&entry.proposition)));
    }
    reachable_gaps.sort_unstable();
    let root_proved = certificate.root.is_some() && !root_is_gap && reachable_gaps.is_empty();

    // Fact identities on the reachable proof graph.
    let mut verified_facts = 0usize;
    let mut stipulated_facts = 0usize;
    let mut user_asserted_facts = 0usize;
    let mut assumed_facts = 0usize;
    let mut disputed_facts = 0usize;
    for index in reachable_assumptions {
        let entry = certificate.assumptions.get(index).ok_or_else(|| {
            format!(
                "根推导引用了不存在的假设 {index}：证书只有 {} 条假设",
                certificate.assumptions.len()
            )
        })?;
        match entry.identity {
            FactIdentity::Verified => verified_facts += 1,
            FactIdentity::Stipulated => stipulated_facts += 1,
            FactIdentity::UserAsserted => user_asserted_facts += 1,
            FactIdentity::Assumed => assumed_facts += 1,
            FactIdentity::Disputed => disputed_facts += 1,
        }
    }
    // A universal instance rests on the universal fact's assertion just as a
    // premise fact does. Counting its identity keeps a proof that instantiates
    // a `user_asserted` universal from being labelled `已验证`.
    for identity in axiom_identities {
        match identity {
            FactIdentity::Verified => verified_facts += 1,
            FactIdentity::Stipulated => stipulated_facts += 1,
            FactIdentity::UserAsserted => user_asserted_facts += 1,
            FactIdentity::Assumed => assumed_facts += 1,
            FactIdentity::Disputed => disputed_facts += 1,
        }
    }
    let claims = user_asserted_facts + assumed_facts + disputed_facts;
    let strict_facts = verified_facts + stipulated_facts;
    let uses_claim = claims > 0 || interpretation_applications > 0;

    // Only obligations attached to the reachable proof graph count. An empty
    // `nodes` list means the certificate did not localize the obligation, so it
    // is treated as relevant rather than silently dropped. `UnresolvedConflict`
    // is the one exception: it duplicates a `conflicts` record, and when the
    // certificate records conflicts those records decide relevance.
    let mut missing_premise_obligations = 0usize;
    let mut open_concept_obligations = 0usize;
    let mut unresolved_conflict_obligations = 0usize;
    let mut needs_human_obligations = 0usize;
    let mut local_extension_obligations = 0usize;
    let mut missing_source_obligations = 0usize;
    let mut other_obligations = 0usize;
    let mut open_concept_ids: Vec<String> = Vec::new();
    let mut needs_human_ids: Vec<String> = Vec::new();
    for obligation in &certificate.open_obligations {
        if !obligation_is_reachable(certificate, obligation, &reachable) {
            continue;
        }
        match obligation.kind {
            ObligationKind::MissingPremise => missing_premise_obligations += 1,
            ObligationKind::MissingSource => missing_source_obligations += 1,
            ObligationKind::Other => other_obligations += 1,
            ObligationKind::OpenConcept => {
                open_concept_obligations += 1;
                open_concept_ids.push(escape_control(&obligation.id));
            }
            ObligationKind::UnresolvedConflict => unresolved_conflict_obligations += 1,
            ObligationKind::NeedsHumanDetermination => {
                if obligation.id == LOCAL_EXTENSION_OBLIGATION_ID {
                    local_extension_obligations += 1;
                } else {
                    needs_human_obligations += 1;
                    needs_human_ids.push(escape_control(&obligation.id));
                }
            }
        }
    }
    open_concept_ids.sort();
    needs_human_ids.sort();
    let open_judgement_obligations =
        open_concept_obligations + needs_human_obligations + local_extension_obligations;
    let relevant_obligations = missing_premise_obligations
        + open_concept_obligations
        + unresolved_conflict_obligations
        + needs_human_obligations
        + local_extension_obligations
        + missing_source_obligations
        + other_obligations;

    // An unresolved conflict affects the root only when one side is a
    // reachable statement or is supported by a rule the root applied.
    let unresolved_conflicts = certificate
        .conflicts
        .iter()
        .filter(|conflict| {
            matches!(
                conflict.resolution,
                crate::model::Resolution::Unresolved { .. }
            ) && conflict_is_reachable(
                conflict,
                &reachable_propositions,
                &reachable_rules,
                &reachable_interpretations,
                &reachable_axioms,
            )
        })
        .count();

    let mut entries: Vec<(TrustLabel, Vec<String>)> = Vec::new();

    // 需律师判断: an open concept, or a rule source outside this project's
    // audit (`local-extension`). It does not absorb an unresolved conflict:
    // `争点未决` is its own label and both can apply.
    if open_judgement_obligations > 0 {
        let mut evidence = Vec::new();
        if open_concept_obligations > 0 {
            evidence.push(format!(
                "开放概念义务 {open_concept_obligations} 项：{}",
                quoted_ids(&open_concept_ids)
            ));
        }
        if local_extension_obligations > 0 {
            evidence.push(format!(
                "案件扩展义务 {local_extension_obligations} 项：`{LOCAL_EXTENSION_OBLIGATION_ID}`"
            ));
        }
        if needs_human_obligations > 0 {
            evidence.push(format!(
                "需人判断义务 {needs_human_obligations} 项：{}",
                quoted_ids(&needs_human_ids)
            ));
        }
        entries.push((TrustLabel::NeedsLawyerJudgment, evidence));
    }

    // 争点未决: logic cannot decide an unresolved conflict, or the certificate
    // records an obligation this mapping leaves unresolved (`missing_source`,
    // `other`). Open concepts and a case extension are `需律师判断`, not this
    // label; when an unresolved conflict also touches an open concept both
    // labels apply.
    let dispute = unresolved_conflicts > 0
        || unresolved_conflict_obligations > 0
        || missing_source_obligations > 0
        || other_obligations > 0;
    if dispute {
        let mut evidence = Vec::new();
        if unresolved_conflicts > 0 {
            evidence.push(format!(
                "证书记录与根相关的未决冲突 {unresolved_conflicts} 项"
            ));
        }
        if unresolved_conflict_obligations > 0 {
            evidence.push(format!(
                "证书记录冲突未决义务 {unresolved_conflict_obligations} 项"
            ));
        }
        if missing_source_obligations > 0 || other_obligations > 0 {
            let mut kinds = Vec::new();
            if missing_source_obligations > 0 {
                kinds.push(format!("缺少来源 {missing_source_obligations} 项"));
            }
            if other_obligations > 0 {
                kinds.push(format!("其他 {other_obligations} 项"));
            }
            evidence.push(format!("证书记录还有未解决事项（{}）", kinds.join("、")));
        }
        entries.push((TrustLabel::DisputeUnresolved, evidence));
    }

    // 事实待举证: the root itself is missing or a gap, the graph below a
    // non-gap root contains a gap, or the certificate records a missing-premise
    // obligation attached to the root. The root gap candidates and the
    // MissingPremise obligations are the evidence that a premise is what is
    // missing.
    let fact_needs_evidence = !root_proved || missing_premise_obligations > 0;
    if fact_needs_evidence {
        let mut evidence = Vec::new();
        if !root_proved {
            match certificate.root {
                None => evidence.push("证书没有根节点，没有可证明的结论".to_owned()),
                Some(root) if root_is_gap => {
                    evidence.push("根为缺口，结论未获证明".to_owned());
                    if let Some(Node::Gap { candidates, .. }) = certificate.nodes.get(root) {
                        let missing: usize = candidates
                            .iter()
                            .map(|candidate| candidate.missing.len())
                            .sum();
                        if missing > 0 {
                            evidence.push(format!("根缺口的候选规则共缺少前提 {missing} 条"));
                        }
                    }
                }
                Some(_) => {
                    evidence.push(format!("根的可达推导中有 {} 处缺口", reachable_gaps.len()))
                }
            }
        }
        if missing_premise_obligations > 0 {
            if root_proved {
                evidence.push(format!(
                    "根已证明，但证书记录与根相关的缺少前提义务 {missing_premise_obligations} 项"
                ));
            } else {
                evidence.push(format!(
                    "证书记录与根相关的缺少前提义务 {missing_premise_obligations} 项"
                ));
            }
        }
        if !root_proved && claims > 0 {
            evidence.push(format!(
                "根推导还使用了主张：{}",
                identity_counts(user_asserted_facts, assumed_facts, disputed_facts)
            ));
        }
        entries.push((TrustLabel::FactNeedsEvidence, evidence));
    }

    // 依赖假设: a proved root whose proof uses a claim or an interpretation.
    // The evidence names every non-strict identity and the strict facts it is
    // mixed with, so a reader can tell what is the user's claim.
    if root_proved && uses_claim {
        let mut evidence = Vec::new();
        if claims > 0 {
            evidence.push(identity_counts(
                user_asserted_facts,
                assumed_facts,
                disputed_facts,
            ));
        }
        if interpretation_applications > 0 {
            evidence.push(format!("解释应用 {interpretation_applications} 处"));
        }
        if strict_facts > 0 {
            evidence.push(format!(
                "同时使用严格事实（法院查明 {verified_facts} 条、双方无争议 {stipulated_facts} 条）"
            ));
        }
        entries.push((TrustLabel::DependsOnAssumption, evidence));
    }

    // 已验证: a proved root that used only strict facts, with no relevant
    // obligation and no relevant unresolved conflict. Unrelated certificate
    // records do not count, or every case with an unrelated branch would lose
    // this label. The evidence keeps the caveat in the output itself, so the
    // label cannot be read as legal correctness.
    if root_proved && !uses_claim && relevant_obligations == 0 && unresolved_conflicts == 0 {
        let mut evidence = Vec::new();
        if strict_facts > 0 {
            evidence.push(format!(
                "模型内：根推导只使用严格事实（法院查明 {verified_facts} 条、双方无争议 {stipulated_facts} 条）"
            ));
        } else {
            evidence.push("模型内：根推导没有使用任何事实".to_owned());
        }
        evidence.push("根可达子图无未决义务、无未决冲突".to_owned());
        evidence.push("这不等同于法律上正确".to_owned());
        entries.push((TrustLabel::Verified, evidence));
    }

    // Every certificate earns at least one label by the mapping above: an
    // unproved root is `事实待举证`, and each obligation kind maps to one of
    // the other labels. Reaching here with no label means the certificate's
    // fields contradict that mapping, which is an explicit error rather than a
    // guessed label.
    if entries.is_empty() {
        return Err("证书的字段无法派生任何信任标签".to_owned());
    }

    let labels: Vec<TrustLabel> = entries.iter().map(|(label, _)| *label).collect();
    let evidence = entries;
    Ok(TrustReport {
        labels,
        evidence,
        root_proved,
        reachable,
    })
}

/// Whether a conflict is about the root's proof graph.
///
/// A side is relevant when its proposition is a statement on a reachable node,
/// or when its rule/interpretation witness is a step the root applied. Both
/// sides are checked: a conflict is relevant when either side is. An
/// unresolved conclusion cannot be a premise of a proving step, so matching the
/// reachable propositions and applied witnesses is sufficient.
fn conflict_is_reachable(
    conflict: &Conflict,
    propositions: &BTreeSet<String>,
    rules: &BTreeSet<String>,
    interpretations: &BTreeSet<usize>,
    axioms: &BTreeSet<String>,
) -> bool {
    conflict_side_is_reachable(
        &conflict.left,
        &conflict.left_by,
        propositions,
        rules,
        interpretations,
        axioms,
    ) || conflict_side_is_reachable(
        &conflict.right,
        &conflict.right_by,
        propositions,
        rules,
        interpretations,
        axioms,
    )
}

fn conflict_side_is_reachable(
    proposition: &CertExpr,
    provenance: &Provenance,
    propositions: &BTreeSet<String>,
    rules: &BTreeSet<String>,
    interpretations: &BTreeSet<usize>,
    axioms: &BTreeSet<String>,
) -> bool {
    if propositions.contains(&expression_key(&Expr::from(proposition))) {
        return true;
    }
    match provenance {
        // The proposition check above already covers an assumption node on the
        // reachable graph; the identity adds nothing structural.
        Provenance::Assumption => false,
        Provenance::Rules { rules: witnesses } => witnesses.iter().any(|rule| rules.contains(rule)),
        Provenance::Axiom { axiom } => axioms.contains(axiom),
        Provenance::Interpretation { interpretation } => interpretations.contains(interpretation),
    }
}

/// Whether an open obligation belongs to the root's proof graph.
///
/// A non-empty `nodes` list is authoritative: the obligation is relevant only
/// when one of those nodes is reachable from the root. An empty list means the
/// certificate did not localize the obligation; it is treated as relevant
/// rather than silently dropped, with one exception: an `unresolved_conflict`
/// obligation duplicates a `conflicts` record and carries no nodes, so when the
/// certificate records conflicts those conflict records decide relevance. A
/// lone unattached `unresolved_conflict` obligation (no conflict records at
/// all) is still relevant.
fn obligation_is_reachable(
    certificate: &Certificate,
    obligation: &OpenObligation,
    reachable: &BTreeSet<NodeId>,
) -> bool {
    if obligation.nodes.iter().any(|node| reachable.contains(node)) {
        return true;
    }
    if obligation.kind == ObligationKind::UnresolvedConflict {
        return obligation.nodes.is_empty() && certificate.conflicts.is_empty();
    }
    obligation.nodes.is_empty()
}

fn quoted_ids(ids: &[String]) -> String {
    if ids.is_empty() {
        return "证书未记录义务编号".to_owned();
    }
    ids.iter()
        .map(|id| format!("`{id}`"))
        .collect::<Vec<_>>()
        .join("、")
}

fn identity_counts(user_asserted: usize, assumed: usize, disputed: usize) -> String {
    let mut parts = Vec::new();
    if user_asserted > 0 {
        parts.push(format!("据用户陈述 {user_asserted} 条"));
    }
    if assumed > 0 {
        parts.push(format!("作为分析假设 {assumed} 条"));
    }
    if disputed > 0 {
        parts.push(format!("对方争议 {disputed} 条"));
    }
    parts.join("、")
}
