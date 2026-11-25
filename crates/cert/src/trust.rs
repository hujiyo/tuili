//! Trust labels derived from a certificate.
//!
//! The five labels are a **derived view**: they are computed from
//! [`Certificate`] fields only and are never written into the certificate JSON.
//! The format version therefore stays at v7, and `:cert` output is unchanged.
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
//! | [`TrustLabel::Verified`] (`已验证`) | `root` proves a proposition (not a gap, and no gap is reachable from it); every assumption reachable from the root is `verified` or `stipulated`; the proof uses no interpretation application; `open_obligations` is empty and no `conflicts` entry is unresolved. The summary names this "模型内" and says it does not mean legally correct. |
//! | [`TrustLabel::DependsOnAssumption`] (`依赖假设`) | `root` proves a proposition, and its reachable proof graph uses at least one `user_asserted`, `assumed` or `disputed` assumption, or at least one [`Node::InterpretationApplication`]. The evidence counts each identity and the interpretation applications, so a mixed strict/claim proof says which facts are the user's. |
//! | [`TrustLabel::FactNeedsEvidence`] (`事实待举证`) | `root` is missing or is a [`Node::Gap`] (or a gap is reachable from a non-gap root). The evidence names the root gap, the `MissingPremise` obligations and the number of missing premises the root gap candidates record. |
//! | [`TrustLabel::DisputeUnresolved`] (`争点未决`) | a `conflicts` entry has [`crate::Resolution::Unresolved`], or an obligation is `UnresolvedConflict`. This label means logic cannot decide; it is not produced by an open concept or a case extension. |
//! | [`TrustLabel::NeedsLawyerJudgment`] (`需律师判断`) | an obligation is `OpenConcept` or `NeedsHumanDetermination` (the `local-extension` case-extension obligation is counted separately). This label means the concept's meaning needs a human, or the rule's source was not audited by this project; it does not absorb an unresolved conflict. |
//!
//! The primary label is the first label a reader should see; it does not make
//! the other labels disappear. A certificate can carry `争点未决` and
//! `需律师判断` at the same time (an unresolved conflict over an open concept),
//! and the summary names every additional label as `另含：…`.
//!
//! A proved root that records an obligation of a kind listed by none of the
//! five rules (`missing_source` or `other`) both blocks `已验证` and earns no
//! other label; [`derive_trust`] then reports that the certificate's fields
//! cannot support a label instead of guessing one.
//!
//! A gap root can never be `已验证`; an unresolved conflict always makes
//! `争点未决` appear, even when another label also applies; and a label never
//! asserts legal correctness. `已验证` is explicitly a proof-relative statement:
//! the certificate is valid and used only strict facts, which is still not a
//! claim that a court would reach the same conclusion.

use std::collections::BTreeSet;

use std_deduce_kernel::env::escape_control;

use crate::model::{Certificate, FactIdentity, Node, NodeId, ObligationKind};
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
}

impl TrustReport {
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

    // Walk the proof graph below the root. The certificate lists facts used by
    // the whole fixed point, so a claim unrelated to the root must not make the
    // root's label conditional.
    let mut reachable: BTreeSet<NodeId> = BTreeSet::new();
    let mut reachable_assumptions: BTreeSet<usize> = BTreeSet::new();
    let mut reachable_gaps: Vec<NodeId> = Vec::new();
    let mut interpretation_applications = 0usize;
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
                Node::Assumption { assumption } => {
                    reachable_assumptions.insert(*assumption);
                }
                Node::RuleApplication { premises, .. } => {
                    pending.extend(premises.iter().copied());
                }
                Node::InterpretationApplication { premise, .. } => {
                    interpretation_applications += 1;
                    pending.push(*premise);
                }
                Node::Gap { .. } => reachable_gaps.push(id),
            }
        }
    }
    reachable_gaps.sort_unstable();

    let root_proved = certificate.root.is_some() && !root_is_gap && reachable_gaps.is_empty();

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
    let claims = user_asserted_facts + assumed_facts + disputed_facts;
    let strict_facts = verified_facts + stipulated_facts;
    let uses_claim = claims > 0 || interpretation_applications > 0;

    let mut missing_premise_obligations = 0usize;
    let mut open_concept_obligations = 0usize;
    let mut unresolved_conflict_obligations = 0usize;
    let mut needs_human_obligations = 0usize;
    let mut local_extension_obligations = 0usize;
    let mut open_concept_ids: Vec<String> = Vec::new();
    let mut needs_human_ids: Vec<String> = Vec::new();
    for obligation in &certificate.open_obligations {
        match obligation.kind {
            ObligationKind::MissingPremise => missing_premise_obligations += 1,
            ObligationKind::MissingSource | ObligationKind::Other => {}
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
    let open_obligations = certificate.open_obligations.len();
    let open_judgement_obligations =
        open_concept_obligations + needs_human_obligations + local_extension_obligations;

    let unresolved_conflicts = certificate
        .conflicts
        .iter()
        .filter(|conflict| {
            matches!(
                conflict.resolution,
                crate::model::Resolution::Unresolved { .. }
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

    // 争点未决: logic cannot decide an unresolved conflict. Open concepts and
    // a case extension are `需律师判断`, not this label; when an unresolved
    // conflict also touches an open concept both labels apply.
    let dispute = unresolved_conflicts > 0 || unresolved_conflict_obligations > 0;
    if dispute {
        let mut evidence = Vec::new();
        if unresolved_conflicts > 0 {
            evidence.push(format!("证书记录未决冲突 {unresolved_conflicts} 项"));
        } else {
            evidence.push(format!(
                "证书记录冲突未决义务 {unresolved_conflict_obligations} 项"
            ));
        }
        entries.push((TrustLabel::DisputeUnresolved, evidence));
    }

    // 事实待举证: the root itself is missing or a gap, or the graph below a
    // non-gap root contains a gap. The root gap candidates and the
    // MissingPremise obligations are the evidence that a premise is what is
    // missing.
    if !root_proved {
        let mut evidence = Vec::new();
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
            Some(_) => evidence.push(format!("根的可达推导中有 {} 处缺口", reachable_gaps.len())),
        }
        if missing_premise_obligations > 0 {
            evidence.push(format!(
                "证书记录缺少前提义务 {missing_premise_obligations} 项"
            ));
        }
        if claims > 0 {
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

    // 已验证: a proved root that used only strict facts, with no open
    // obligation and no unresolved conflict. The evidence keeps the caveat in
    // the output itself, so the label cannot be read as legal correctness.
    if root_proved && !uses_claim && open_obligations == 0 && unresolved_conflicts == 0 {
        let mut evidence = Vec::new();
        if strict_facts > 0 {
            evidence.push(format!(
                "模型内：根推导只使用严格事实（法院查明 {verified_facts} 条、双方无争议 {stipulated_facts} 条）"
            ));
        } else {
            evidence.push("模型内：根推导没有使用任何事实".to_owned());
        }
        evidence.push("无未决义务、无未决冲突".to_owned());
        evidence.push("这不等同于法律上正确".to_owned());
        entries.push((TrustLabel::Verified, evidence));
    }

    // Every certificate earns at least one label: an unproved root is
    // `事实待举证`, and a proved root is `已验证`, `依赖假设` or `争点未决`.
    // Reaching here with no label means the certificate's fields cannot support
    // any conclusion, which is an explicit error rather than a guessed label.
    if entries.is_empty() {
        return Err("证书的字段无法派生任何信任标签".to_owned());
    }

    let labels: Vec<TrustLabel> = entries.iter().map(|(label, _)| *label).collect();
    let evidence = entries;
    Ok(TrustReport { labels, evidence })
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
