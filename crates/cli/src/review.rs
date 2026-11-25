//! The lawyer review report renderer (`:review`).
//!
//! This module turns data the session already has into a Markdown report a
//! practising lawyer can read. It is a **derived view**, not a new inference
//! and not legal advice. Every sentence is read from one of four inputs:
//!
//! * the certificate v8 the query path produced (`:why` / `:cert` build the
//!   same certificate),
//! * the reasoner's gap trees (the root's tree and the `:issues` scan),
//! * the rules' declared burden of proof (`RulePleading`, the same map
//!   `:gap` / `:explain` use), and
//! * the trust labels `std_deduce_cert::derive_trust` computes from the
//!   certificate.
//!
//! The environment is consulted only for two certificate-derived
//! recomputations: the open-concept dependency (the certificate checker uses
//! the same function) and kernel equivalence, so "the root's issue" is not
//! compared by printed text.
//!
//! ## Sections
//!
//! The report has a fixed section order and a fixed item order inside each
//! section: rules by rule name, facts and conflicts by structural key, gap
//! trees by structural goal key, nodes by node id. There is no timestamp, path,
//! or session state in the report, so running `:review` twice on the same case
//! produces byte-identical Markdown.
//!
//! ## Wording and escaping
//!
//! The header says the report is a model-internal derivation report and not
//! legal advice. Labels are described as model-internal certainty; the report
//! never says a conclusion is legally correct. A missing source, an undeclared
//! burden or standard, and a missing event time are written out as such; none
//! of them is defaulted. Every external value (propositions, rule names,
//! labels, sources, obligations, paths in the caller's line) goes through
//! `escape_control`, so a newline or a control character in a source note
//! cannot inject a Markdown heading or another line. Redaction is not
//! implemented yet: names and places keep the text the proposition and the
//! source carry.

use std::collections::{BTreeMap, BTreeSet};

use std_deduce_cert::{
    expression_key, Certificate, FactIdentity, Node, NodeId, ObligationKind, OpenConceptDependency,
    PriorityClause, PriorityEdge, PriorityOrigin, Provenance, Resolution, ResolutionBasis,
    RiskReport, Side, Source, TrustLabel, TrustReport, UnresolvedReason,
    LOCAL_EXTENSION_OBLIGATION_ID,
};
use std_deduce_kernel::conv::convertible;
use std_deduce_kernel::env::{escape_control, RulePleading};
use std_deduce_kernel::norm::normalize;
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{Ctx, Env, Expr, Name};
use std_deduce_reason::{GapLimit, GapStatus, GapTree, IssueScan};

/// The label order of the trust table, independent of the report's primary
/// label. Every report lists all five labels with either their evidence or a
/// sentence saying they do not apply.
const ALL_LABELS: [TrustLabel; 5] = [
    TrustLabel::NeedsLawyerJudgment,
    TrustLabel::DisputeUnresolved,
    TrustLabel::FactNeedsEvidence,
    TrustLabel::DependsOnAssumption,
    TrustLabel::Verified,
];

/// One rule as the report cites it.
struct RuleRecord {
    /// Rule-application nodes on the root's reachable proof graph.
    root_nodes: Vec<NodeId>,
    /// Sources the certificate records for this rule's applications. Never
    /// filled from the environment: an applied rule with no recorded source
    /// must read "证书未记录来源".
    cert_sources: Vec<Source>,
    /// Applicability texts of the certificate's rule applications.
    cert_verdicts: BTreeSet<String>,
    /// Sources the current environment declares for this rule. This is a
    /// separate, recomputable result; for a gap candidate it is displayed as
    /// "来自当前环境声明（非证书记录）" and never mixed with `cert_sources`.
    env_sources: Vec<Source>,
    /// Applicability texts of the gap-tree candidates.
    gap_verdicts: BTreeSet<String>,
    /// Whether the rule appears as a gap candidate at all.
    in_gap: bool,
    /// The first non-positive applicability verdict, if any, for the question
    /// section. `None` means every recorded instance is `适用`.
    needs_applicability_review: Option<String>,
}

impl RuleRecord {
    fn new() -> Self {
        RuleRecord {
            root_nodes: Vec::new(),
            cert_sources: Vec::new(),
            cert_verdicts: BTreeSet::new(),
            env_sources: Vec::new(),
            gap_verdicts: BTreeSet::new(),
            in_gap: false,
            needs_applicability_review: None,
        }
    }

    fn push_cert_source(&mut self, source: &Source) {
        if !self.cert_sources.contains(source) {
            self.cert_sources.push(source.clone());
        }
    }

    fn push_env_source(&mut self, source: &Source) {
        if !self.env_sources.contains(source) {
            self.env_sources.push(source.clone());
        }
    }
}

/// One universal fact an instance on the root's proof graph came from.
///
/// The certificate records the instance (`axiom_instance`), its identity and
/// its sources; the report groups the instances of one declaration so a
/// reader sees which universal fact the proof leaned on.
struct AxiomInstanceRecord {
    /// Instance nodes on the root's reachable proof graph.
    root_nodes: Vec<NodeId>,
    /// The Chinese identity labels the instances are asserted under.
    identities: BTreeSet<String>,
    /// The instantiated conclusions, printed in a stable order.
    conclusions: BTreeSet<String>,
    /// Binding lists of the instances, printed in a stable order.
    bindings: BTreeSet<String>,
    /// `sources` the certificate records for the instances. Never filled from
    /// the environment: a missing certificate source stays missing.
    cert_sources: Vec<Source>,
}

impl AxiomInstanceRecord {
    fn new() -> Self {
        AxiomInstanceRecord {
            root_nodes: Vec::new(),
            identities: BTreeSet::new(),
            conclusions: BTreeSet::new(),
            bindings: BTreeSet::new(),
            cert_sources: Vec::new(),
        }
    }

    fn push_cert_source(&mut self, source: &Source) {
        if !self.cert_sources.contains(source) {
            self.cert_sources.push(source.clone());
        }
    }
}

/// One universal fact a gap tree lists as an axiom candidate.
///
/// The candidate's sources come from the current environment declaration, not
/// from the certificate, and are labelled as such; the refused ones carry the
/// reasoner's own refusal text.
struct AxiomCandidateRecord {
    /// Binding lists the candidate would use, printed in a stable order.
    bindings: BTreeSet<String>,
    /// Refusal reasons; empty means the instance was legal but not demanded.
    problems: BTreeSet<String>,
    /// Sources the current environment declares for the universal fact.
    env_sources: Vec<Source>,
}

impl AxiomCandidateRecord {
    fn new() -> Self {
        AxiomCandidateRecord {
            bindings: BTreeSet::new(),
            problems: BTreeSet::new(),
            env_sources: Vec::new(),
        }
    }

    fn push_env_source(&mut self, source: &Source) {
        if !self.env_sources.contains(source) {
            self.env_sources.push(source.clone());
        }
    }
}

/// Render the Markdown review report for one case.
///
/// `certificate` and `trust` are the same objects `:verify-cert` and
/// `:labels` would inspect; `root_gap` is the reasoner's recursive tree of the
/// queried conclusion and must be `None` when the root is proved. `issues` is
/// the `:issues` scan of the current fact set. `pleadings` is the declared
/// burden/standard map keyed by rule name.
///
/// A certificate whose root or node references are invalid is an error (the
/// CLI runs both certificate layers first); this renderer never fills a
/// missing field and never guesses a label.
pub(crate) fn render_review(
    env: &Env,
    certificate: &Certificate,
    trust: &TrustReport,
    dependency: Option<&OpenConceptDependency>,
    issues: &IssueScan,
    root_gap: Option<&GapTree>,
    pleadings: &BTreeMap<String, RulePleading>,
) -> Result<String, String> {
    // The risk themes are derived here from the same certificate the report
    // renders, so the caller cannot pass a different derivation's grading.
    let risk = std_deduce_cert::derive_risk(env, certificate)?;
    let mut out = String::new();
    write_header(&mut out);

    // The root's proposition, or an explicit statement that there is none.
    let root_proposition = match certificate.root {
        Some(root) => node_proposition_text(certificate, root)?,
        None => "本案推导没有结论命题".to_owned(),
    };
    let root_expr = certificate
        .root
        .map(|root| node_proposition(certificate, root).map(Expr::from))
        .transpose()?;

    // Stable order for everything the certificate may list in reasoner order.
    let mut issues_sorted: Vec<&GapTree> = issues.issues.iter().collect();
    issues_sorted.sort_by_key(|tree| expression_key(&tree.goal));

    let mut conflicts: Vec<&std_deduce_cert::Conflict> = certificate.conflicts.iter().collect();
    conflicts.sort_by_key(|conflict| {
        (
            expression_key(&Expr::from(&conflict.left)),
            expression_key(&Expr::from(&conflict.right)),
        )
    });

    let rules = collect_rules(certificate, trust, root_gap, &issues_sorted);
    let (axiom_instances, axiom_candidates) =
        collect_axioms(env, certificate, trust, root_gap, &issues_sorted);

    write_conclusion_section(
        &mut out,
        certificate,
        trust,
        dependency,
        &risk,
        &root_proposition,
    );

    // Sections are rendered in order; each records the item numbers the
    // question section cites, so a question can always point at an item the
    // report actually contains.
    let mut questions: Vec<Question> = Vec::new();
    let mut question_groups: BTreeMap<u8, Vec<Question>> = BTreeMap::new();

    write_issues_section(
        &mut out,
        env,
        &issues_sorted,
        issues,
        root_expr.as_ref(),
        &mut question_groups,
    )?;
    write_rules_section(
        &mut out,
        &rules,
        &axiom_instances,
        &axiom_candidates,
        &mut question_groups,
    );
    write_facts_section(
        &mut out,
        env,
        certificate,
        trust,
        root_gap,
        &issues_sorted,
        root_expr.as_ref(),
    )?;
    let gap_inputs = GapSection {
        env,
        root_gap,
        issues: &issues_sorted,
        root_expr: root_expr.as_ref(),
        pleadings,
    };
    write_gaps_section(&mut out, &gap_inputs, &mut question_groups)?;
    write_conflicts_section(&mut out, certificate, &conflicts, &mut question_groups);
    write_open_concepts_section(&mut out, env, certificate, dependency, &mut question_groups)?;

    // Flatten the groups in their fixed order: conflicts, open concepts,
    // human-determination obligations, case extensions, the root gap, issues,
    // rule applicability, and missing rule sources.
    for group in 0u8..=7 {
        if let Some(entries) = question_groups.remove(&group) {
            questions.extend(entries);
        }
    }
    write_questions_section(&mut out, &questions);

    Ok(out)
}

/// What the header says before any section.
fn write_header(out: &mut String) {
    out.push_str("# 律师复核报告\n\n");
    out.push_str(
        "> **本报告是模型内推导报告，不是法律意见。** \
         它只整理本案已有的推导、缺口、冲突与信任标签；\
         信任标签只表示模型内的确定性（例如「已验证」只表示结论在严格事实下已证明、\
         没有与结论相关的未决事项），不表示法律上正确，也不能代替律师对事实、\
         法律解释与计算结果的判断。\n\n",
    );
    out.push_str(
        "- 报告范围：本案推导、缺口展开、规则声明与信任标签；不新增推导，也不是法律意见。\n",
    );
    out.push_str(
        "- 隐私边界：命题与来源文本中的人名、地名等原样保留，本报告未做脱敏（脱敏尚未实现）。\n",
    );
}

/// The first section: conclusion, root reachability, and all five labels.
fn write_conclusion_section(
    out: &mut String,
    certificate: &Certificate,
    trust: &TrustReport,
    dependency: Option<&OpenConceptDependency>,
    risk: &RiskReport,
    root_proposition: &str,
) {
    begin_section(out, "## 一、结论与信任标签");
    out.push_str(&format!("**结论命题：**「{root_proposition}」\n"));
    let root_state = match certificate.root {
        None => "否（本案推导没有结论节点）".to_owned(),
        Some(root) if matches!(certificate.nodes.get(root), Some(Node::Gap { .. })) => {
            "否（结论未获证明）".to_owned()
        }
        Some(_) if trust.root_proved() => "是（结论已证明）".to_owned(),
        Some(_) => "否（结论的证明里仍有缺口）".to_owned(),
    };
    out.push_str(&format!(
        "**根是否可达（即本次推导是否证明了结论）：**{root_state}\n"
    ));
    out.push_str("信任标签（模型内确定性，不表示法律上正确）：\n");
    for label in ALL_LABELS {
        let name = label.name_zh();
        if trust.contains(label) {
            let evidence = label_evidence(certificate, trust, dependency, label);
            if evidence.is_empty() {
                out.push_str(&format!("- 「{name}」：成立\n"));
            } else {
                out.push_str(&format!("- 「{name}」：成立（{evidence}）\n"));
            }
        } else {
            out.push_str(&format!(
                "- 「{name}」：不成立（{}）\n",
                absent_label_reason(label)
            ));
        }
    }
    out.push_str("信任标签不涵盖时空适用性：规则实例的判定依据单独列在「规则与出处」。\n");
    // Risk themes are a second, independent view: they say what the case is
    // about, not whether the model may decide it. A low-risk case gets no line
    // (the report must not drown an ordinary case in noise); the hint for a
    // theory without `risk` declarations is a `:why` / `:explain` display aid,
    // not part of the lawyer report.
    if risk.is_high_risk() {
        if let Some(warning) = risk.warning_line() {
            out.push_str(&format!("{warning}\n"));
            for theme in risk.themes() {
                for evidence in risk.evidence(*theme) {
                    out.push_str(&format!("  依据：{evidence}\n"));
                }
            }
        }
    }
    out.push_str("\n声明：这是模型内推导，不是法律意见。\n");
}

/// A lawyer-facing evidence line for one trust label. The trust report's own
/// evidence for `需律师判断` names obligation ids; this renderer replaces them
/// with plain counts, so the report does not expose internal identifiers.
fn label_evidence(
    certificate: &Certificate,
    trust: &TrustReport,
    dependency: Option<&OpenConceptDependency>,
    label: TrustLabel,
) -> String {
    if label == TrustLabel::NeedsLawyerJudgment {
        let mut parts = Vec::new();
        let concepts = dependency
            .map(|dependency| dependency.concepts.len())
            .unwrap_or(0);
        if concepts > 0 {
            parts.push(format!("{concepts} 个开放概念需要解释"));
        }
        let extensions = certificate
            .open_obligations
            .iter()
            .filter(|obligation| {
                obligation.kind == ObligationKind::NeedsHumanDetermination
                    && obligation.id == LOCAL_EXTENSION_OBLIGATION_ID
                    && obligation_is_root_relevant(trust, obligation)
            })
            .count();
        if extensions > 0 {
            parts.push(format!("{extensions} 项案件扩展需要律师确认"));
        }
        let human = certificate
            .open_obligations
            .iter()
            .filter(|obligation| {
                obligation.kind == ObligationKind::NeedsHumanDetermination
                    && obligation.id != LOCAL_EXTENSION_OBLIGATION_ID
                    && obligation_is_root_relevant(trust, obligation)
            })
            .count();
        if human > 0 {
            parts.push(format!("{human} 项需要人判断的事项"));
        }
        return parts.join("；");
    }
    lawyer_evidence(&trust.evidence(label).join("；"))
}

/// Whether a recorded item is attached to the conclusion's proof. A non-empty
/// node list is authoritative; an empty list means the record was not localized
/// and is treated as relevant, the same conservative rule the labels use.
fn obligation_is_root_relevant(
    trust: &TrustReport,
    obligation: &std_deduce_cert::OpenObligation,
) -> bool {
    obligation.nodes.is_empty()
        || obligation
            .nodes
            .iter()
            .any(|node| trust.reachable_nodes().contains(node))
}

/// Rewrite the trust report's internal wording for a lawyer reader: no
/// certificate/root-graph jargon, no obligation ids. The label's meaning is
/// unchanged; only the display words are replaced.
fn lawyer_evidence(text: &str) -> String {
    let mut text = text.to_owned();
    for (from, to) in [
        ("根为缺口，结论未获证明", "结论未获证明"),
        ("证书记录", "本案推导"),
        ("与根相关", "与结论相关"),
        ("根可达子图", "结论的证明"),
        ("根推导", "结论的证明"),
        ("根为缺口", "结论未获证明"),
        ("根已证明", "结论已证明"),
        ("根缺口", "结论缺口"),
        ("未决义务", "未决事项"),
        ("缺少前提义务", "缺少证据事项"),
    ] {
        text = text.replace(from, to);
    }
    text
}

fn absent_label_reason(label: TrustLabel) -> &'static str {
    match label {
        TrustLabel::NeedsLawyerJudgment => {
            "本案推导没有与结论相关的开放概念、需人判断事项或案件扩展"
        }
        TrustLabel::DisputeUnresolved => "本案推导没有与结论相关的未决冲突，也没有其他未解决事项",
        TrustLabel::FactNeedsEvidence => "结论已证明，且没有与结论相关的缺少证据事项",
        TrustLabel::DependsOnAssumption => {
            "结论未证明，或结论的证明没有使用用户陈述、分析假设、对方争议或解释"
        }
        TrustLabel::Verified => "结论未证明，或结论的证明使用了主张，或仍有与结论相关的未决事项",
    }
}

/// The `:issues` conclusions, in structural-key order.
fn write_issues_section(
    out: &mut String,
    env: &Env,
    issues_sorted: &[&GapTree],
    issues: &IssueScan,
    root_expr: Option<&Expr>,
    questions: &mut BTreeMap<u8, Vec<Question>>,
) -> Result<(), String> {
    begin_section(out, "## 二、争点");
    out.push_str("争点：当前事实集下尚未证明、仍可被主张的结论。\n");
    if issues_sorted.is_empty() {
        out.push_str("当前事实集下没有可争的结论。\n");
    } else {
        out.push_str(&format!(
            "当前事实集下可争的结论 {} 条：\n",
            issues_sorted.len()
        ));
        for (index, tree) in issues_sorted.iter().enumerate() {
            write_issue_item(out, index + 1, tree, root_expr, env, questions)?;
        }
    }
    for limit in &issues.limits {
        out.push_str(&format!(
            "- 已截断：{}；其余未列出。\n",
            gap_limit_text(limit)
        ));
    }
    if !issues.uninstantiable.is_empty() {
        out.push_str(&format!(
            "- 另有 {} 条规则因当前事实集缺少可枚举的对象，或结论依赖前提的证明，无法逐一检查其结论：{}\n",
            issues.uninstantiable.len(),
            format_limited_names(&issues.uninstantiable)
        ));
    }
    if !issues.excluded.is_empty() {
        out.push_str(&format!(
            "- 另有 {} 条规则因时空适用性被排除，未作为争点检查：{}\n",
            issues.excluded.len(),
            issues
                .excluded
                .iter()
                .map(|excluded| format!("⟨{}⟩", escape_control(&excluded.rule)))
                .collect::<Vec<_>>()
                .join("、")
        ));
    }
    Ok(())
}

fn write_issue_item(
    out: &mut String,
    number: usize,
    tree: &GapTree,
    root_expr: Option<&Expr>,
    env: &Env,
    questions: &mut BTreeMap<u8, Vec<Question>>,
) -> Result<(), String> {
    let goal = expr_text(&tree.goal);
    let same_as_root = match root_expr {
        Some(root) => same_proposition(env, &tree.goal, root)?,
        None => false,
    };
    match tree.status {
        GapStatus::Unreachable => {
            let missing: usize = tree
                .candidates
                .iter()
                .map(|candidate| candidate.missing.len())
                .sum();
            let names = candidate_names(&tree.candidates);
            if same_as_root {
                out.push_str(&format!(
                    "{number}. 「{goal}」：与结论是同一命题；缺口见「缺口与举证」第 1 条。\n"
                ));
            } else {
                out.push_str(&format!(
                    "{number}. 「{goal}」：候选规则{names}；缺少前提合计 {missing} 条；缺口细节见「缺口与举证」。\n"
                ));
                questions.entry(5).or_default().push(Question {
                    text: format!("争点「{goal}」尚未证明；请确认是否主张该结论，以及由谁举证。"),
                    anchor: format!("「争点」第 {number} 条"),
                });
            }
        }
        GapStatus::Conflicted => {
            out.push_str(&format!(
                "{number}. 「{goal}」：它是一处未决冲突的一侧，模型不能判定；见「未决与冲突」。\n"
            ));
        }
        GapStatus::Defeated => {
            out.push_str(&format!(
                "{number}. 「{goal}」：它在已裁决的冲突中败出，按记录不再作为争点。\n"
            ));
        }
        GapStatus::InterpretedOnly => {
            out.push_str(&format!(
                "{number}. 「{goal}」：只由解释推出，规则阶段不消费解释结论，因此仍可争。\n"
            ));
        }
        other => {
            out.push_str(&format!(
                "{number}. 「{goal}」：缺口状态为{other:?}，无法在这里当作可争结论展开。\n"
            ));
        }
    }
    Ok(())
}

/// The rules the root proof and the report's gap trees use.
fn collect_rules(
    certificate: &Certificate,
    trust: &TrustReport,
    root_gap: Option<&GapTree>,
    issues_sorted: &[&GapTree],
) -> BTreeMap<String, RuleRecord> {
    let mut rules: BTreeMap<String, RuleRecord> = BTreeMap::new();
    for node_id in trust.reachable_nodes() {
        let Some(Node::RuleApplication {
            rule,
            sources,
            applicability,
            ..
        }) = certificate.nodes.get(*node_id)
        else {
            continue;
        };
        let record = rules.entry(rule.clone()).or_insert_with(RuleRecord::new);
        if !record.root_nodes.contains(node_id) {
            record.root_nodes.push(*node_id);
        }
        for source in sources {
            record.push_cert_source(source);
        }
        let verdict = cert_applicability_text(applicability);
        record.cert_verdicts.insert(verdict.clone());
        note_applicability_question(record, applicability.verdict, &verdict);
    }
    // Gap candidates are not applied rules. Their sources come from the gap
    // tree (the current environment declaration) and are kept in `env_sources`
    // so they cannot be mistaken for certificate-recorded sources.
    if let Some(tree) = root_gap {
        collect_gap_rules(tree, &mut rules);
    }
    for tree in issues_sorted {
        collect_gap_rules(tree, &mut rules);
    }
    rules
}

fn collect_gap_rules(tree: &GapTree, rules: &mut BTreeMap<String, RuleRecord>) {
    for candidate in &tree.candidates {
        let record = rules
            .entry(candidate.rule.to_string())
            .or_insert_with(RuleRecord::new);
        record.in_gap = true;
        for source in &candidate.sources {
            record.push_env_source(&Source::from(source));
        }
        let verdict = candidate.applicability.summary_zh();
        record.gap_verdicts.insert(verdict.clone());
        if !candidate.applicability.is_applicable() {
            record.needs_applicability_review.get_or_insert(verdict);
        }
        for premise in &candidate.missing {
            if let Some(child) = &premise.gap {
                collect_gap_rules(child, rules);
            }
        }
    }
}

/// The universal facts the root proof instantiated and the gap trees list.
///
/// Instances come from the certificate's reachable `axiom_instance` nodes:
/// their identity, conclusion, bindings and recorded sources are grouped by
/// the universal fact's name. Candidates come from the reasoner's gap trees
/// (root and `:issues`, nested levels included) — the same recursion the rule
/// candidates use — and their sources are read from the current environment
/// declaration, so a candidate's provenance is never mixed into the
/// certificate's sources.
fn collect_axioms(
    env: &Env,
    certificate: &Certificate,
    trust: &TrustReport,
    root_gap: Option<&GapTree>,
    issues_sorted: &[&GapTree],
) -> (
    BTreeMap<String, AxiomInstanceRecord>,
    BTreeMap<String, AxiomCandidateRecord>,
) {
    let mut instances: BTreeMap<String, AxiomInstanceRecord> = BTreeMap::new();
    for node_id in trust.reachable_nodes() {
        let Some(Node::AxiomInstance {
            axiom,
            identity,
            bindings,
            conclusion,
            sources,
        }) = certificate.nodes.get(*node_id)
        else {
            continue;
        };
        let record = instances
            .entry(axiom.clone())
            .or_insert_with(AxiomInstanceRecord::new);
        if !record.root_nodes.contains(node_id) {
            record.root_nodes.push(*node_id);
        }
        record
            .identities
            .insert(identity_text(*identity).0.to_owned());
        record.conclusions.insert(cert_expr_text(conclusion));
        record.bindings.insert(cert_bindings_text(bindings));
        for source in sources {
            record.push_cert_source(source);
        }
    }
    let mut candidates: BTreeMap<String, AxiomCandidateRecord> = BTreeMap::new();
    if let Some(tree) = root_gap {
        collect_gap_axioms(env, tree, &mut candidates);
    }
    for tree in issues_sorted {
        collect_gap_axioms(env, tree, &mut candidates);
    }
    (instances, candidates)
}

/// Collect one gap tree's axiom candidates and recurse into its nested
/// premises. Rule candidates and axiom candidates are separate lists; neither
/// recursion consumes the other.
fn collect_gap_axioms(
    env: &Env,
    tree: &GapTree,
    candidates: &mut BTreeMap<String, AxiomCandidateRecord>,
) {
    for candidate in &tree.axiom_candidates {
        let record = candidates
            .entry(candidate.axiom.to_string())
            .or_insert_with(AxiomCandidateRecord::new);
        record
            .bindings
            .insert(format_candidate_bindings(&candidate.bindings));
        match &candidate.problem {
            Some(problem) => {
                record.problems.insert(escape_control(problem));
            }
            None => {
                record
                    .problems
                    .insert("可由该全称公理实例化；当前推导没有触发它".to_owned());
            }
        }
        if let Some(decl) = env.get(candidate.axiom.as_ref()) {
            for source in &decl.sources {
                record.push_env_source(&Source::from(source));
            }
        }
    }
    for candidate in &tree.candidates {
        for premise in &candidate.missing {
            if let Some(child) = &premise.gap {
                collect_gap_axioms(env, child, candidates);
            }
        }
    }
}

/// One certificate binding list as `p ↦ 张三`; an empty list is stated rather
/// than left blank.
fn cert_bindings_text(bindings: &[std_deduce_cert::Binding]) -> String {
    if bindings.is_empty() {
        return "无绑定变量".to_owned();
    }
    bindings
        .iter()
        .map(|binding| {
            format!(
                "{} ↦ {}",
                escape_control(&binding.parameter),
                cert_expr_text(&binding.value)
            )
        })
        .collect::<Vec<_>>()
        .join("、")
}

/// One reasoner axiom-candidate binding list as `p ↦ 张三`.
fn format_candidate_bindings(bindings: &[(Name, Expr)]) -> String {
    if bindings.is_empty() {
        return "无绑定变量".to_owned();
    }
    bindings
        .iter()
        .map(|(parameter, value)| format!("{} ↦ {}", parameter, expr_text(value)))
        .collect::<Vec<_>>()
        .join("、")
}

fn note_applicability_question(
    record: &mut RuleRecord,
    verdict: std_deduce_cert::ApplicabilityVerdict,
    text: &str,
) {
    if verdict == std_deduce_cert::ApplicabilityVerdict::Applicable {
        return;
    }
    record
        .needs_applicability_review
        .get_or_insert_with(|| text.to_owned());
}

/// Section three: every rule, its sources and its recorded applicability.
fn write_rules_section(
    out: &mut String,
    rules: &BTreeMap<String, RuleRecord>,
    axiom_instances: &BTreeMap<String, AxiomInstanceRecord>,
    axiom_candidates: &BTreeMap<String, AxiomCandidateRecord>,
    questions: &mut BTreeMap<u8, Vec<Question>>,
) {
    begin_section(out, "## 三、规则与出处");
    out.push_str(
        "规则与出处只列本案结论的证明实际用到的规则、缺口中的候选规则，以及证明用到的全称公理实例与缺口列出的全称公理候选。\n",
    );
    if rules.is_empty() && axiom_instances.is_empty() && axiom_candidates.is_empty() {
        out.push_str("本案推导没有用到任何规则或全称公理。\n");
        return;
    }
    if rules.is_empty() {
        out.push_str("本案推导没有用到任何规则。\n");
    }
    let mut number = 0usize;
    for (name, record) in rules {
        number += 1;
        let number_label = number;
        out.push_str(&format!("{number}. 规则「{}」\n", escape_control(name)));
        if record.root_nodes.is_empty() {
            out.push_str("   - 用于结论的证明：否（只作为缺口候选规则）\n");
        } else {
            out.push_str("   - 用于结论的证明：是\n");
        }
        if !record.root_nodes.is_empty() {
            out.push_str(&format_source_line(
                "证书出处",
                "   ",
                &record.cert_sources,
                "证书未记录来源",
            ));
        }
        if record.in_gap {
            let label = "缺口候选出处（来自当前环境声明，非证书记录）";
            out.push_str(&format_source_line(
                label,
                "   ",
                &record.env_sources,
                "当前环境声明未记录来源",
            ));
        }
        // Certificate applications and gap candidates use different inputs, so
        // only one of the two lists is shown: a root-applied rule's certificate
        // text wins; a candidate-only rule shows the gap tree's summary. The
        // two wordings are never both printed for the same rule.
        if !record.cert_verdicts.is_empty() {
            for verdict in &record.cert_verdicts {
                out.push_str(&format!("   - 适用性：{}\n", verdict));
            }
        } else if !record.gap_verdicts.is_empty() {
            for verdict in &record.gap_verdicts {
                out.push_str(&format!("   - 适用性：{}\n", verdict));
            }
        } else {
            out.push_str("   - 适用性：没有记录判定。\n");
        }
        if record.root_nodes.is_empty() && record.env_sources.is_empty() {
            questions
                .entry(7)
                .or_default()
                .push(Question {
                    text: format!(
                        "缺口候选规则「{}」在当前环境声明里没有记录来源；请补充可核对的来源（文本、条号、版本、管辖、引文）。",
                        escape_control(name)
                    ),
                    anchor: format!("「规则与出处」第 {number_label} 条"),
                });
        } else if !record.root_nodes.is_empty() && record.cert_sources.is_empty() {
            questions
                .entry(7)
                .or_default()
                .push(Question {
                    text: format!(
                        "规则「{}」在证书记录里没有来源；请补充可核对的来源（文本、条号、版本、管辖、引文）。",
                        escape_control(name)
                    ),
                    anchor: format!("「规则与出处」第 {number_label} 条"),
                });
        }
        if let Some(verdict) = &record.needs_applicability_review {
            questions.entry(6).or_default().push(Question {
                text: format!(
                    "规则「{}」的时空适用性为{}；请确认该规则是否适用于本案的事件时间与地点。",
                    escape_control(name),
                    verdict
                ),
                anchor: format!("「规则与出处」第 {number_label} 条"),
            });
        }
    }
    // Universal instances the proof used. The certificate records the identity,
    // the bindings, the substituted conclusion and the declaration's sources;
    // the report prints them instead of silently dropping an elimination step
    // that is not a rule.
    if !axiom_instances.is_empty() {
        out.push_str("\n全称公理实例（证书记录）：\n");
        for (name, record) in axiom_instances {
            number += 1;
            out.push_str(&format!("{number}. 全称公理「{}」\n", escape_control(name)));
            for identity in &record.identities {
                out.push_str(&format!("   - 断言身份：{identity}\n"));
            }
            for bindings in &record.bindings {
                out.push_str(&format!("   - 绑定：{bindings}\n"));
            }
            for conclusion in &record.conclusions {
                out.push_str(&format!("   - 实例结论：{conclusion}\n"));
            }
            out.push_str(&format_source_line(
                "证书出处",
                "   ",
                &record.cert_sources,
                "证书未记录来源",
            ));
            out.push_str(
                "   - 适用性：公理实例没有前提事实，证书不为它记录适用性判定；它的结论由全称公理按绑定替换得到。\n",
            );
        }
    }
    // Universal facts a gap tree could have instantiated. These are diagnostics
    // from the current environment declaration, not certificate steps, and are
    // labelled as such.
    if !axiom_candidates.is_empty() {
        out.push_str("\n全称公理候选（缺口诊断，来自当前环境声明，非证书记录）：\n");
        for (name, record) in axiom_candidates {
            number += 1;
            out.push_str(&format!("{number}. 全称公理「{}」\n", escape_control(name)));
            for bindings in &record.bindings {
                out.push_str(&format!("   - 绑定：{bindings}\n"));
            }
            for problem in &record.problems {
                if problem.starts_with("可由该全称公理实例化") {
                    out.push_str(&format!("   - {problem}\n"));
                } else {
                    out.push_str(&format!("   - 未实例化：{problem}\n"));
                }
            }
            out.push_str(&format_source_line(
                "当前环境声明出处",
                "   ",
                &record.env_sources,
                "当前环境声明未记录来源",
            ));
        }
    }
}

/// The facts the certificate records, each with its identity.
fn write_facts_section(
    out: &mut String,
    env: &Env,
    certificate: &Certificate,
    trust: &TrustReport,
    root_gap: Option<&GapTree>,
    issues_sorted: &[&GapTree],
    root_expr: Option<&Expr>,
) -> Result<(), String> {
    begin_section(out, "## 四、事实账本");
    out.push_str(
        "事实账本区分事实身份：法院查明与双方无争议是严格事实；用户陈述与分析假设是主张，\
         不是证明；对方争议只记录对方的主张，不参与推导。\n",
    );
    if certificate.assumptions.is_empty() {
        out.push_str("本案推导没有记录任何假设事实。\n");
    } else {
        let reachable_assumptions: BTreeSet<usize> = trust
            .reachable_nodes()
            .iter()
            .filter_map(|node_id| match certificate.nodes.get(*node_id) {
                Some(Node::Assumption { assumption }) => Some(*assumption),
                _ => None,
            })
            .collect();
        let mut root_held = BTreeSet::new();
        if let Some(tree) = root_gap {
            collect_tree_held(tree, &mut root_held);
        }
        let mut issue_held = BTreeSet::new();
        for tree in issues_sorted {
            collect_tree_held(tree, &mut issue_held);
        }

        let mut ordered: Vec<(usize, String)> = certificate
            .assumptions
            .iter()
            .enumerate()
            .map(|(index, entry)| (index, expression_key(&Expr::from(&entry.proposition))))
            .collect();
        ordered.sort_by(|a, b| a.1.cmp(&b.1).then_with(|| a.0.cmp(&b.0)));
        for (index, _) in ordered {
            let entry = &certificate.assumptions[index];
            let proposition = cert_expr_text(&entry.proposition);
            let (identity, strictness) = identity_text(entry.identity);
            let relation = if reachable_assumptions.contains(&index) {
                "用于结论的证明".to_owned()
            } else if root_held.contains(&expression_key(&Expr::from(&entry.proposition))) {
                "结论缺口已掌握的材料（缺口未闭合，不能当作证明）".to_owned()
            } else if issue_held.contains(&expression_key(&Expr::from(&entry.proposition))) {
                "争点缺口已掌握的材料（缺口未闭合，不能当作证明）".to_owned()
            } else {
                "未用于结论的证明（推导的其他部分）".to_owned()
            };
            out.push_str(&format!(
                "- 「{proposition}」：身份：{identity}（{strictness}）；与结论的关系：{relation}\n"
            ));
            if let Some(label) = &entry.label {
                out.push_str(&format!("  - 标签：{}\n", escape_control(label)));
            }
            let occurred_at = entry
                .occurred_at
                .as_ref()
                .map(|value| escape_control(value))
                .unwrap_or_else(|| "未记录".to_owned());
            let occurred_in = entry
                .occurred_in
                .as_ref()
                .map(|value| escape_control(value))
                .unwrap_or_else(|| "未记录".to_owned());
            out.push_str(&format!(
                "  - 发生时间：{occurred_at}；发生地：{occurred_in}\n"
            ));
            out.push_str(&format_source_line(
                "来源",
                "  ",
                &entry.sources,
                "证书未记录来源",
            ));
        }
    }

    out.push_str("缺口命题（不是事实，只是缺少的证据）：\n");
    if root_gap.is_none() && issues_sorted.is_empty() {
        out.push_str("- 无。结论已证明，当前事实集下也没有可争结论。\n");
    } else {
        if let Some(tree) = root_gap {
            out.push_str(&format!(
                "- 「{}」〔缺口〕：结论未获证明；见「缺口与举证」第 1 条。\n",
                expr_text(&tree.goal)
            ));
        }
        for tree in issues_sorted {
            if tree.status != GapStatus::Unreachable {
                continue;
            }
            let same_as_root = match root_expr {
                Some(root) => same_proposition(env, &tree.goal, root)?,
                None => false,
            };
            if same_as_root {
                continue;
            }
            out.push_str(&format!(
                "- 「{}」〔缺口〕：争点缺口；见「缺口与举证」。\n",
                expr_text(&tree.goal)
            ));
        }
    }
    Ok(())
}

/// The inputs of section five. Grouped so the renderer keeps one context
/// object instead of a long argument list.
struct GapSection<'a> {
    env: &'a Env,
    root_gap: Option<&'a GapTree>,
    issues: &'a [&'a GapTree],
    root_expr: Option<&'a Expr>,
    pleadings: &'a BTreeMap<String, RulePleading>,
}

/// Section five: every gap with what it lacks and who must prove it.
///
/// The root's gap tree and every contestable conclusion's gap tree are expanded
/// recursively with the reasoner's own tree: its depth, node and rule-attempt
/// limits are already applied, and each node's limit marker is printed where it
/// stopped the expansion.
fn write_gaps_section(
    out: &mut String,
    inputs: &GapSection<'_>,
    questions: &mut BTreeMap<u8, Vec<Question>>,
) -> Result<(), String> {
    let env = inputs.env;
    let root_gap = inputs.root_gap;
    let issues_sorted = inputs.issues;
    let root_expr = inputs.root_expr;
    let pleadings = inputs.pleadings;
    begin_section(out, "## 五、缺口与举证");
    out.push_str(
        "缺口：一条命题没有被任何可用的推导闭合，它和冲突是两回事。\
         全称公理候选：能实例化该命题的全称事实，绑定值与拒绝原因都会列出。\
         举证责任：谁应当提出证据；证明标准：证据应达到的程度。\
         证明标准只是标签，不量化；未声明的字段写作未声明。\n",
    );
    let mut number = 0usize;
    let mut wrote_any = false;
    if let Some(tree) = root_gap {
        number += 1;
        wrote_any = true;
        write_root_gap_item(out, tree, number, pleadings)?;
        if tree.status == GapStatus::Unreachable {
            questions
                .entry(4)
                .or_default()
                .push(Question {
                    text: format!(
                        "结论「{}」未获证明；请确认缺少的证据是否存在，以及报告所列的举证责任与证明标准是否适用。",
                        expr_text(&tree.goal)
                    ),
                    anchor: format!("「缺口与举证」第 {number} 条"),
                });
        }
    }

    for tree in issues_sorted {
        let same_as_root = match root_expr {
            Some(root) => same_proposition(env, &tree.goal, root)?,
            None => false,
        };
        if matches!(tree.status, GapStatus::Unreachable) && !same_as_root {
            number += 1;
            wrote_any = true;
            out.push_str(&format!(
                "{number}. 争点「{}」的缺口\n",
                expr_text(&tree.goal)
            ));
            write_gap_body(out, tree, "   ", pleadings);
        }
    }

    if !wrote_any {
        if issues_sorted.is_empty() {
            out.push_str("结论已证明，当前事实集下也没有可争结论，因此没有缺口。\n");
        } else {
            out.push_str("结论已证明；当前争点都不是可展开的缺口，因此没有缺口。\n");
        }
    }
    Ok(())
}

fn write_root_gap_item(
    out: &mut String,
    tree: &GapTree,
    number: usize,
    pleadings: &BTreeMap<String, RulePleading>,
) -> Result<(), String> {
    match tree.status {
        GapStatus::Unreachable => {
            out.push_str(&format!(
                "{number}. 结论「{}」未获证明（缺口）\n",
                expr_text(&tree.goal)
            ));
            write_gap_body(out, tree, "   ", pleadings);
            Ok(())
        }
        GapStatus::Conflicted => {
            out.push_str(&format!(
                "{number}. 结论「{}」处于未决冲突（缺口）\n   - 该命题处于未决冲突，不能作为缺口展开；见「未决与冲突」。\n",
                expr_text(&tree.goal)
            ));
            Ok(())
        }
        GapStatus::Defeated => {
            out.push_str(&format!(
                "{number}. 结论「{}」在已裁决的冲突中败出（缺口）\n   - 按冲突记录，它不作为已证明的结论；见「未决与冲突」。\n",
                expr_text(&tree.goal)
            ));
            Ok(())
        }
        GapStatus::InterpretedOnly => {
            out.push_str(&format!(
                "{number}. 结论「{}」只由解释推出（缺口）\n   - 解释推出的结论不能作为规则的已证明前提，因此仍不算证明；见「规则与出处」。\n",
                expr_text(&tree.goal)
            ));
            Ok(())
        }
        GapStatus::Proved => {
            Err("内部状态错误：根被报告为缺口，但缺口树根的状态是已证明".to_owned())
        }
        GapStatus::NotAProposition => {
            Err("内部状态错误：根目标不是命题，不能生成复核报告".to_owned())
        }
        GapStatus::OpenPattern => {
            out.push_str(&format!(
                "{number}. 结论「{}」仍依赖未确定的规则参数（缺口）\n   - 前提中有未随结论确定的规则参数，无法继续展开。\n",
                expr_text(&tree.goal)
            ));
            Ok(())
        }
        GapStatus::Cycle => {
            out.push_str(&format!(
                "{number}. 结论「{}」形成循环依赖（缺口）\n   - 同一命题已在当前展开路径上，停止递归。\n",
                expr_text(&tree.goal)
            ));
            Ok(())
        }
    }
}

/// Render one gap tree body recursively.
///
/// The recursion is the reasoner's own tree: its limits (depth 6, 128 nodes per
/// tree, 8 attempts per rule) are already applied when the tree is built, and
/// the report prints every limit marker the tree carries.
fn write_gap_body(
    out: &mut String,
    tree: &GapTree,
    indent: &str,
    pleadings: &BTreeMap<String, RulePleading>,
) {
    match tree.status {
        GapStatus::Unreachable => {}
        GapStatus::Proved => {
            out.push_str(&format!("{indent}- 目标已可推出。\n"));
            return;
        }
        GapStatus::InterpretedOnly => {
            out.push_str(&format!(
                "{indent}- 该命题已由解释推出，但规则前提不消费解释结论，因此作为规则前提仍不算满足。\n"
            ));
            return;
        }
        GapStatus::Conflicted => {
            out.push_str(&format!(
                "{indent}- 该命题处于未决冲突，未决的结论不作为已证明的前提。\n"
            ));
            return;
        }
        GapStatus::Defeated => {
            out.push_str(&format!(
                "{indent}- 该命题在已裁决的冲突中败出，按记录不作为已证明的前提。\n"
            ));
            return;
        }
        GapStatus::NotAProposition => {
            out.push_str(&format!("{indent}- 该目标不是命题。\n"));
            return;
        }
        GapStatus::OpenPattern => {
            out.push_str(&format!(
                "{indent}- 该前提仍依赖未确定的规则参数，无法继续展开。\n"
            ));
            return;
        }
        GapStatus::Cycle => {
            out.push_str(&format!(
                "{indent}- 循环依赖：同一命题已在当前展开路径上，停止递归。\n"
            ));
            return;
        }
    }
    let mut candidates: Vec<&std_deduce_reason::GapRule> = tree.candidates.iter().collect();
    candidates.sort_by(|a, b| a.rule.cmp(&b.rule));
    let mut axiom_candidates: Vec<&std_deduce_reason::AxiomCandidate> =
        tree.axiom_candidates.iter().collect();
    axiom_candidates.sort_by(|a, b| a.axiom.cmp(&b.axiom));
    if candidates.is_empty() && axiom_candidates.is_empty() && tree.limit.is_none() {
        out.push_str(&format!(
            "{indent}- 没有任何规则以这个命题为结论：需要补充规则，或把它作为已知事实登记。\n"
        ));
    }
    for candidate in candidates {
        out.push_str(&format!(
            "{indent}- 候选规则「{}」（适用性：{}）\n",
            escape_control(&candidate.rule),
            candidate.applicability.summary_zh()
        ));
        if matches!(
            candidate.applicability,
            std_deduce_reason::Applicability::Undecidable { .. }
        ) {
            out.push_str(&format!(
                "{indent}  - 提示：需要为该争点显式指定引用时间（尚未实现）。\n"
            ));
        }
        if candidate.missing.is_empty() && candidate.blocked_by.is_empty() {
            if candidate.applicability.is_applicable() {
                out.push_str(&format!("{indent}  - 这里没有记录它缺少什么。\n"));
            } else {
                out.push_str(&format!(
                    "{indent}  - 这条规则没有缺失前提，但因适用性为{}，规则不触发。\n",
                    candidate.applicability.summary_zh()
                ));
            }
        }
        if !candidate.missing.is_empty() {
            out.push_str(&format!(
                "{indent}  - 判定口径：按已持有事实；补上缺失前提后判定可能变化。\n"
            ));
        }
        for premise in &candidate.missing {
            let proposition = expr_text(&premise.premise);
            out.push_str(&format!("{indent}  - 缺：「{proposition}」\n"));
            write_burden_lines(
                out,
                &format!("{indent}    "),
                pleadings
                    .get(candidate.rule.as_ref())
                    .map(|pleading| pleading.requirements),
                "举证责任",
                "证明标准",
            );
            match &premise.gap {
                Some(child) => {
                    out.push_str(&format!("{indent}    - 子缺口：\n"));
                    write_gap_body(out, child, &format!("{indent}      "), pleadings);
                }
                None => match gap_truncation_reason(tree, candidate) {
                    Some(reason) => {
                        out.push_str(&format!(
                            "{indent}    - 子缺口：「{proposition}」未展开（已截断：{reason}）。\n"
                        ));
                    }
                    None => {
                        out.push_str(&format!(
                            "{indent}    - 子缺口：「{proposition}」未展开：候选规则「{}」的适用性为{}，补上该前提也不会让它触发。\n",
                            escape_control(&candidate.rule),
                            candidate.applicability.summary_zh()
                        ));
                    }
                },
            }
        }
        write_burden_lines(
            out,
            &format!("{indent}  "),
            pleadings
                .get(candidate.rule.as_ref())
                .map(|pleading| pleading.exceptions),
            "例外举证",
            "例外证明标准",
        );
        if candidate.blocked_by.is_empty() {
            out.push_str(&format!(
                "{indent}  - 阻断条件：无（没有已成立的例外条件）。\n"
            ));
        } else {
            for blocker in &candidate.blocked_by {
                out.push_str(&format!(
                    "{indent}  - 阻断条件：「{}」已成立。\n",
                    expr_text(blocker)
                ));
            }
        }
        if let Some(limit) = &candidate.limit {
            out.push_str(&format!(
                "{indent}  - 已截断：{}；其余前提不再展开。\n",
                gap_limit_text(limit)
            ));
        }
    }
    if let Some(limit) = &tree.limit {
        out.push_str(&format!(
            "{indent}- 已截断：{}；其余缺口不再展开。\n",
            gap_limit_text(limit)
        ));
    }
    // Universal facts that could instantiate this gap. They are diagnostics
    // from the current environment declaration, not certificate steps; a
    // refused one carries the reasoner's own reason.
    for candidate in axiom_candidates {
        out.push_str(&format!(
            "{indent}- 公理候选「{}」（来自当前环境声明，非证书记录）\n",
            escape_control(candidate.axiom.as_ref())
        ));
        out.push_str(&format!(
            "{indent}  - 绑定：{}\n",
            format_candidate_bindings(&candidate.bindings)
        ));
        match &candidate.problem {
            Some(problem) => {
                out.push_str(&format!(
                    "{indent}  - 未实例化：{}\n",
                    escape_control(problem)
                ));
            }
            None => {
                out.push_str(&format!(
                    "{indent}  - 可由该全称公理实例化；当前推导没有触发它。\n"
                ));
            }
        }
    }
}

/// Why a missing premise was not expanded, read from the candidate's own limit
/// or its parent gap node's limit. `None` means the candidate was listed but
/// deliberately not expanded (inapplicable/undecidable), not truncated.
fn gap_truncation_reason(tree: &GapTree, candidate: &std_deduce_reason::GapRule) -> Option<String> {
    if !candidate.applicability.allows_firing() {
        // The candidate was listed because it cannot fire, not because a limit
        // cut it off. Its own applicability summary is the reason.
        return None;
    }
    if let Some(limit) = &candidate.limit {
        return Some(gap_limit_text(limit));
    }
    tree.limit.as_ref().map(gap_limit_text)
}

/// Two declared burden lines. `None` means the rule's declaration was not
/// available, which is stated rather than defaulted.
fn write_burden_lines(
    out: &mut String,
    indent: &str,
    pleading: Option<std_deduce_kernel::env::ProofBurden>,
    burden_label: &str,
    standard_label: &str,
) {
    match pleading {
        Some(burden) => {
            let (burden_value, standard_value) = burden.labels_zh();
            out.push_str(&format!("{indent}- {burden_label}：{burden_value}\n"));
            out.push_str(&format!("{indent}- {standard_label}：{standard_value}\n"));
        }
        None => {
            out.push_str(&format!(
                "{indent}- {burden_label}：未找到规则声明，无法报告\n"
            ));
            out.push_str(&format!(
                "{indent}- {standard_label}：未找到规则声明，无法报告\n"
            ));
        }
    }
}

/// Section six: every conflict the certificate records.
fn write_conflicts_section(
    out: &mut String,
    certificate: &Certificate,
    conflicts: &[&std_deduce_cert::Conflict],
    questions: &mut BTreeMap<u8, Vec<Question>>,
) {
    begin_section(out, "## 六、未决与冲突");
    out.push_str("未决冲突：两条相反结论，没有任何已记录的优先关系或严格事实能判出胜负。\n");
    if conflicts.is_empty() {
        out.push_str("本案推导没有记录冲突。\n");
    } else {
        for (index, conflict) in conflicts.iter().enumerate() {
            let number = index + 1;
            let left = cert_expr_text(&conflict.left);
            let right = cert_expr_text(&conflict.right);
            match &conflict.resolution {
                Resolution::Unresolved { reason } => {
                    out.push_str(&format!("{number}. 未决冲突：「{left}」与「{right}」\n"));
                    out.push_str(&format!(
                        "   - 左侧：{}\n",
                        provenance_text(certificate, &conflict.left, &conflict.left_by)
                    ));
                    out.push_str(&format!(
                        "   - 右侧：{}\n",
                        provenance_text(certificate, &conflict.right, &conflict.right_by)
                    ));
                    out.push_str(&format!(
                        "   - 裁决：未决；未决原因：{}\n",
                        unresolved_text(certificate, conflict, reason)
                    ));
                    questions
                        .entry(0)
                        .or_default()
                        .push(Question {
                            text: format!(
                                "「{left}」与「{right}」相反，模型无法判定哪一方成立；请确认哪一侧的依据更强。"
                            ),
                            anchor: format!("「未决与冲突」第 {number} 条"),
                        });
                }
                Resolution::Defeated { winner, basis } => {
                    let (win, win_by, lose, lose_by) = match winner {
                        Side::Left => (
                            &conflict.left,
                            &conflict.left_by,
                            &conflict.right,
                            &conflict.right_by,
                        ),
                        Side::Right => (
                            &conflict.right,
                            &conflict.right_by,
                            &conflict.left,
                            &conflict.left_by,
                        ),
                    };
                    out.push_str(&format!("{number}. 已裁决冲突：「{left}」与「{right}」\n"));
                    out.push_str(&format!(
                        "   - 胜方：「{}」（{}）\n",
                        cert_expr_text(win),
                        provenance_text(certificate, win, win_by)
                    ));
                    out.push_str(&format!(
                        "   - 被否决：「{}」（{}）\n",
                        cert_expr_text(lose),
                        provenance_text(certificate, lose, lose_by)
                    ));
                    match basis {
                        ResolutionBasis::Assumption => {
                            let text = if matches!(lose_by, Provenance::Rules { .. }) {
                                "严格事实优先于可废止规则结论。"
                            } else if matches!(lose_by, Provenance::Interpretation { .. }) {
                                "严格事实优先于解释结论。"
                            } else {
                                "严格事实优先于未经证明的主张。"
                            };
                            out.push_str(&format!("   - 依据：{text}\n"));
                        }
                        ResolutionBasis::Priority { edges } => {
                            for edge in edges {
                                out.push_str(&format!("   - 依据：{}\n", priority_edge_text(edge)));
                            }
                        }
                    }
                }
            }
        }
    }

    // Obligations that are not conflicts, gaps, open concepts or case
    // extensions. They are printed rather than silently dropped, because
    // `MissingSource` / `Other` are exactly the records that make the trust
    // label `争点未决`.
    let mut other: Vec<&std_deduce_cert::OpenObligation> = certificate
        .open_obligations
        .iter()
        .filter(|obligation| {
            matches!(
                obligation.kind,
                ObligationKind::MissingSource
                    | ObligationKind::UnresolvedConflict
                    | ObligationKind::Other
            )
        })
        .collect();
    other.sort_by_key(|obligation| {
        (
            obligation_kind_order(obligation.kind),
            obligation.id.clone(),
            obligation.nodes.clone(),
            obligation.description.clone(),
        )
    });
    if !other.is_empty() {
        out.push_str("其他未决事项：\n");
        for obligation in other {
            out.push_str(&format!(
                "- [{}] {}{}\n",
                obligation_kind_label(obligation.kind),
                escape_control(&obligation.description),
                node_suffix(&obligation.nodes)
            ));
        }
    }
}

fn obligation_kind_order(kind: ObligationKind) -> u8 {
    match kind {
        ObligationKind::MissingSource => 0,
        ObligationKind::UnresolvedConflict => 1,
        ObligationKind::Other => 2,
        _ => 3,
    }
}

fn obligation_kind_label(kind: ObligationKind) -> &'static str {
    match kind {
        ObligationKind::MissingPremise => "缺少前提",
        ObligationKind::MissingSource => "缺少来源",
        ObligationKind::OpenConcept => "开放概念",
        ObligationKind::UnresolvedConflict => "冲突未决",
        ObligationKind::NeedsHumanDetermination => "需人判断",
        ObligationKind::Other => "其他",
    }
}

/// Section seven: every item a human must decide.
fn write_open_concepts_section(
    out: &mut String,
    env: &Env,
    certificate: &Certificate,
    dependency: Option<&OpenConceptDependency>,
    questions: &mut BTreeMap<u8, Vec<Question>>,
) -> Result<(), String> {
    begin_section(out, "## 七、需人判断");
    out.push_str(
        "需人判断：模型不能替代人对法律概念、未经官方法律包审核的案件规则或逻辑未决事项作出判断。\n",
    );
    let mut number = 0usize;
    let mut wrote_any = false;

    if let Some(dependency) = dependency {
        for concept in &dependency.concepts {
            number += 1;
            wrote_any = true;
            let concept_text = escape_control(concept);
            out.push_str(&format!(
                "{number}. 开放概念「{concept_text}」：需要人来解释的法律用语；模型把它当作普通谓词使用。\n"
            ));
            let nodes = concept_nodes(env, certificate, dependency, concept)?;
            if nodes.is_empty() {
                out.push_str("   - 所在推导步骤：没有定位到具体节点。\n");
            } else {
                out.push_str("   - 所在推导步骤：\n");
                for node in &nodes {
                    out.push_str(&format!(
                        "     - {}\n",
                        node_description(certificate, *node)?
                    ));
                }
            }
            out.push_str(
                "   - 为什么不能自动判定：概念的含义、判断标准以及本案是否满足，必须由律师或法院解释；\
                 这里只记录模型在推导中把它当成了已成立的命题。\n",
            );
            questions
                .entry(1)
                .or_default()
                .push(Question {
                    text: format!(
                        "开放概念「{concept_text}」不能由模型自动判定；请确认它在本案中的含义与判断标准。"
                    ),
                    anchor: format!("「需人判断」第 {number} 条"),
                });
        }
    }

    // Every open-concept obligation counts even if the dependency is absent:
    // the certificate checker rejects such a certificate, but the report still
    // never invents a concept name it does not have.
    let mut open_obligations: Vec<&std_deduce_cert::OpenObligation> = certificate
        .open_obligations
        .iter()
        .filter(|obligation| obligation.kind == ObligationKind::OpenConcept)
        .collect();
    open_obligations.sort_by_key(|obligation| (obligation.id.clone(), obligation.nodes.clone()));
    for obligation in open_obligations {
        if dependency.is_some_and(|dependency| {
            obligation
                .nodes
                .iter()
                .any(|node| dependency.nodes.contains(node))
        }) {
            continue;
        }
        number += 1;
        wrote_any = true;
        out.push_str(&format!(
            "{number}. 开放概念事项：{}{}\n",
            escape_control(&obligation.description),
            node_suffix(&obligation.nodes)
        ));
        questions.entry(1).or_default().push(Question {
            text: format!(
                "有一项开放概念需要解释：{}。请确认相关概念的判断标准。",
                escape_control(&obligation.description)
            ),
            anchor: format!("「需人判断」第 {number} 条"),
        });
    }

    let mut human_obligations: Vec<&std_deduce_cert::OpenObligation> = certificate
        .open_obligations
        .iter()
        .filter(|obligation| {
            obligation.kind == ObligationKind::NeedsHumanDetermination
                && obligation.id != LOCAL_EXTENSION_OBLIGATION_ID
        })
        .collect();
    human_obligations.sort_by_key(|obligation| (obligation.id.clone(), obligation.nodes.clone()));
    for obligation in human_obligations {
        number += 1;
        wrote_any = true;
        out.push_str(&format!(
            "{number}. 需人判断事项：{}{}\n",
            escape_control(&obligation.description),
            node_suffix(&obligation.nodes)
        ));
        out.push_str("   - 为什么不能自动判定：这条事项需要人来决定，模型不替人给出判断。\n");
        questions.entry(2).or_default().push(Question {
            text: format!(
                "需人判断事项：{}。请确认应当如何处理。",
                escape_control(&obligation.description)
            ),
            anchor: format!("「需人判断」第 {number} 条"),
        });
    }

    let mut extensions: Vec<&std_deduce_cert::OpenObligation> = certificate
        .open_obligations
        .iter()
        .filter(|obligation| {
            obligation.kind == ObligationKind::NeedsHumanDetermination
                && obligation.id == LOCAL_EXTENSION_OBLIGATION_ID
        })
        .collect();
    extensions.sort_by_key(|obligation| (obligation.id.clone(), obligation.nodes.clone()));
    for obligation in extensions {
        number += 1;
        wrote_any = true;
        out.push_str(&format!(
            "{number}. 案件扩展：{}{}\n",
            escape_control(&obligation.description),
            node_suffix(&obligation.nodes)
        ));
        out.push_str(
            "   - 为什么不能自动判定：这些规则由案件文件声明，未经官方法律包审核；\
             它们不是已审核的法律依据。\n",
        );
        questions.entry(3).or_default().push(Question {
            text: format!(
                "案件本地规则需要律师判断：{}。请确认这些规则能否作为本案的法律依据。",
                escape_control(&obligation.description)
            ),
            anchor: format!("「需人判断」第 {number} 条"),
        });
    }

    if !wrote_any {
        out.push_str("本案推导没有记录开放概念、需人判断事项或案件扩展。\n");
    }
    Ok(())
}

/// Section eight: every question derived from an entry above.
fn write_questions_section(out: &mut String, questions: &[Question]) {
    begin_section(out, "## 八、建议向律师确认的问题");
    out.push_str(
        "以下问题只从上文条目派生，每条末尾用「〔见…〕」指向报告中的对应条目；\
         报告不凭空编造问题，也不把答案当成法律意见。\n",
    );
    if questions.is_empty() {
        out.push_str("没有可由上述条目派生的确认问题。这不表示法律上正确。\n");
        return;
    }
    for (index, question) in questions.iter().enumerate() {
        out.push_str(&format!(
            "{}. {}〔见{}〕\n",
            index + 1,
            question.text,
            question.anchor
        ));
    }
}

struct Question {
    text: String,
    anchor: String,
}

/// Whether the root's issue is the same proposition as the root, using kernel
/// definitional equality rather than printed text.
fn same_proposition(env: &Env, left: &Expr, right: &Expr) -> Result<bool, String> {
    convertible(env, &Ctx::new(), left, right)
        .map_err(|error| format!("无法按内核等价比较两个命题：{error}"))
}

fn concept_nodes(
    env: &Env,
    certificate: &Certificate,
    dependency: &OpenConceptDependency,
    concept: &Name,
) -> Result<Vec<NodeId>, String> {
    let mut nodes = Vec::new();
    for node_id in &dependency.nodes {
        let proposition = node_proposition(certificate, *node_id)?;
        let normalized = normalize(env, &Ctx::new(), &Expr::from(proposition))
            .map_err(|error| format!("无法规范化节点 {node_id} 的命题以判定开放概念：{error}"))?;
        if normalized
            .head_const()
            .is_some_and(|head| head.as_ref() == concept.as_ref())
        {
            nodes.push(*node_id);
        }
    }
    Ok(nodes)
}

fn node_description(certificate: &Certificate, node_id: NodeId) -> Result<String, String> {
    let Some(entry) = certificate.nodes.get(node_id) else {
        return Err(format!(
            "节点 {node_id}：节点索引越界：证书只有 {} 个节点",
            certificate.nodes.len()
        ));
    };
    Ok(match entry {
        Node::Assumption { .. } => {
            let proposition = node_proposition(certificate, node_id)?;
            format!(
                "推导步骤 {node_id}（结论命题「{}」，作为事实断言）",
                cert_expr_text(proposition)
            )
        }
        Node::RuleApplication {
            rule, conclusion, ..
        } => format!(
            "推导步骤 {node_id}（规则「{}」的结论「{}」）",
            escape_control(rule),
            cert_expr_text(conclusion)
        ),
        Node::InterpretationApplication {
            interpretation,
            conclusion,
            ..
        } => {
            let entry = certificate
                .interpretations
                .get(*interpretation)
                .ok_or_else(|| {
                    format!(
                        "节点 {node_id}：引用了不存在的解释 {interpretation}：证书只有 {} 条解释",
                        certificate.interpretations.len()
                    )
                })?;
            format!(
                "推导步骤 {node_id}（解释「{}」的结论「{}」）",
                escape_control(&entry.id),
                cert_expr_text(conclusion)
            )
        }
        Node::AxiomInstance {
            axiom,
            identity,
            bindings,
            conclusion,
            ..
        } => format!(
            "推导步骤 {node_id}（全称公理「{}」〔{}〕的实例「{}」，绑定 {}）",
            escape_control(axiom),
            identity_text(*identity).0,
            cert_expr_text(conclusion),
            cert_bindings_text(bindings)
        ),
        Node::Gap { proposition, .. } => format!(
            "推导步骤 {node_id}（缺口命题「{}」）",
            cert_expr_text(proposition)
        ),
    })
}

fn node_proposition(
    certificate: &Certificate,
    node: NodeId,
) -> Result<&std_deduce_cert::CertExpr, String> {
    let Some(entry) = certificate.nodes.get(node) else {
        return Err(format!(
            "节点 {node}：节点索引越界：证书只有 {} 个节点",
            certificate.nodes.len()
        ));
    };
    match entry {
        Node::Assumption { assumption } => certificate
            .assumptions
            .get(*assumption)
            .map(|entry| &entry.proposition)
            .ok_or_else(|| {
                format!(
                    "节点 {node}：引用了不存在的假设 {assumption}：证书只有 {} 条假设",
                    certificate.assumptions.len()
                )
            }),
        Node::RuleApplication { conclusion, .. } => Ok(conclusion),
        Node::InterpretationApplication { conclusion, .. } => Ok(conclusion),
        Node::AxiomInstance { conclusion, .. } => Ok(conclusion),
        Node::Gap { proposition, .. } => Ok(proposition),
    }
}

fn node_proposition_text(certificate: &Certificate, node: NodeId) -> Result<String, String> {
    node_proposition(certificate, node).map(cert_expr_text)
}

fn cert_expr_text(expression: &std_deduce_cert::CertExpr) -> String {
    // `print_expr` already escapes constant and binder names through the kernel
    // helper (`pretty::print_expr`), so the printed form is a single-line
    // escaped rendering. Escaping it again would double a literal backslash and
    // disagree with `:why` / `:explain`.
    print_expr(&Expr::from(expression))
}

fn expr_text(expression: &Expr) -> String {
    print_expr(expression)
}

fn identity_text(identity: FactIdentity) -> (&'static str, &'static str) {
    match identity {
        FactIdentity::Verified => ("法院查明", "严格事实"),
        FactIdentity::Stipulated => ("双方无争议", "严格事实"),
        FactIdentity::UserAsserted => ("用户陈述", "主张，不是证明"),
        FactIdentity::Assumed => ("分析假设", "主张，不是证明"),
        FactIdentity::Disputed => ("对方争议", "只记录对方的主张，不参与推导"),
    }
}

fn provenance_text(
    certificate: &Certificate,
    proposition: &std_deduce_cert::CertExpr,
    provenance: &Provenance,
) -> String {
    match provenance {
        Provenance::Assumption => match assumption_for(certificate, proposition) {
            Some(entry) => {
                let identity = identity_text(entry.identity).0;
                match &entry.label {
                    Some(label) => format!("事实〔{identity}〕，标签：{}", escape_control(label)),
                    None => format!("事实〔{identity}〕"),
                }
            }
            None => "记为事实，但没有可识别的身份记录".to_owned(),
        },
        Provenance::Rules { rules } if rules.is_empty() => {
            "由规则推出，但没有记录具体规则".to_owned()
        }
        Provenance::Rules { rules } => format!(
            "由规则{}推出",
            rules
                .iter()
                .map(|rule| format!("「{}」", escape_control(rule)))
                .collect::<Vec<_>>()
                .join("、")
        ),
        Provenance::Interpretation { interpretation } => {
            match certificate.interpretations.get(*interpretation) {
                Some(entry) => format!(
                    "由解释「{}」（方向 {}）推出",
                    escape_control(&entry.id),
                    entry.direction.keyword()
                ),
                None => "由解释推出，但没有记录可识别的解释".to_owned(),
            }
        }
        Provenance::Axiom { axiom } => format!(
            "由全称公理「{}」实例化推出（公理实例是推导，不是假设）",
            escape_control(axiom)
        ),
    }
}

fn unresolved_text(
    certificate: &Certificate,
    conflict: &std_deduce_cert::Conflict,
    reason: &UnresolvedReason,
) -> String {
    match reason {
        UnresolvedReason::ConflictingAssumptions => {
            match (
                assumption_for(certificate, &conflict.left),
                assumption_for(certificate, &conflict.right),
            ) {
                (Some(left), Some(right))
                    if is_strict(left.identity) && is_strict(right.identity) =>
                {
                    "两侧都是严格事实，事实之间没有先后。".to_owned()
                }
                (Some(left), Some(right))
                    if !is_strict(left.identity) && !is_strict(right.identity) =>
                {
                    "两侧都只是主张，未经证明，不能判出一方胜出。".to_owned()
                }
                _ => "两侧都是事实，但没有记录可判定的身份先后。".to_owned(),
            }
        }
        UnresolvedReason::NonStrictFact { identity } => {
            let (fact_side, other_is_interpretation) = match (&conflict.left_by, &conflict.right_by)
            {
                (Provenance::Assumption, other) => (
                    Some(&conflict.left),
                    matches!(other, Provenance::Interpretation { .. }),
                ),
                (other, Provenance::Assumption) => (
                    Some(&conflict.right),
                    matches!(other, Provenance::Interpretation { .. }),
                ),
                _ => (None, false),
            };
            let conclusion = if other_is_interpretation {
                "解释结论"
            } else {
                "规则结论"
            };
            let identity = identity_text(*identity).0;
            match fact_side {
                Some(proposition) => format!(
                    "「{}」只是「{identity}」，未经证明，不能自动胜过{conclusion}。",
                    cert_expr_text(proposition)
                ),
                None => format!("一侧只是「{identity}」，未经证明，不能自动胜过{conclusion}。"),
            }
        }
        UnresolvedReason::UnknownWitnesses => {
            "一侧由规则推出，但没有记录可重建的规则实例，无法核对优先级。".to_owned()
        }
        UnresolvedReason::NoPriority => {
            let interpretation = matches!(conflict.left_by, Provenance::Interpretation { .. })
                || matches!(conflict.right_by, Provenance::Interpretation { .. });
            if interpretation {
                "解释结论与另一方之间没有可用的优先声明，不能判定谁胜出。".to_owned()
            } else {
                "两侧规则之间没有声明优先级，不能判定谁胜出。".to_owned()
            }
        }
        UnresolvedReason::PriorityUnusable { declared } => {
            let mut text =
                "声明的优先级不足以裁决（覆盖不全、双向覆盖或位于优先级环内）。".to_owned();
            if !declared.is_empty() {
                text.push_str("已声明：");
                text.push_str(
                    &declared
                        .iter()
                        .map(priority_edge_text)
                        .collect::<Vec<_>>()
                        .join("；"),
                );
                text.push('。');
            }
            text
        }
    }
}

fn priority_edge_text(edge: &PriorityEdge) -> String {
    match &edge.origin {
        PriorityOrigin::PriorityDeclaration {
            declared_in,
            sources,
        } => format!(
            "{} 声明的 priority {} over {}（出处：{}）",
            escape_control(declared_in),
            escape_control(&edge.winner),
            escape_control(&edge.loser),
            citations(sources)
        ),
        PriorityOrigin::RuleClause {
            declaring_rule,
            clause,
            rule_sources,
        } => format!(
            "规则 {} 的 {} 子句（出处：{}）",
            escape_control(declaring_rule),
            match clause {
                PriorityClause::Prefer => "prefer",
                PriorityClause::DefeatedBy => "defeated_by",
            },
            citations(rule_sources)
        ),
    }
}

fn citations(sources: &[Source]) -> String {
    if sources.is_empty() {
        return "证书未记录来源".to_owned();
    }
    sources
        .iter()
        .map(Source::one_line)
        .collect::<Vec<_>>()
        .join("、")
}

fn assumption_for<'a>(
    certificate: &'a Certificate,
    proposition: &std_deduce_cert::CertExpr,
) -> Option<&'a std_deduce_cert::Assumption> {
    certificate
        .assumptions
        .iter()
        .find(|entry| &entry.proposition == proposition)
}

fn is_strict(identity: FactIdentity) -> bool {
    matches!(identity, FactIdentity::Verified | FactIdentity::Stipulated)
}

/// One source line with the fields the report promises: text, locator, version,
/// jurisdiction and quotation, plus the optional fields when recorded. A
/// missing field is written `未记录`; no value is inferred.
fn format_source_line(label: &str, indent: &str, sources: &[Source], empty: &str) -> String {
    if sources.is_empty() {
        return format!("{indent}- {label}：{empty}\n");
    }
    let mut out = format!("{indent}- {label}：\n");
    for source in sources {
        out.push_str(&format!("{indent}  - {}\n", source_fields(source)));
    }
    out
}

fn source_fields(source: &Source) -> String {
    let mut parts = vec![
        format!("文本：{}", field_zh(&source.text)),
        format!("条号：{}", field_zh(&source.locator)),
        format!("版本：{}", field_zh(&source.version)),
        format!("管辖：{}", field_zh(&source.jurisdiction)),
        format!("引文：{}", quote_zh(&source.quote)),
    ];
    if let Some(effective) = source
        .effective
        .as_deref()
        .filter(|value| !value.is_empty())
    {
        parts.push(format!("生效：{}", escape_control(effective)));
    }
    if !source.note.is_empty() {
        parts.push(format!("说明：{}", escape_control(&source.note)));
    }
    if !source.url.is_empty() {
        parts.push(format!("链接：{}", escape_control(&source.url)));
    }
    parts.join("；")
}

fn field_zh(value: &str) -> String {
    if value.is_empty() {
        "未记录".to_owned()
    } else {
        format!("「{}」", escape_control(value))
    }
}

/// A quotation, shortened only when it is longer than the summary limit. The
/// full text stays in the certificate; the report labels the short form so it
/// is not presented as the complete quotation.
fn quote_zh(quote: &str) -> String {
    if quote.is_empty() {
        return "未记录".to_owned();
    }
    let total = quote.chars().count();
    if total <= 60 {
        return format!("「{}」", escape_control(quote));
    }
    let summary: String = quote.chars().take(60).collect();
    format!(
        "（前 60 字，共 {total} 字）「{}…」",
        escape_control(&summary)
    )
}

fn node_suffix(nodes: &[NodeId]) -> String {
    if nodes.is_empty() {
        String::new()
    } else {
        format!("（相关推导步骤：{}）", node_list_text(nodes))
    }
}

fn node_list_text(nodes: &[NodeId]) -> String {
    if nodes.is_empty() {
        return "未记录".to_owned();
    }
    nodes
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("、")
}

fn candidate_names(candidates: &[std_deduce_reason::GapRule]) -> String {
    if candidates.is_empty() {
        return "（没有候选规则）".to_owned();
    }
    candidates
        .iter()
        .map(|candidate| format!("「{}」", escape_control(&candidate.rule)))
        .collect::<Vec<_>>()
        .join("、")
}

/// Collect every held premise in a gap tree, including nested candidates.
///
/// The reasoner keeps each candidate's held premises at every tree level, so a
/// fact consumed by a nested candidate is attributed to the conclusion's gap
/// rather than called an unrelated branch.
fn collect_tree_held(tree: &GapTree, out: &mut BTreeSet<String>) {
    for candidate in &tree.candidates {
        for held in &candidate.held {
            out.insert(expression_key(held));
        }
        for premise in &candidate.missing {
            if let Some(child) = &premise.gap {
                collect_tree_held(child, out);
            }
        }
    }
}

fn format_limited_names(names: &[Name]) -> String {
    let shown = names
        .iter()
        .take(8)
        .map(|name| format!("⟨{}⟩", escape_control(name)))
        .collect::<Vec<_>>()
        .join("、");
    if names.len() > 8 {
        format!("{shown} 等 {} 条", names.len())
    } else {
        shown
    }
}

fn gap_limit_text(limit: &GapLimit) -> String {
    match limit {
        GapLimit::Depth { limit } => format!("达到最大展开深度（{limit} 层）"),
        GapLimit::Nodes { limit } => format!("达到最大节点数（{limit} 个）"),
        GapLimit::RuleAttempts { rule, limit } => {
            format!(
                "规则 ⟨{}⟩ 的尝试次数已达上限（{limit} 次）",
                escape_control(rule)
            )
        }
        GapLimit::Issues { limit } => format!("可争的结论已达到上限（{limit} 条）"),
        GapLimit::Excluded { limit } => format!("被排除的规则已达到上限（{limit} 条）"),
    }
}

fn begin_section(out: &mut String, title: &str) {
    if !out.is_empty() {
        out.push('\n');
    }
    out.push_str(title);
    out.push('\n');
    out.push('\n');
}

/// The certificate's rule applicability rendered from its own record: the
/// verdict, the reference dates and places, the rule's declared scope with its
/// origin, and the reason when the verdict is not a positive one.
fn cert_applicability_text(record: &std_deduce_cert::RuleApplicability) -> String {
    let verdict = match record.verdict {
        std_deduce_cert::ApplicabilityVerdict::Applicable => "适用",
        std_deduce_cert::ApplicabilityVerdict::Inapplicable => "不适用",
        std_deduce_cert::ApplicabilityVerdict::Unchecked => "适用性未判定",
        std_deduce_cert::ApplicabilityVerdict::Undecidable => "适用性无法判定",
    };
    let mut details = Vec::new();
    if !record.basis.dates.is_empty() {
        let dates = record
            .basis
            .dates
            .iter()
            .map(|dated| {
                let coverage = if dated.covered {
                    "区间内"
                } else {
                    "区间外"
                };
                if dated.query_date_fallback {
                    format!(
                        "以查询基准日 {} 代替行为时（{coverage}）",
                        escape_control(&dated.date)
                    )
                } else {
                    format!("事件时间 {}（{coverage}）", escape_control(&dated.date))
                }
            })
            .collect::<Vec<_>>()
            .join("、");
        details.push(dates);
    }
    if !record.basis.places.is_empty() {
        let places = record
            .basis
            .places
            .iter()
            .map(|place| {
                let coverage = match place.covered {
                    Some(true) => "覆盖",
                    Some(false) => "不覆盖",
                    None => "层级未声明",
                };
                format!("{}（{coverage}）", escape_control(&place.place))
            })
            .collect::<Vec<_>>()
            .join("、");
        details.push(format!("事件地点 {places}"));
    }
    if record.basis.missing_event_date {
        details.push("部分前提事实没有记录发生时间".to_owned());
    }
    if record.basis.missing_event_place {
        details.push("部分前提事实没有记录发生地点".to_owned());
    }
    let scope = &record.basis.scope;
    let from = scope
        .effective_from
        .as_ref()
        .map(|value| escape_control(value));
    let to = scope
        .effective_to
        .as_ref()
        .map(|value| escape_control(value));
    if from.is_some() || to.is_some() {
        let range = match (&from, &to) {
            (Some(from), Some(to)) => format!("{from}..{to}"),
            (Some(from), None) => format!("{from}..未注明"),
            (None, Some(to)) => format!("未注明..{to}"),
            (None, None) => "未声明".to_owned(),
        };
        let from_origin = origin_label(scope.effective_from_origin.as_ref());
        let to_origin = origin_label(scope.effective_to_origin.as_ref());
        details.push(format!(
            "生效范围 {range}（开始：{from_origin}；结束：{to_origin}）"
        ));
    }
    if let Some(jurisdiction) = scope.jurisdiction.as_ref() {
        details.push(format!(
            "管辖 {}（{}）",
            escape_control(jurisdiction),
            origin_label(scope.jurisdiction_origin.as_ref())
        ));
    }
    if let Some(territory) = scope.territory.as_ref() {
        details.push(format!(
            "地域 {}（{}）",
            escape_control(territory),
            origin_label(scope.territory_origin.as_ref())
        ));
    }
    if let Some(as_of) = record.basis.session.as_of.as_ref() {
        details.push(format!("会话兜底日 {}", escape_control(as_of)));
    }
    if let Some(jurisdiction) = record.basis.session.jurisdiction.as_ref() {
        details.push(format!("会话管辖 {}", escape_control(jurisdiction)));
    }
    if let Some(reason) = record.reason() {
        // The checker recomputes this text and compares it byte for byte, so a
        // validated certificate cannot carry an unescaped reason here.
        details.push(reason.text.clone());
    }
    if details.is_empty() {
        verdict.to_owned()
    } else {
        format!("{verdict}（{}）", details.join("；"))
    }
}

fn origin_label(origin: Option<&std_deduce_cert::ScopeOriginRecord>) -> &'static str {
    match origin {
        Some(origin) => origin.label_zh(),
        None => "未记录",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source(text: &str) -> Source {
        Source {
            text: text.to_owned(),
            locator: "第五条".to_owned(),
            version: "2024".to_owned(),
            effective: None,
            note: String::new(),
            quote: String::new(),
            url: String::new(),
            jurisdiction: String::new(),
            retrieved_at: String::new(),
            hash: String::new(),
        }
    }

    fn render(record: RuleRecord) -> String {
        let mut rules = BTreeMap::new();
        rules.insert("处罚".to_owned(), record);
        let mut questions = BTreeMap::new();
        let mut out = String::new();
        write_rules_section(
            &mut out,
            &rules,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &mut questions,
        );
        out
    }

    #[test]
    fn an_applied_rule_without_a_recorded_source_never_uses_the_environment_source() {
        let mut record = RuleRecord::new();
        record.root_nodes.push(0);
        record.in_gap = true;
        record.push_env_source(&source("示例法"));
        let out = render(record);
        let certificate_line = out
            .lines()
            .find(|line| line.contains("证书出处"))
            .unwrap_or_else(|| panic!("no certificate source line:\n{out}"));
        assert!(
            certificate_line.contains("证书未记录来源"),
            "an applied rule with no certificate source must say so: {certificate_line}"
        );
        assert!(
            !certificate_line.contains("示例法"),
            "the environment source must not be substituted for the certificate source: {certificate_line}"
        );
        assert!(
            out.contains("非证书记录") && out.contains("示例法"),
            "the gap candidate's environment source must be displayed separately:\n{out}"
        );
    }

    #[test]
    fn an_applied_rule_without_a_gap_still_says_the_source_is_not_recorded() {
        let mut record = RuleRecord::new();
        record.root_nodes.push(0);
        let out = render(record);
        assert!(out.contains("证书未记录来源"), "{out}");
        assert!(!out.contains("非证书记录"), "{out}");
    }
}
