//! The lawyer review report renderer (`:review`).
//!
//! This module turns data the session already has into a Markdown report a
//! practising lawyer can read. It is a **derived view**, not a new inference
//! and not legal advice. Every sentence is read from one of four inputs:
//!
//! * the certificate v7 the query path produced (`:why` / `:cert` build the
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
    PriorityClause, PriorityEdge, PriorityOrigin, Provenance, Resolution, ResolutionBasis, Side,
    Source, TrustLabel, TrustReport, UnresolvedReason, LOCAL_EXTENSION_OBLIGATION_ID,
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
    /// Sources the certificate records for this rule's applications.
    cert_sources: Vec<Source>,
    /// Applicability texts of the certificate's rule applications.
    cert_verdicts: BTreeSet<String>,
    /// Sources the gap trees record for this rule's candidates.
    gap_sources: Vec<Source>,
    /// Applicability texts of the gap-tree candidates.
    gap_verdicts: BTreeSet<String>,
    /// Whether the rule appears on the root's proof graph.
    in_root: bool,
    /// Whether the rule appears as a candidate in a gap tree.
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
            gap_sources: Vec::new(),
            gap_verdicts: BTreeSet::new(),
            in_root: false,
            in_gap: false,
            needs_applicability_review: None,
        }
    }

    fn push_cert_source(&mut self, source: &Source) {
        if !self.cert_sources.contains(source) {
            self.cert_sources.push(source.clone());
        }
    }

    fn push_gap_source(&mut self, source: &Source) {
        if !self.gap_sources.contains(source) {
            self.gap_sources.push(source.clone());
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
    let mut out = String::new();
    write_header(&mut out);

    // The root's proposition, or an explicit statement that there is none.
    let root_proposition = match certificate.root {
        Some(root) => node_proposition_text(certificate, root)?,
        None => "证书没有根节点".to_owned(),
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

    write_conclusion_section(&mut out, certificate, trust, &root_proposition);

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
    write_rules_section(&mut out, &rules, &mut question_groups);
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
        certificate,
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
         它只陈述 std-deduce 在当前理论内记录的推导、缺口、冲突与信任标签；\
         信任标签只表示模型内的确定性（例如「已验证」只表示证书在严格事实下证明了根、\
         根可达图里没有与根相关的未决事项），不表示法律上正确，也不能代替律师对事实、\
         法律解释与计算结果的判断。\n\n",
    );
    out.push_str("- 报告来源：证书（格式 v7）、缺口树、规则举证元数据、信任标签（派生视图）。\n");
    out.push_str(
        "- 隐私边界：命题与来源文本中的人名、地名等原样保留，本报告未做脱敏（脱敏尚未实现）。\n",
    );
}

/// The first section: conclusion, root reachability, and all five labels.
fn write_conclusion_section(
    out: &mut String,
    certificate: &Certificate,
    trust: &TrustReport,
    root_proposition: &str,
) {
    begin_section(out, "## 一、结论与信任标签");
    out.push_str(&format!("**结论命题：**「{root_proposition}」\n"));
    let root_state = match certificate.root {
        None => "否（证书没有根节点）".to_owned(),
        Some(root) if matches!(certificate.nodes.get(root), Some(Node::Gap { .. })) => {
            "否（根是缺口，结论未获证明）".to_owned()
        }
        Some(root) if trust.root_proved() => format!("是（根节点 {root} 已证明）"),
        Some(_) => "否（根的可达推导里仍有缺口）".to_owned(),
    };
    out.push_str(&format!("**根是否可达：**{root_state}\n"));
    out.push_str(&format!("**{}**\n", trust.summary()));
    out.push_str("信任标签（模型内确定性，不表示法律上正确）：\n");
    for label in ALL_LABELS {
        let name = label.name_zh();
        if trust.contains(label) {
            let evidence = trust.evidence(label).join("；");
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
}

fn absent_label_reason(label: TrustLabel) -> &'static str {
    match label {
        TrustLabel::NeedsLawyerJudgment => {
            "证书记录里没有与根相关的开放概念、需人判断义务或案件扩展"
        }
        TrustLabel::DisputeUnresolved => {
            "证书没有与根相关的未决冲突，也没有与根相关的缺少来源或其他未解决事项"
        }
        TrustLabel::FactNeedsEvidence => "根已证明，且没有与根相关的缺少前提义务",
        TrustLabel::DependsOnAssumption => {
            "根未证明，或根推导没有使用用户陈述、分析假设、对方争议或解释"
        }
        TrustLabel::Verified => "根未证明，或根推导使用了主张，或仍有与根相关的未决事项",
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
    out.push_str("争点：当前事实集下尚未证明、仍可被主张的结论（来自 :issues 扫描）。\n");
    if issues_sorted.is_empty() {
        out.push_str("当前事实集下没有可争的结论（:issues 扫描为空）。\n");
    } else {
        out.push_str(&format!(
            "当前事实集下可争的结论 {} 条（按结构键排序）：\n",
            issues_sorted.len()
        ));
        for (index, tree) in issues_sorted.iter().enumerate() {
            write_issue_item(out, index + 1, tree, root_expr, env, questions)?;
        }
    }
    for limit in &issues.limits {
        out.push_str(&format!(
            "- 扫描上限：{}；其余未列出。\n",
            gap_limit_text(limit)
        ));
    }
    if !issues.uninstantiable.is_empty() {
        out.push_str(&format!(
            "- 另有 {} 条规则无法在当前事实集上实例化（参数类型没有已声明的常量，或结论依赖前提证明）：{}\n",
            issues.uninstantiable.len(),
            format_limited_names(&issues.uninstantiable)
        ));
    }
    if !issues.excluded.is_empty() {
        out.push_str(&format!(
            "- 另有 {} 条规则因所有可枚举实例都被时空适用性排除而未扫描：{}\n",
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
                    "{number}. 「{goal}」：与根结论是同一命题；缺口见「缺口与举证」第 1 条。\n"
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
        record.in_root = true;
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
    // A gap candidate in the certificate also records its rule's sources and
    // applicability. Those records are certificate data even though the
    // recursive tree is not: collect them so the rule section does not report
    // "the certificate records no source" for a candidate the certificate does
    // carry.
    for node in &certificate.nodes {
        let Node::Gap { candidates, .. } = node else {
            continue;
        };
        for candidate in candidates {
            let record = rules
                .entry(candidate.rule.clone())
                .or_insert_with(RuleRecord::new);
            for source in &candidate.sources {
                record.push_cert_source(source);
            }
            let verdict = cert_applicability_text(&candidate.applicability);
            record.cert_verdicts.insert(verdict.clone());
            note_applicability_question(record, candidate.applicability.verdict, &verdict);
        }
    }
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
            record.push_gap_source(&Source::from(source));
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
    questions: &mut BTreeMap<u8, Vec<Question>>,
) {
    begin_section(out, "## 三、规则与出处");
    out.push_str(
        "规则与出处只列根推导使用的规则和本报告缺口树里的候选规则；\
         证书固定点其他分支里的规则不列入。\n",
    );
    if rules.is_empty() {
        out.push_str("证书记录里没有用到任何规则。\n");
        return;
    }
    for (index, (name, record)) in rules.iter().enumerate() {
        let number = index + 1;
        out.push_str(&format!("{number}. 规则「{}」\n", escape_control(name)));
        if record.root_nodes.is_empty() {
            out.push_str("   - 根推导使用：否（只作为缺口候选规则）\n");
        } else {
            out.push_str(&format!(
                "   - 根推导使用：是（节点 {}）\n",
                record
                    .root_nodes
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("、")
            ));
        }
        out.push_str(&format_source_line(
            "证书出处",
            "   ",
            &record.cert_sources,
            "证书未记录来源",
        ));
        if record.in_gap {
            let extra: Vec<Source> = record
                .gap_sources
                .iter()
                .filter(|source| !record.cert_sources.contains(source))
                .cloned()
                .collect();
            if extra.is_empty() {
                if record.gap_sources.is_empty() {
                    out.push_str("   - 缺口树补充出处：无（缺口树没有记录额外来源）\n");
                } else {
                    out.push_str("   - 缺口树补充出处：无（证书已经记录了同一份来源）\n");
                }
            } else {
                out.push_str(&format_source_line(
                    "缺口树补充出处",
                    "   ",
                    &extra,
                    "缺口树未记录来源",
                ));
            }
        }
        if record.cert_verdicts.is_empty() && record.gap_verdicts.is_empty() {
            out.push_str("   - 适用性：证书与缺口树都没有记录判定。\n");
        } else {
            for verdict in &record.cert_verdicts {
                out.push_str(&format!("   - 适用性（证书记录）：{}\n", verdict));
            }
            let mut extra_gap_verdicts = 0usize;
            for verdict in &record.gap_verdicts {
                if record.cert_verdicts.contains(verdict) {
                    continue;
                }
                extra_gap_verdicts += 1;
                out.push_str(&format!("   - 适用性（缺口树记录）：{}\n", verdict));
            }
            if record.in_gap && !record.gap_verdicts.is_empty() && extra_gap_verdicts == 0 {
                out.push_str("   - 缺口树判定与证书记录相同。\n");
            }
        }
        if record.cert_sources.is_empty() && record.gap_sources.is_empty() {
            questions
                .entry(7)
                .or_default()
                .push(Question {
                    text: format!(
                        "规则「{}」的出处没有被证书或缺口树记录；请补充可核对的来源（文本、条号、版本、管辖、引文）。",
                        escape_control(name)
                    ),
                    anchor: format!("「规则与出处」第 {number} 条"),
                });
        }
        if let Some(verdict) = &record.needs_applicability_review {
            questions.entry(6).or_default().push(Question {
                text: format!(
                    "规则「{}」的时空适用性为{}；请确认该规则是否适用于本案的事件时间与地点。",
                    escape_control(name),
                    verdict
                ),
                anchor: format!("「规则与出处」第 {number} 条"),
            });
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
        out.push_str("证书没有记录任何假设事实。\n");
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
        if root_gap.is_some() {
            collect_certificate_held(certificate, &mut root_held);
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
                "根推导使用".to_owned()
            } else if root_held.contains(&expression_key(&Expr::from(&entry.proposition))) {
                "根缺口候选的已持有前提（缺口未闭合，不能当作证明）".to_owned()
            } else {
                "未进入根推导（证书固定点的其他分支）".to_owned()
            };
            out.push_str(&format!(
                "- 「{proposition}」：身份：{identity}（{strictness}）；与根的关系：{relation}\n"
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
        out.push_str("- 无。根已完成证明，当前事实集下也没有可争结论。\n");
    } else {
        if let Some(tree) = root_gap {
            out.push_str(&format!(
                "- 「{}」〔缺口〕：根结论未获证明；见「缺口与举证」第 1 条。\n",
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
    certificate: &'a Certificate,
    root_gap: Option<&'a GapTree>,
    issues: &'a [&'a GapTree],
    root_expr: Option<&'a Expr>,
    pleadings: &'a BTreeMap<String, RulePleading>,
}

/// Section five: every gap with what it lacks and who must prove it.
///
/// The root's gap tree is expanded recursively. The gap trees of the other
/// contestable conclusions are shown one level deep; the report says so instead
/// of silently truncating them.
fn write_gaps_section(
    out: &mut String,
    inputs: &GapSection<'_>,
    questions: &mut BTreeMap<u8, Vec<Question>>,
) -> Result<(), String> {
    let env = inputs.env;
    let certificate = inputs.certificate;
    let root_gap = inputs.root_gap;
    let issues_sorted = inputs.issues;
    let root_expr = inputs.root_expr;
    let pleadings = inputs.pleadings;
    begin_section(out, "## 五、缺口与举证");
    out.push_str(
        "缺口：一条命题没有被任何可用的推导闭合，它和冲突是两回事（本节的展开来自推理器的缺口树，\
         不是证书记录）。举证责任：谁应当提出证据；证明标准：证据应达到的程度。\
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
                        "根结论「{}」未获证明；请确认缺少的证据是否存在，以及报告所列的举证责任与证明标准是否适用。",
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
                "{number}. 争点「{}」的缺口（只列第一层；更深缺口用 :gap <命题> 查看）\n",
                expr_text(&tree.goal)
            ));
            write_gap_body(out, tree, "   ", false, pleadings);
        }
    }

    if !wrote_any {
        if issues_sorted.is_empty() {
            out.push_str("根已证明，当前事实集下也没有可争结论，因此没有缺口。\n");
        } else {
            out.push_str("根已证明；当前争点都不是可展开的缺口，因此没有缺口。\n");
        }
    }
    // The certificate records a `MissingPremise` obligation for every gap node
    // it contains. Name them here so the evidence gap and its obligation id
    // cannot drift apart.
    let missing: Vec<&std_deduce_cert::OpenObligation> = certificate
        .open_obligations
        .iter()
        .filter(|obligation| obligation.kind == ObligationKind::MissingPremise)
        .collect();
    if !missing.is_empty() {
        out.push_str("证书记录的缺少前提义务：\n");
        for obligation in missing {
            out.push_str(&format!(
                "- 「{}」：{}（义务编号：{}；相关节点：{}）\n",
                escape_control(&obligation.id),
                escape_control(&obligation.description),
                escape_control(&obligation.id),
                node_list_text(&obligation.nodes)
            ));
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
                "{number}. 根结论「{}」未获证明（缺口）\n",
                expr_text(&tree.goal)
            ));
            write_gap_body(out, tree, "   ", true, pleadings);
            Ok(())
        }
        GapStatus::Conflicted => {
            out.push_str(&format!(
                "{number}. 根结论「{}」处于未决冲突（缺口根）\n   - 该命题处于未决冲突，不能作为缺口展开；见「未决与冲突」。\n",
                expr_text(&tree.goal)
            ));
            Ok(())
        }
        GapStatus::Defeated => {
            out.push_str(&format!(
                "{number}. 根结论「{}」在已裁决的冲突中败出（缺口根）\n   - 按冲突记录它不进入事实库；见「未决与冲突」。\n",
                expr_text(&tree.goal)
            ));
            Ok(())
        }
        GapStatus::InterpretedOnly => {
            out.push_str(&format!(
                "{number}. 根结论「{}」只由解释推出（缺口根）\n   - 规则阶段不消费解释结论，因此作为根结论仍不算证明；见「规则与出处」。\n",
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
                "{number}. 根结论「{}」含未闭合的规则参数（缺口根）\n   - 前提含有未随目标闭合的规则参数，无法继续展开。\n",
                expr_text(&tree.goal)
            ));
            Ok(())
        }
        GapStatus::Cycle => {
            out.push_str(&format!(
                "{number}. 根结论「{}」形成规则环（缺口根）\n   - 循环依赖：同一命题已在当前展开路径上，停止递归。\n",
                expr_text(&tree.goal)
            ));
            Ok(())
        }
    }
}

/// Render one gap tree body. `expand_children` controls whether nested missing
/// premises are expanded or only named.
fn write_gap_body(
    out: &mut String,
    tree: &GapTree,
    indent: &str,
    expand_children: bool,
    pleadings: &BTreeMap<String, RulePleading>,
) {
    let mut candidates: Vec<&std_deduce_reason::GapRule> = tree.candidates.iter().collect();
    candidates.sort_by(|a, b| a.rule.cmp(&b.rule));
    if candidates.is_empty() && tree.limit.is_none() {
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
        if candidate.missing.is_empty() && candidate.blocked_by.is_empty() {
            out.push_str(&format!("{indent}  - 证书没有记录它缺少什么。\n"));
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
                Some(child) if expand_children => {
                    out.push_str(&format!("{indent}    - 子缺口：\n"));
                    write_gap_body(out, child, &format!("{indent}      "), true, pleadings);
                }
                Some(_) => {
                    out.push_str(&format!(
                        "{indent}    - 子缺口：「{proposition}」在本报告只列第一层；更深缺口用 :gap <命题> 查看。\n"
                    ));
                }
                None => {
                    out.push_str(&format!(
                        "{indent}    - 子缺口：「{proposition}」未展开（已达到缺口树节点上限）。\n"
                    ));
                }
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
        out.push_str("证书记录里没有冲突。\n");
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
        out.push_str("证书记录的其他未决义务：\n");
        for obligation in other {
            out.push_str(&format!(
                "- [{}]「{}」：{}（相关节点：{}）\n",
                obligation_kind_label(obligation.kind),
                escape_control(&obligation.id),
                escape_control(&obligation.description),
                node_list_text(&obligation.nodes)
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
        "需人判断：模型不能替代人对法律概念、未经本项目审核的案件规则或逻辑未决事项作出判断。\n",
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
                out.push_str("   - 所在节点：证书记录的开放概念义务没有定位到具体节点。\n");
            } else {
                out.push_str("   - 所在节点：\n");
                for node in &nodes {
                    out.push_str(&format!(
                        "     - {}\n",
                        node_description(certificate, *node)?
                    ));
                }
            }
            out.push_str(
                "   - 为什么不能自动判定：概念的含义、判断标准以及本案是否满足，必须由律师或法院解释；\
                 证书只记录模型在推导中把它当成了已成立的命题。\n",
            );
            out.push_str(&format!(
                "   - 对应义务：`{}`\n",
                std_deduce_cert::OPEN_CONCEPT_OBLIGATION_ID
            ));
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
            "{number}. 开放概念义务「{}」：{}（相关节点：{}）。\n",
            escape_control(&obligation.id),
            escape_control(&obligation.description),
            node_list_text(&obligation.nodes)
        ));
        questions.entry(1).or_default().push(Question {
            text: format!(
                "开放概念义务「{}」需要人判断；请确认相关概念的判断标准。",
                escape_control(&obligation.id)
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
            "{number}. 需人判断义务「{}」：{}{}\n",
            escape_control(&obligation.id),
            escape_control(&obligation.description),
            node_suffix(&obligation.nodes)
        ));
        out.push_str(
            "   - 为什么不能自动判定：这条义务记录的事项需要人来决定，证书不替人给出判断。\n",
        );
        questions.entry(2).or_default().push(Question {
            text: format!(
                "义务「{}」需要人判断：{}。请确认应当如何处理。",
                escape_control(&obligation.id),
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
            "   - 为什么不能自动判定：这些规则由案件文件声明，未经官方包审核；\
             它们不是本项目审计过的法律依据。\n",
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
        out.push_str("证书没有记录开放概念、需人判断义务或案件扩展。\n");
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
                "节点 {node_id}（根命题「{}」，作为事实断言）",
                cert_expr_text(proposition)
            )
        }
        Node::RuleApplication {
            rule, conclusion, ..
        } => format!(
            "节点 {node_id}（规则「{}」的结论「{}」）",
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
                "节点 {node_id}（解释「{}」的结论「{}」）",
                escape_control(&entry.id),
                cert_expr_text(conclusion)
            )
        }
        Node::Gap { proposition, .. } => format!(
            "节点 {node_id}（缺口命题「{}」）",
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
            None => "证书列为事实，但没有可识别的身份记录".to_owned(),
        },
        Provenance::Rules { rules } if rules.is_empty() => {
            "由规则推出，但证书没有记录具体规则".to_owned()
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
                None => "由解释推出，但证书没有记录可识别的解释".to_owned(),
            }
        }
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
                _ => "两侧都是事实，证书没有记录可判定的身份先后。".to_owned(),
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
            "一侧由规则推出，但证书没有记录可重建的规则实例，无法核对优先级。".to_owned()
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
        format!("（相关节点：{}）", node_list_text(nodes))
    }
}

fn node_list_text(nodes: &[NodeId]) -> String {
    if nodes.is_empty() {
        return "证书未记录".to_owned();
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

/// Collect every held premise the certificate's gap nodes record.
///
/// Only the certificate's own `gap` node candidates carry `held`; the reasoner's
/// recursive gap tree does not (the certificate format, not the report, is the
/// place that records it). A nested gap is not in the certificate, so a fact
/// that only a nested candidate holds is not marked here.
fn collect_certificate_held(certificate: &Certificate, out: &mut BTreeSet<String>) {
    for node in &certificate.nodes {
        let Node::Gap { candidates, .. } = node else {
            continue;
        };
        for candidate in candidates {
            for held in &candidate.held {
                out.insert(expression_key(&Expr::from(held)));
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
