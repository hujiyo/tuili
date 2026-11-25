//! Natural-language rendering of a certificate.
//!
//! [`render_narrative`] turns the same certificate [`crate::render`] prints as
//! a formal tree into a Chinese "because … so …" explanation. It reads only
//! fields the certificate already records: assumption propositions, labels and
//! identities, rule conclusions, bindings and sources, conflict resolutions and
//! open obligations. It does not consult the reasoner, a pack registry or a
//! corpus, so it cannot add an inference, a citation or a legal conclusion that
//! the certificate does not contain.
//!
//! A fact is always attributed: a `verified` assumption reads "根据法院查明",
//! `user_asserted` reads "据用户陈述", `assumed` reads "作为分析假设", and
//! `stipulated` reads "双方无争议". An empty source list is printed as
//! "证书未记录来源" rather than omitted. A universal elimination reads
//! 「根据全称公理「…」（身份）的全称实例，所以「…」成立」 and then prints the
//! binding values; the universal fact's identity is the evidence its instance
//! rests on. A conflict is printed with its winner,
//! loser and recorded basis, or as "此处未决" with the recorded reason; a gap
//! lists its candidates, its universal-fact candidates (with the values an
//! instance would need and the refusal reason) and `unless` blockers. A
//! blocker's identity is taken from the assumption table when the certificate
//! records it, and otherwise the line says no identity is recorded.
//!
//! A gap candidate's rule may declare who must prove the missing premises and
//! to what standard, plus the same for its `unless` exceptions. The
//! certificate does not record these declarations, so the caller passes them
//! ([`render_narrative_with_context`]); every missing-premise sentence then
//! states the burden in plain words. An undeclared burden or standard is
//! written as such, never defaulted, and the standard is a label, never a
//! number.
//!
//! External text (rule names, labels, quotations, notes, declaration names and
//! obligations) is escaped before it is printed, so a newline or a terminal
//! control sequence in a certificate cannot forge another explanation line.
//! Node references and cycles are validated by the same function the formal
//! renderer uses; an invalid certificate is an error naming the node.

use std::collections::BTreeMap;

use std_deduce_kernel::env::{escape_control, RulePleading};
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::Expr;

use crate::expr::CertExpr;
use crate::model::{
    Assumption, Certificate, Conflict, FactIdentity, GapCandidate, Node, NodeId, ObligationKind,
    OpenObligation, PriorityClause, PriorityEdge, PriorityOrigin, Provenance, Resolution,
    ResolutionBasis, Side, UnresolvedReason,
};
use crate::render::{root_nodes, validate};
use crate::source::Source;

/// How many characters of a quotation are kept in the explanation. The full
/// quotation stays in the certificate; the narrative labels the shorter form as
/// a summary and says how long the original is, so it is not presented as the
/// complete text.
const QUOTE_SUMMARY_CHARS: usize = 60;

/// Render a certificate as a Chinese explanation.
///
/// The output is the proof the certificate records: the conclusion, the
/// because-so steps with their sources and parameter bindings, every gap,
/// every conflict resolution and every open obligation. An invalid node
/// reference or a cyclic node graph is an error naming the offending node.
///
/// This entry point prints no open-concept notice and no applicability
/// annotation; use [`render_narrative_with_context`] when the caller has
/// recomputed the concepts the root derivation depends on, or knows the
/// derivation's per-node applicability verdicts.
pub fn render_narrative(certificate: &Certificate) -> Result<String, String> {
    render_narrative_with_context(certificate, &[], &BTreeMap::new(), &BTreeMap::new())
}

/// Render as [`render_narrative`], with the parts of the derivation the
/// certificate itself does not record.
///
/// `open_concepts` is the recomputed list ([`crate::open::dependency`]) of the
/// certificate in its environment: the narrative never parses an obligation's
/// description to recover the concept names, and `std_deduce_cert::check`
/// rejects a certificate whose recorded obligation disagrees with that
/// recomputation. Naming the concepts here is what keeps a conclusion over
/// 「重大」 from reading as an unconditional proof; the names are escaped, so a
/// concept name cannot forge another explanation line. One
/// `此处需人判断：`<concept>`` line is printed per concept, after the root
/// conclusion and before the numbered steps.
///
/// `annotations` carries one applicability verdict per rule-application node
/// id. The certificate records no verdict, so a caller that knows the
/// derivation's judgements passes them by node id; each is appended to the
/// step's conclusion sentence (and to the one-line root conclusion), escaped
/// like every other external value. A node without an annotation, like a
/// caller with no recomputed open concepts, renders exactly as
/// [`render_narrative`] does.
///
/// `pleadings` is every declared rule's burden/standard, keyed by rule name.
/// Certificate v9 does not record these declarations, so the caller supplies
/// them; a missing-premise sentence then says who must present the evidence
/// and to what standard. An undeclared burden or standard reads `未声明举证责任`
/// / `未声明证明标准`, never a default; the standard itself is only a label and
/// is never turned into a number. A rule the map has no entry for is reported
/// as `未找到规则声明，无法报告` in the sentence, the same marker `:gap` prints,
/// instead of silently dropping the annotation.
pub fn render_narrative_with_context(
    certificate: &Certificate,
    open_concepts: &[String],
    annotations: &BTreeMap<NodeId, String>,
    pleadings: &BTreeMap<String, RulePleading>,
) -> Result<String, String> {
    validate(certificate)?;

    let mut out = String::new();
    match certificate.root {
        Some(root) => {
            write_conclusion(certificate, root, annotations, &mut out)?;
            write_open_concept_notice(open_concepts, &mut out);
            let mut order = Vec::new();
            let mut seen = vec![false; certificate.nodes.len()];
            collect_postorder(certificate, root, &mut seen, &mut order)?;
            write_proof(certificate, &order, annotations, pleadings, &mut out)?;
        }
        None => {
            out.push_str("【结论】证书没有根节点，不能给出单一结论。\n");
            let mut order = Vec::new();
            let mut seen = vec![false; certificate.nodes.len()];
            for root in root_nodes(certificate) {
                collect_postorder(certificate, root, &mut seen, &mut order)?;
            }
            write_proof(certificate, &order, annotations, pleadings, &mut out)?;
        }
    }

    write_conflicts(certificate, &mut out)?;
    write_obligations(certificate, pleadings, &mut out);
    Ok(out)
}

/// Write one `此处需人判断：`<concept>`` line per concept, after the conclusion.
fn write_open_concept_notice(open_concepts: &[String], out: &mut String) {
    for concept in open_concepts {
        out.push_str(&format!("此处需人判断：`{}`\n", escape_control(concept)));
    }
}

/// Write the one-line conclusion the certificate's root states.
fn write_conclusion(
    certificate: &Certificate,
    root: NodeId,
    annotations: &BTreeMap<NodeId, String>,
    out: &mut String,
) -> Result<(), String> {
    let Some(node) = certificate.nodes.get(root) else {
        return Err(format!(
            "节点 {root}：节点索引越界：证书只有 {} 个节点",
            certificate.nodes.len()
        ));
    };
    match node {
        Node::Assumption { assumption } => {
            let entry = assumption_at(certificate, *assumption, root)?;
            out.push_str("【结论】");
            out.push_str(&assumption_sentence(entry));
            out.push('\n');
        }
        Node::RuleApplication { conclusion, .. } => {
            out.push_str(&format!(
                "【结论】「{}」由规则推出。",
                print_expr(&Expr::from(conclusion))
            ));
            if let Some(annotation) = annotations.get(&root) {
                out.push_str(&format!(" 〔{}〕", escape_control(annotation)));
            }
            out.push('\n');
        }
        Node::InterpretationApplication { conclusion, .. } => {
            out.push_str(&format!(
                "【结论】「{}」由解释推出。\n",
                print_expr(&Expr::from(conclusion))
            ));
        }
        Node::AxiomInstance {
            axiom, conclusion, ..
        } => {
            out.push_str(&format!(
                "【结论】「{}」由全称公理「{}」实例化推出。\n",
                print_expr(&Expr::from(conclusion)),
                escape_control(axiom)
            ));
        }
        Node::Gap { proposition, .. } => {
            out.push_str(&format!(
                "【结论】「{}」未获证明（此处是缺口）。\n",
                print_expr(&Expr::from(proposition))
            ));
        }
    }
    Ok(())
}

/// Collect the proof nodes reachable from `id` after their premises.
fn collect_postorder(
    certificate: &Certificate,
    id: NodeId,
    seen: &mut [bool],
    order: &mut Vec<NodeId>,
) -> Result<(), String> {
    let Some(node) = certificate.nodes.get(id) else {
        return Err(format!(
            "节点 {id}：节点索引越界：证书只有 {} 个节点",
            certificate.nodes.len()
        ));
    };
    if seen[id] {
        return Ok(());
    }
    seen[id] = true;
    match node {
        Node::RuleApplication { premises, .. } => {
            for premise in premises {
                collect_postorder(certificate, *premise, seen, order)?;
            }
        }
        Node::InterpretationApplication { premise, .. } => {
            collect_postorder(certificate, *premise, seen, order)?;
        }
        Node::Assumption { .. } | Node::AxiomInstance { .. } | Node::Gap { .. } => {}
    }
    order.push(id);
    Ok(())
}

/// Write the numbered because-so steps and, after them, every reachable gap.
fn write_proof(
    certificate: &Certificate,
    order: &[NodeId],
    annotations: &BTreeMap<NodeId, String>,
    pleadings: &BTreeMap<String, RulePleading>,
    out: &mut String,
) -> Result<(), String> {
    let mut steps = Vec::new();
    let mut gaps = Vec::new();
    for id in order {
        match certificate.nodes.get(*id) {
            Some(
                Node::Assumption { .. }
                | Node::RuleApplication { .. }
                | Node::InterpretationApplication { .. }
                | Node::AxiomInstance { .. },
            ) => steps.push(*id),
            Some(Node::Gap { .. }) => gaps.push(*id),
            None => {
                return Err(format!(
                    "节点 {id}：节点索引越界：证书只有 {} 个节点",
                    certificate.nodes.len()
                ));
            }
        }
    }

    if !steps.is_empty() {
        begin_section(out, "【推理过程】");
        let mut step_of: BTreeMap<NodeId, usize> = BTreeMap::new();
        for (index, id) in steps.iter().enumerate() {
            step_of.insert(*id, index + 1);
            write_step(certificate, *id, index + 1, &step_of, annotations, out)?;
        }
    }

    if !gaps.is_empty() {
        begin_section(out, "【缺口】");
        for id in gaps {
            write_gap(certificate, id, pleadings, out)?;
        }
    }
    Ok(())
}

/// Write one numbered step: a fact or a rule application.
fn write_step(
    certificate: &Certificate,
    id: NodeId,
    number: usize,
    step_of: &BTreeMap<NodeId, usize>,
    annotations: &BTreeMap<NodeId, String>,
    out: &mut String,
) -> Result<(), String> {
    let Some(node) = certificate.nodes.get(id) else {
        return Err(format!(
            "节点 {id}：节点索引越界：证书只有 {} 个节点",
            certificate.nodes.len()
        ));
    };
    match node {
        Node::Assumption { assumption } => {
            let entry = assumption_at(certificate, *assumption, id)?;
            out.push_str(&format!("  {number}. {}", assumption_sentence(entry)));
            out.push('\n');
            if let Some(label) = &entry.label {
                out.push_str(&format!("     标签：{}\n", escape_control(label)));
            }
            write_sources(&entry.sources, out);
        }
        Node::RuleApplication {
            rule,
            conclusion,
            premises,
            bindings,
            sources,
            ..
        } => {
            let conclusion = print_expr(&Expr::from(conclusion));
            if premises.is_empty() {
                out.push_str(&format!(
                    "  {number}. 根据规则「{}」（该规则没有前提），所以「{conclusion}」成立。",
                    escape_control(rule)
                ));
            } else {
                let reasons = premises
                    .iter()
                    .map(|premise| premise_reference(certificate, *premise, step_of))
                    .collect::<Result<Vec<_>, String>>()?
                    .join("、");
                out.push_str(&format!(
                    "  {number}. 因为{reasons}，根据规则「{}」，所以「{conclusion}」成立。",
                    escape_control(rule)
                ));
            }
            if let Some(annotation) = annotations.get(&id) {
                out.push_str(&format!(" 〔{}〕", escape_control(annotation)));
            }
            out.push('\n');
            if !bindings.is_empty() {
                let instance = bindings
                    .iter()
                    .map(|binding| {
                        format!(
                            "{} ↦ {}",
                            escape_control(&binding.parameter),
                            print_expr(&Expr::from(&binding.value))
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("，");
                out.push_str(&format!("     实例：{instance}\n"));
            }
            write_sources(sources, out);
        }
        Node::InterpretationApplication {
            interpretation,
            premise,
            conclusion,
        } => {
            let entry = certificate
                .interpretations
                .get(*interpretation)
                .ok_or_else(|| {
                    format!(
                        "节点 {id}：引用了不存在的解释 {interpretation}：证书只有 {} 条解释",
                        certificate.interpretations.len()
                    )
                })?;
            let conclusion = print_expr(&Expr::from(conclusion));
            let premise = premise_reference(certificate, *premise, step_of)?;
            out.push_str(&format!(
                "  {number}. 因为{premise}，根据解释「{}」（方向 {}），所以「{conclusion}」成立。\n",
                escape_control(&entry.id),
                entry.direction.keyword()
            ));
            write_sources(&entry.sources, out);
        }
        Node::AxiomInstance {
            axiom,
            identity,
            bindings,
            conclusion,
            sources,
        } => {
            out.push_str(&format!(
                "  {number}. 根据全称公理「{}」（{}）的全称实例，所以「{}」成立。",
                escape_control(axiom),
                identity.label_zh(),
                print_expr(&Expr::from(conclusion))
            ));
            if let Some(annotation) = annotations.get(&id) {
                out.push_str(&format!(" 〔{}〕", escape_control(annotation)));
            }
            out.push('\n');
            if !bindings.is_empty() {
                let instance = bindings
                    .iter()
                    .map(|binding| {
                        format!(
                            "{} ↦ {}",
                            escape_control(&binding.parameter),
                            print_expr(&Expr::from(&binding.value))
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("，");
                out.push_str(&format!("     实例：{instance}\n"));
            }
            write_sources(sources, out);
        }
        Node::Gap { .. } => {
            return Err(format!("节点 {id}：缺口不应被编号为推理步骤"));
        }
    }
    Ok(())
}

/// The reference to a premise in a because clause.
fn premise_reference(
    certificate: &Certificate,
    id: NodeId,
    step_of: &BTreeMap<NodeId, usize>,
) -> Result<String, String> {
    let Some(node) = certificate.nodes.get(id) else {
        return Err(format!(
            "节点 {id}：节点索引越界：证书只有 {} 个节点",
            certificate.nodes.len()
        ));
    };
    let proposition = match node {
        Node::Assumption { assumption } => {
            &assumption_at(certificate, *assumption, id)?.proposition
        }
        Node::RuleApplication { conclusion, .. } => conclusion,
        Node::InterpretationApplication { conclusion, .. } => conclusion,
        Node::AxiomInstance { conclusion, .. } => conclusion,
        Node::Gap { proposition, .. } => proposition,
    };
    let printed = print_expr(&Expr::from(proposition));
    Ok(match step_of.get(&id) {
        Some(number) => format!("「{printed}」（第 {number} 条）"),
        None => format!("「{printed}」（缺口未闭合）"),
    })
}

/// Write a certificate's sources, or say that none were recorded.
fn write_sources(sources: &[Source], out: &mut String) {
    if sources.is_empty() {
        out.push_str("     来源：证书未记录来源。\n");
        return;
    }
    for source in sources {
        out.push_str(&format!("     来源：{}\n", source_text(source)));
    }
}

/// One source with its citation and the optional fields the narrative keeps.
fn source_text(source: &Source) -> String {
    let mut text = source.one_line();
    if let Some(effective) = source
        .effective
        .as_deref()
        .filter(|value| !value.is_empty())
    {
        text.push_str(&format!("；生效：{}", escape_control(effective)));
    }
    if !source.jurisdiction.is_empty() {
        text.push_str(&format!("；管辖：{}", escape_control(&source.jurisdiction)));
    }
    if !source.quote.is_empty() {
        text.push_str(&format!("；引文摘要：{}", quote_summary(&source.quote)));
    }
    if !source.note.is_empty() {
        text.push_str(&format!("；说明：{}", escape_control(&source.note)));
    }
    if !source.url.is_empty() {
        text.push_str(&format!("；链接：{}", escape_control(&source.url)));
    }
    text
}

/// A quotation, shortened only when it is longer than the summary limit.
fn quote_summary(quote: &str) -> String {
    let total = quote.chars().count();
    if total <= QUOTE_SUMMARY_CHARS {
        return format!("「{}」", escape_control(quote));
    }
    let summary: String = quote.chars().take(QUOTE_SUMMARY_CHARS).collect();
    format!(
        "（前 {QUOTE_SUMMARY_CHARS} 字，共 {total} 字）「{}…」",
        escape_control(&summary)
    )
}

/// Write one gap with every candidate the certificate records.
fn write_gap(
    certificate: &Certificate,
    id: NodeId,
    pleadings: &BTreeMap<String, RulePleading>,
    out: &mut String,
) -> Result<(), String> {
    let Some(Node::Gap {
        proposition,
        candidates,
        axiom_candidates,
        note,
    }) = certificate.nodes.get(id)
    else {
        return Err(format!("节点 {id}：该节点不是缺口，无法渲染缺口"));
    };
    out.push_str(&format!(
        "  · 「{}」没有可闭合的推导。\n",
        print_expr(&Expr::from(proposition))
    ));
    if let Some(note) = note {
        out.push_str(&format!("  · 说明：{}\n", escape_control(note)));
    }
    for candidate in axiom_candidates {
        let mut line = format!("  · 公理候选「{}」", escape_control(&candidate.axiom));
        if !candidate.bindings.is_empty() {
            let bindings = candidate
                .bindings
                .iter()
                .map(|binding| {
                    format!(
                        "{} ↦ {}",
                        escape_control(&binding.parameter),
                        print_expr(&Expr::from(&binding.value))
                    )
                })
                .collect::<Vec<_>>()
                .join("，");
            line.push_str(&format!("（绑定：{bindings}）"));
        }
        match &candidate.problem {
            Some(problem) => line.push_str(&format!("：未实例化：{}。", escape_control(problem))),
            None => line.push_str("：可由该公理实例化，但本次推导没有触发它。"),
        }
        out.push_str(&line);
        out.push('\n');
    }
    if candidates.is_empty() && axiom_candidates.is_empty() {
        out.push_str("  · 证书没有记录候选规则或公理，无法说明还缺什么。\n");
        return Ok(());
    }
    for candidate in candidates {
        write_gap_candidate(certificate, candidate, pleadings, out);
    }
    Ok(())
}

fn write_gap_candidate(
    certificate: &Certificate,
    candidate: &GapCandidate,
    pleadings: &BTreeMap<String, RulePleading>,
    out: &mut String,
) {
    out.push_str(&format!(
        "  · 候选规则「{}」：",
        escape_control(&candidate.rule)
    ));
    let mut clauses = Vec::new();
    if !candidate.missing.is_empty() {
        let missing = candidate
            .missing
            .iter()
            .map(|proposition| format!("「{}」", print_expr(&Expr::from(proposition))))
            .collect::<Vec<_>>()
            .join("、");
        let mut clause = format!("缺少前提{missing}");
        let requirement = match pleadings.get(&candidate.rule) {
            Some(pleading) => pleading.requirements.sentence_zh(false),
            // The caller supplied no declaration for this rule. Saying so
            // matches `:gap`, which writes the same marker instead of
            // silently dropping the annotation.
            None => "未找到规则声明，无法报告".to_owned(),
        };
        clause.push_str(&format!("（{requirement}）"));
        clauses.push(clause);
    }
    if !candidate.blocked_by.is_empty() {
        let blockers = candidate
            .blocked_by
            .iter()
            .map(|proposition| blocked_condition(certificate, proposition))
            .collect::<Vec<_>>()
            .join("、");
        let mut clause = format!("unless 条件{blockers}已成立，故该规则被阻断");
        let exception = match pleadings.get(&candidate.rule) {
            Some(pleading) => pleading.exceptions.sentence_zh(true),
            None => "例外未找到规则声明，无法报告".to_owned(),
        };
        clause.push_str(&format!("（{exception}）"));
        clauses.push(clause);
    }
    if clauses.is_empty() {
        out.push_str("证书没有记录它缺少什么。\n");
    } else {
        out.push_str(&clauses.join("；"));
        out.push_str("。\n");
    }
    if candidate.sources.is_empty() {
        out.push_str("     来源：证书未记录来源。\n");
    } else {
        for source in &candidate.sources {
            out.push_str(&format!("     来源：{}\n", source_text(source)));
        }
    }
}

/// A blocker proposition, with its identity when that attribution is
/// unambiguous in the certificate.
fn blocked_condition(certificate: &Certificate, proposition: &CertExpr) -> String {
    let printed = print_expr(&Expr::from(proposition));
    match blocker_assumption(certificate, proposition) {
        Some(entry) => format!("「{printed}」（{}）", entry.identity.label_zh()),
        None => format!("「{printed}」（证书未记录身份）"),
    }
}

/// The assumption that may be attributed to a blocker.
///
/// A gap candidate records only the blocker proposition, not whether it was
/// seeded as a fact or derived by a rule. Attributing the identity of a fact
/// that happens to have the same proposition would mislabel a rule-derived
/// blocker, so this returns a match only when exactly one assumption has the
/// proposition and no rule application in the certificate concludes it. The
/// formal renderer keeps its older approximation; the narrative is stricter
/// because it states the identity in words instead of leaving it implicit.
fn blocker_assumption<'a>(
    certificate: &'a Certificate,
    proposition: &CertExpr,
) -> Option<&'a Assumption> {
    let mut matches = certificate
        .assumptions
        .iter()
        .filter(|entry| &entry.proposition == proposition);
    let first = matches.next()?;
    if matches.next().is_some() {
        return None;
    }
    let derived = certificate.nodes.iter().any(|node| {
        matches!(
            node,
            Node::RuleApplication { conclusion, .. } if conclusion == proposition
        ) || matches!(
            node,
            Node::InterpretationApplication { conclusion, .. } if conclusion == proposition
        ) || matches!(
            node,
            Node::AxiomInstance { conclusion, .. } if conclusion == proposition
        )
    });
    if derived {
        None
    } else {
        Some(first)
    }
}

/// Write the `【冲突】` section when the certificate records any conflict.
fn write_conflicts(certificate: &Certificate, out: &mut String) -> Result<(), String> {
    if certificate.conflicts.is_empty() {
        return Ok(());
    }
    begin_section(out, "【冲突】");
    for (index, conflict) in certificate.conflicts.iter().enumerate() {
        let status = match conflict.resolution {
            Resolution::Unresolved { .. } => "此处未决",
            Resolution::Defeated { .. } => "已裁决",
        };
        out.push_str(&format!(
            "  {}. 「{}」与「{}」冲突，{status}。\n",
            index + 1,
            print_expr(&Expr::from(&conflict.left)),
            print_expr(&Expr::from(&conflict.right))
        ));
        write_side(certificate, "左侧", &conflict.left, &conflict.left_by, out);
        write_side(
            certificate,
            "右侧",
            &conflict.right,
            &conflict.right_by,
            out,
        );
        match &conflict.resolution {
            Resolution::Defeated { winner, basis } => {
                write_defeat(certificate, conflict, *winner, basis, out);
            }
            Resolution::Unresolved { reason } => {
                write_unresolved(certificate, conflict, reason, out);
            }
        }
    }
    Ok(())
}

fn write_side(
    certificate: &Certificate,
    label: &str,
    proposition: &CertExpr,
    provenance: &Provenance,
    out: &mut String,
) {
    out.push_str(&format!(
        "     {label}「{}」（{}）。\n",
        print_expr(&Expr::from(proposition)),
        provenance_phrase(certificate, proposition, provenance)
    ));
}

/// How one side of a conflict is supported, for the narrative.
fn provenance_phrase(
    certificate: &Certificate,
    proposition: &CertExpr,
    provenance: &Provenance,
) -> String {
    match provenance {
        Provenance::Assumption => match assumption_for(certificate, proposition) {
            Some(entry) => {
                let mut phrase = format!("证书记为{}", entry.identity.label_zh());
                if let Some(label) = &entry.label {
                    phrase.push_str(&format!("，标签：{}", escape_control(label)));
                }
                phrase
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
        Provenance::Axiom { axiom } => {
            format!("由全称公理「{}」实例化推出", escape_control(axiom))
        }
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

fn write_defeat(
    certificate: &Certificate,
    conflict: &Conflict,
    winner: Side,
    basis: &ResolutionBasis,
    out: &mut String,
) {
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
    out.push_str(&format!(
        "     胜出：「{}」（{}）。\n",
        print_expr(&Expr::from(win)),
        provenance_phrase(certificate, win, win_by)
    ));
    out.push_str(&format!(
        "     被否决：「{}」（{}）。\n",
        print_expr(&Expr::from(lose)),
        provenance_phrase(certificate, lose, lose_by)
    ));
    match basis {
        ResolutionBasis::Assumption => {
            let text = if matches!(lose_by, Provenance::Rules { .. }) {
                "严格事实优先于可废止规则结论。"
            } else if matches!(lose_by, Provenance::Axiom { .. }) {
                "严格事实优先于公理实例结论。"
            } else if matches!(lose_by, Provenance::Interpretation { .. }) {
                "严格事实优先于解释结论。"
            } else {
                "严格事实优先于未经证明的主张。"
            };
            out.push_str(&format!("     依据：{text}\n"));
        }
        ResolutionBasis::Priority { edges } => {
            for edge in edges {
                out.push_str(&format!("     依据：{}\n", priority_edge_text(edge)));
            }
        }
    }
}

fn write_unresolved(
    certificate: &Certificate,
    conflict: &Conflict,
    reason: &UnresolvedReason,
    out: &mut String,
) {
    let text = match reason {
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
            match fact_side {
                Some(proposition) => format!(
                    "「{}」只是「{}」，未经证明，不能自动胜过{conclusion}。",
                    print_expr(&Expr::from(proposition)),
                    identity.label_zh()
                ),
                None => format!(
                    "一侧只是「{}」，未经证明，不能自动胜过{conclusion}。",
                    identity.label_zh()
                ),
            }
        }
        UnresolvedReason::UnknownWitnesses => {
            "一侧由规则推出，但证书没有记录可重建的规则实例，无法核对优先级。".to_owned()
        }
        UnresolvedReason::NoPriority => {
            let interpretation = matches!(conflict.left_by, Provenance::Interpretation { .. })
                || matches!(conflict.right_by, Provenance::Interpretation { .. });
            let axiom = matches!(conflict.left_by, Provenance::Axiom { .. })
                || matches!(conflict.right_by, Provenance::Axiom { .. });
            if interpretation {
                "解释结论与另一方之间没有可用的优先声明，不能判定谁胜出。".to_owned()
            } else if axiom {
                "公理实例结论与另一方之间没有可用的优先声明，不能判定谁胜出。".to_owned()
            } else {
                "两侧规则之间没有声明优先级，不能判定谁胜出。".to_owned()
            }
        }
        UnresolvedReason::PriorityUnusable { .. } => {
            "声明的优先级不足以裁决（覆盖不全、双向覆盖或位于优先级环内）。".to_owned()
        }
    };
    out.push_str(&format!("     原因：{text}\n"));
    if let UnresolvedReason::PriorityUnusable { declared } = reason {
        for edge in declared {
            out.push_str(&format!("     已声明：{}\n", priority_edge_text(edge)));
        }
    }
}

/// One declared priority edge as the narrative cites it.
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

/// A list of citations, or an explicit statement that none were recorded.
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

/// Write the open obligations the certificate records.
fn write_obligations(
    certificate: &Certificate,
    pleadings: &BTreeMap<String, RulePleading>,
    out: &mut String,
) {
    if certificate.open_obligations.is_empty() {
        return;
    }
    begin_section(out, "【未决义务】");
    for obligation in &certificate.open_obligations {
        out.push_str(&obligation_line(certificate, pleadings, obligation));
        out.push('\n');
    }
}

fn obligation_line(
    certificate: &Certificate,
    pleadings: &BTreeMap<String, RulePleading>,
    obligation: &OpenObligation,
) -> String {
    let mut line = format!(
        "  - [{}] {}",
        obligation_kind_label(obligation.kind),
        escape_control(&obligation.description)
    );
    let mut details = Vec::new();
    if !obligation.id.is_empty() {
        details.push(format!("义务编号：{}", escape_control(&obligation.id)));
    }
    if !obligation.nodes.is_empty() {
        details.push(format!(
            "相关节点：{}",
            obligation
                .nodes
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("、")
        ));
    }
    // A missing-premise obligation points at the certificate's gap node. The
    // declaration itself is not recorded in the certificate, so the caller's
    // pleadings map supplies the same burden sentence the 【缺口】 section
    // prints; the obligation line does not infer a default.
    if obligation.kind == ObligationKind::MissingPremise {
        let mut missing = Vec::new();
        for id in &obligation.nodes {
            let Some(Node::Gap { candidates, .. }) = certificate.nodes.get(*id) else {
                continue;
            };
            for candidate in candidates {
                if candidate.missing.is_empty() {
                    continue;
                }
                let premises = candidate
                    .missing
                    .iter()
                    .map(|proposition| format!("「{}」", print_expr(&Expr::from(proposition))))
                    .collect::<Vec<_>>()
                    .join("、");
                let requirement = match pleadings.get(&candidate.rule) {
                    Some(pleading) => pleading.requirements.sentence_zh(false),
                    None => "未找到规则声明，无法报告".to_owned(),
                };
                missing.push(format!(
                    "规则「{}」缺少前提{premises}：{requirement}",
                    escape_control(&candidate.rule)
                ));
            }
        }
        if !missing.is_empty() {
            details.push(format!("举证责任：{}", missing.join("；")));
        }
    }
    if !details.is_empty() {
        line.push_str(&format!("（{}）", details.join("；")));
    }
    line
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

/// The sentence a fact is introduced with, always carrying its identity.
fn assumption_sentence(entry: &Assumption) -> String {
    let proposition = print_expr(&Expr::from(&entry.proposition));
    match entry.identity {
        FactIdentity::Verified => format!("根据法院查明，「{proposition}」成立。"),
        FactIdentity::UserAsserted => {
            format!("据用户陈述，「{proposition}」成立（这是用户主张，未经独立证明）。")
        }
        FactIdentity::Assumed => {
            format!("作为分析假设，「{proposition}」假定成立（未经独立证明）。")
        }
        FactIdentity::Stipulated => format!("双方无争议，「{proposition}」成立。"),
        FactIdentity::Disputed => {
            format!("「{proposition}」是对方争议的事实（不参与推导）。")
        }
    }
}

fn is_strict(identity: FactIdentity) -> bool {
    matches!(identity, FactIdentity::Verified | FactIdentity::Stipulated)
}

fn assumption_at(
    certificate: &Certificate,
    index: usize,
    node: NodeId,
) -> Result<&Assumption, String> {
    certificate.assumptions.get(index).ok_or_else(|| {
        format!(
            "节点 {node}：引用了不存在的假设 {index}：证书只有 {} 条假设",
            certificate.assumptions.len()
        )
    })
}

fn assumption_for<'a>(
    certificate: &'a Certificate,
    proposition: &CertExpr,
) -> Option<&'a Assumption> {
    certificate
        .assumptions
        .iter()
        .find(|entry| &entry.proposition == proposition)
}

/// Start a new section with one blank line before it.
fn begin_section(out: &mut String, title: &str) {
    if !out.is_empty() {
        out.push('\n');
    }
    out.push_str(title);
    out.push('\n');
}
