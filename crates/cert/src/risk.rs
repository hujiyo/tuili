//! The risk themes a derivation is about.
//!
//! A theory declares a predicate's theme with `risk <类别> <谓词>` (for example
//! `risk 人身安全 人身受到伤害`), and [`crate::check`]'s environment exposes the
//! markers through [`std_deduce_kernel::Env::risk_markers`]. The judgement here
//! is therefore structural: a theme applies when a proposition on the root's
//! proof graph has that marked predicate as its kernel predicate head. The
//! system never matches printed text, never guesses from a predicate's
//! spelling, and never infers a theme from rule names: a predicate is risky only
//! because a declaration says so, and `:inspect` shows that declaration.
//!
//! ## Which propositions count
//!
//! Every node reachable from [`Certificate::root`] states a proposition, and the
//! case content is exactly what the requested conclusion is about:
//!
//! * a `rule_application` conclusion — the step that states the themed
//!   proposition (its rule and citation are the evidence);
//! * an `axiom_instance` conclusion — universal elimination stating it;
//! * an `interpretation_application` conclusion — an enabled interpretation
//!   licensing it;
//! * an assumption node — a fact the case asserts (`:why` of a themed goal must
//!   warn even when the goal is an assumed fact);
//! * a gap node — an unproved goal still belongs to its theme, so asking whether
//!   a personal-safety proposition holds is a personal-safety question whether
//!   or not it can be proved.
//!
//! An unrelated branch is ignored: a certificate lists the facts and conflicts
//! of the whole fixed point, so a themed proposition the root does not use must
//! not change the warning. A graph node's proposition is normalized first (the
//! kernel's beta/delta/zeta reductions only; a predicate is opaque), so a `def`
//! alias of a themed predicate is recognised as the same predicate, and a head
//! that is not a constant (a variable, a quantified form, a sort) is never read
//! as a declared predicate.
//!
//! ## What the report is
//!
//! [`RiskReport`] lists the themes that apply, in the fixed keyword order, each
//! with one evidence line per proving node. The evidence names the proposition,
//! the declared theme and the declaration (`risk <类别> <谓词>`), plus the
//! rule/axiom/interpretation and its recorded sources when the node has one. The
//! report is a **derived view**: it is never written into the certificate, so
//! certificate v8 and `:cert` JSON are unchanged, and `:verify-cert` does not
//! recompute it. The five trust labels are a different judgement: a themed case
//! keeps its trust label (a proof under strict facts is still `已验证`), and the
//! risk theme is reported next to it rather than folded into
//! [`crate::TrustLabel::NeedsLawyerJudgment`].
//!
//! ## The non-judgment hint
//!
//! A declared `risk` is the only input that may grade a case. A theory without
//! markers would stay completely silent about a plainly safety-related case, and
//! most theories have none (the bundled pack is the constitution only).
//! [`derive_risk`] therefore adds one **hint** sentence when — and only when — no
//! `risk` declaration matched:
//!
//! * it looks for [`HINT_TERMS`], a small word list documented here and in the
//!   README, inside the *printed* propositions of the root's proof graph;
//! * the sentence names the matched terms and the theme each most plausibly
//!   belongs to, and says `可能属于 … 题材`, never `高风险题材`;
//! * it says the case declared no `risk` (or that none covered this derivation),
//!   and that it changes no label, no exit code and no certificate;
//! * it is suppressed the moment a declaration matches, so a graded case never
//!   shows both;
//! * the list is not a classifier: an ambiguous term keeps the hint wording
//!   instead of being promoted into a verdict (拘留 can be administrative, 报警
//!   says nothing about who did what).
//!
//! The hint belongs to the same derived view: it changes no label, no exit code
//! and no certificate field, and `:labels` does not print it at all.

use std::collections::{BTreeMap, BTreeSet};

use std_deduce_kernel::env::escape_control;
use std_deduce_kernel::norm::normalize;
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{Ctx, Env, Expr, Name, RiskTheme};

use crate::expr::CertExpr;
use crate::model::{Certificate, Node, NodeId};
use crate::render::validate;
use crate::source::Source;

/// The warning a high-risk theme prints, as the `；`-joined suffix.
///
/// The exact line is composed by [`RiskReport::warning_line`] so the themes and
/// the advice cannot drift apart between the commands that print it.
const HIGH_RISK_ADVICE: &str = "建议尽快咨询执业律师";

/// The small, documented word list behind the non-judgment hint.
///
/// A declared `risk` is the *only* thing that may grade a case, and most
/// theories do not declare one; without this list a case whose propositions
/// plainly talk about an offence or bodily harm would get no sentence at all.
/// The list is deliberately tiny, written down here and in the README, and it is
/// matched against the printed propositions of the root's proof graph only.
///
/// It is **not** a classifier: the theme next to each term is the one a reader
/// would most plausibly expect, and an ambiguous term keeps the hint wording
/// instead of being promoted into a verdict. `拘留` can also be an
/// administrative detention; `报警` says nothing about who did what. The hint
/// therefore says `可能属于 … 题材` and never `高风险题材`.
pub const HINT_TERMS: &[(&str, RiskTheme)] = &[
    ("犯罪", RiskTheme::Criminal),
    ("有期徒刑", RiskTheme::Criminal),
    ("拘役", RiskTheme::Criminal),
    ("拘留", RiskTheme::Criminal),
    ("重伤", RiskTheme::PersonalSafety),
    ("死亡", RiskTheme::PersonalSafety),
    ("自杀", RiskTheme::PersonalSafety),
    ("报警", RiskTheme::PersonalSafety),
];

/// The hint line for a case whose root graph mentions a listed term but whose
/// propositions are not covered by any `risk` declaration.
///
/// `declares_risk` distinguishes "the theory declares no marker at all" from
/// "it declares markers, none of which covers this derivation": the sentence
/// must not claim the case declared nothing when it did.
fn hint_line(propositions: &BTreeSet<String>, declares_risk: bool) -> Option<String> {
    let terms: Vec<&str> = HINT_TERMS
        .iter()
        .filter(|(term, _)| propositions.iter().any(|text| text.contains(*term)))
        .map(|(term, _)| *term)
        .collect();
    if terms.is_empty() {
        return None;
    }
    let mut themes: Vec<RiskTheme> = HINT_TERMS
        .iter()
        .filter(|(term, _)| terms.contains(term))
        .map(|(_, theme)| *theme)
        .collect();
    themes.sort();
    themes.dedup();
    let terms = terms
        .iter()
        .map(|term| format!("「{term}」"))
        .collect::<Vec<_>>()
        .join("");
    let themes = themes
        .iter()
        .map(|theme| theme.label_zh())
        .collect::<Vec<_>>()
        .join("、");
    let absence = if declares_risk {
        "但没有命中的 risk 声明"
    } else {
        "但本案没有声明 risk"
    };
    Some(format!(
        "提示：案情中出现{terms}相关用语，可能属于{themes}题材，{absence}；\
         这只是提示，不改变标签、不改退出码。"
    ))
}

/// One theme that applies, with the evidence lines that produced it, and the
/// non-judgment hint a case without any matching declaration can get.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RiskReport {
    themes: Vec<RiskTheme>,
    evidence: Vec<(RiskTheme, Vec<String>)>,
    hint: Option<String>,
}

impl RiskReport {
    /// The themes that apply, in the fixed keyword order.
    pub fn themes(&self) -> &[RiskTheme] {
        &self.themes
    }

    /// Whether the derivation is about at least one themed proposition.
    ///
    /// A low-risk derivation has no theme; callers print no warning line at all
    /// for it, so an ordinary case does not get noise.
    pub fn is_high_risk(&self) -> bool {
        !self.themes.is_empty()
    }

    /// The evidence lines for `theme`, or an empty slice when it does not apply.
    pub fn evidence(&self, theme: RiskTheme) -> &[String] {
        self.evidence
            .iter()
            .find(|(entry, _)| *entry == theme)
            .map(|(_, lines)| lines.as_slice())
            .unwrap_or(&[])
    }

    /// The one explicit warning line, or `None` for a low-risk derivation.
    ///
    /// The themes are joined with `、` in the fixed keyword order, so the same
    /// case prints the same line every time.
    pub fn warning_line(&self) -> Option<String> {
        if self.themes.is_empty() {
            return None;
        }
        let themes = self
            .themes
            .iter()
            .map(|theme| theme.label_zh())
            .collect::<Vec<_>>()
            .join("、");
        Some(format!("高风险题材：涉及{themes}；{HIGH_RISK_ADVICE}。"))
    }

    /// The non-judgment hint, or `None` when it does not apply.
    ///
    /// This is **not** a grading: it exists only because a declared `risk` is
    /// the only thing that may mark a case high-risk, and a theory that declares
    /// none would otherwise stay silent about a plainly safety-related case.
    /// It is produced only when no `risk` declaration matched, it is worded so a
    /// reader cannot mistake it for a verdict, and it changes no label, no exit
    /// code and no certificate field.
    pub fn hint_line(&self) -> Option<&str> {
        self.hint.as_deref()
    }
}

/// Derive the risk themes of a certificate from its root proof graph and the
/// environment's `risk` markers.
///
/// An invalid node reference is an error naming the node, not a silently
/// ignored theme. A certificate whose root proves nothing still reports the
/// theme of its gap proposition: the goal is about that theme either way. A
/// certificate with no root at all has no single conclusion, so it reports
/// nothing rather than guessing which of its statements the reader asked about.
pub fn derive_risk(env: &Env, certificate: &Certificate) -> Result<RiskReport, String> {
    validate(certificate)?;

    // One predicate carries at most one theme. The loader refuses a repeated
    // marker, so a conflicting pair here can only come from a hand-built
    // environment; report it instead of silently picking one.
    let mut markers: BTreeMap<Name, RiskTheme> = BTreeMap::new();
    for (pred, theme) in env.risk_markers() {
        if markers.insert(pred.clone(), theme).is_some() {
            return Err(format!(
                "谓词 `{pred}` 在环境里有重复的 risk 标记：risk 声明必须唯一"
            ));
        }
    }
    let declares_risk = !markers.is_empty();

    let Some(root) = certificate.root else {
        return Ok(RiskReport {
            themes: Vec::new(),
            evidence: Vec::new(),
            hint: None,
        });
    };

    let mut visited = vec![false; certificate.nodes.len()];
    let mut pending: Vec<NodeId> = vec![root];
    let mut lines: BTreeMap<RiskTheme, BTreeSet<String>> = BTreeMap::new();
    // The printed propositions of the root graph, for the non-judgment hint.
    // They are collected even when a theme matched: the hint is only printed
    // when no declaration did, and the caller decides from this report.
    let mut propositions: BTreeSet<String> = BTreeSet::new();
    while let Some(id) = pending.pop() {
        if id >= certificate.nodes.len() {
            return Err(format!(
                "节点 {id}：节点索引越界：证书只有 {} 个节点",
                certificate.nodes.len()
            ));
        }
        if visited[id] {
            continue;
        }
        visited[id] = true;
        let node = &certificate.nodes[id];
        let (proposition, step) = match node {
            Node::Assumption { assumption } => {
                let entry = certificate.assumptions.get(*assumption).ok_or_else(|| {
                    format!(
                        "节点 {id}：引用了不存在的假设 {assumption}：证书只有 {} 条假设",
                        certificate.assumptions.len()
                    )
                })?;
                (
                    &entry.proposition,
                    Step::Fact {
                        identity: entry.identity.label_zh(),
                        sources: &entry.sources,
                    },
                )
            }
            Node::RuleApplication {
                rule,
                conclusion,
                premises,
                sources,
                ..
            } => {
                for premise in premises {
                    if *premise >= certificate.nodes.len() {
                        return Err(format!(
                            "节点 {id}：前提 {premise} 越界：证书只有 {} 个节点",
                            certificate.nodes.len()
                        ));
                    }
                    pending.push(*premise);
                }
                (
                    conclusion,
                    Step::Rule {
                        name: rule,
                        sources,
                    },
                )
            }
            Node::InterpretationApplication {
                interpretation,
                premise,
                conclusion,
            } => {
                if *premise >= certificate.nodes.len() {
                    return Err(format!(
                        "节点 {id}：前提 {premise} 越界：证书只有 {} 个节点",
                        certificate.nodes.len()
                    ));
                }
                pending.push(*premise);
                let entry = certificate
                    .interpretations
                    .get(*interpretation)
                    .ok_or_else(|| {
                        format!(
                            "节点 {id}：引用了不存在的解释 {interpretation}：证书只有 {} 条解释",
                            certificate.interpretations.len()
                        )
                    })?;
                (
                    conclusion,
                    Step::Interpretation {
                        id: &entry.id,
                        sources: &entry.sources,
                    },
                )
            }
            Node::AxiomInstance {
                axiom,
                conclusion,
                sources,
                ..
            } => (
                conclusion,
                Step::Axiom {
                    name: axiom,
                    sources,
                },
            ),
            // A gap can never be a premise of a proving step; its own
            // proposition still belongs to its theme.
            Node::Gap { proposition, .. } => (
                proposition,
                Step::Gap {
                    is_root: id == root,
                },
            ),
        };
        propositions.insert(print_expr(&Expr::from(proposition)));
        if markers.is_empty() {
            continue;
        }
        let Some(head) = themed_head(env, proposition, &markers)? else {
            continue;
        };
        let (pred, theme) = head;
        let line = evidence_line(proposition, &pred, theme, &step);
        lines.entry(theme).or_default().insert(line);
    }

    if lines.is_empty() {
        // No declaration covers this derivation, so there is no theme and no
        // evidence. A listed term in the propositions may still earn one
        // sentence, explicitly marked as a hint.
        return Ok(RiskReport {
            themes: Vec::new(),
            evidence: Vec::new(),
            hint: hint_line(&propositions, declares_risk),
        });
    }

    let themes: Vec<RiskTheme> = lines.keys().copied().collect();
    let evidence = themes
        .iter()
        .map(|theme| {
            let lines = lines
                .get(theme)
                .map(|lines| lines.iter().cloned().collect::<Vec<_>>())
                .unwrap_or_default();
            (*theme, lines)
        })
        .collect();
    Ok(RiskReport {
        themes,
        evidence,
        hint: None,
    })
}

/// How a themed proposition entered the proof graph.
enum Step<'a> {
    Fact {
        identity: &'static str,
        sources: &'a [Source],
    },
    Rule {
        name: &'a str,
        sources: &'a [Source],
    },
    Interpretation {
        id: &'a str,
        sources: &'a [Source],
    },
    Axiom {
        name: &'a str,
        sources: &'a [Source],
    },
    Gap {
        is_root: bool,
    },
}

/// One evidence line, naming the proposition, the predicate, the theme, the
/// declaration that marked it and the step that stated it.
fn evidence_line(proposition: &CertExpr, pred: &Name, theme: RiskTheme, step: &Step<'_>) -> String {
    let proposition = print_expr(&Expr::from(proposition));
    let predicate = escape_control(pred);
    let theme = theme.label_zh();
    let declaration = format!("risk {theme} {predicate}");
    match step {
        Step::Fact { identity, sources } => format!(
            "命题「{proposition}」是事实〔{identity}〕，其谓词「{predicate}」被声明为风险题材「{theme}」\
             （声明 `{declaration}`）；{}",
            sources_text(sources)
        ),
        Step::Rule { name, sources } => format!(
            "命题「{proposition}」由规则「{}」推出，其谓词「{predicate}」被声明为风险题材「{theme}」\
             （声明 `{declaration}`）；{}",
            escape_control(name),
            sources_text(sources)
        ),
        Step::Interpretation { id, sources } => format!(
            "命题「{proposition}」由解释「{}」推出，其谓词「{predicate}」被声明为风险题材「{theme}」\
             （声明 `{declaration}`）；{}",
            escape_control(id),
            sources_text(sources)
        ),
        Step::Axiom { name, sources } => format!(
            "命题「{proposition}」由全称公理「{}」实例化推出，其谓词「{predicate}」被声明为风险题材「{theme}」\
             （声明 `{declaration}`）；{}",
            escape_control(name),
            sources_text(sources)
        ),
        Step::Gap { is_root } => {
            let what = if *is_root { "目标" } else { "缺口" };
            format!(
                "{what}「{proposition}」未获证明，其谓词「{predicate}」被声明为风险题材「{theme}」\
                 （声明 `{declaration}`）"
            )
        }
    }
}

/// The recorded sources of a step, or an explicit statement that there are none.
fn sources_text(sources: &[Source]) -> String {
    if sources.is_empty() {
        return "出处：证书未记录来源".to_owned();
    }
    let cited = sources
        .iter()
        .map(Source::one_line)
        .collect::<Vec<_>>()
        .join("、");
    format!("出处：{cited}")
}

/// The themed predicate a proposition states, if its kernel head is marked.
///
/// The proposition is normalized first, so a `def` alias that unfolds to a
/// themed predicate's application is recognized as the same predicate. A head
/// that is not a constant is not a declared predicate and is never themed.
fn themed_head(
    env: &Env,
    proposition: &CertExpr,
    markers: &BTreeMap<Name, RiskTheme>,
) -> Result<Option<(Name, RiskTheme)>, String> {
    let expression = Expr::from(proposition);
    let normalized = normalize(env, &Ctx::new(), &expression).map_err(|error| {
        format!(
            "无法规范化「{}」以判定风险题材：{error}",
            print_expr(&expression)
        )
    })?;
    Ok(normalized
        .head_const()
        .and_then(|head| markers.get(&head).map(|theme| (head, *theme))))
}
