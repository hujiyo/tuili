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

/// One theme that applies, with the evidence lines that produced it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RiskReport {
    themes: Vec<RiskTheme>,
    evidence: Vec<(RiskTheme, Vec<String>)>,
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
    if markers.is_empty() {
        return Ok(RiskReport {
            themes: Vec::new(),
            evidence: Vec::new(),
        });
    }

    let Some(root) = certificate.root else {
        return Ok(RiskReport {
            themes: Vec::new(),
            evidence: Vec::new(),
        });
    };

    let mut visited = vec![false; certificate.nodes.len()];
    let mut pending: Vec<NodeId> = vec![root];
    let mut lines: BTreeMap<RiskTheme, BTreeSet<String>> = BTreeMap::new();
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
        let Some(head) = themed_head(env, proposition, &markers)? else {
            continue;
        };
        let (pred, theme) = head;
        let line = evidence_line(proposition, &pred, theme, &step);
        lines.entry(theme).or_default().insert(line);
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
    Ok(RiskReport { themes, evidence })
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
