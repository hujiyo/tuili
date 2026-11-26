//! Candidate interpretations for an open-concept-obstructed outcome.
//!
//! An `open` marker makes a predicate a concept a human has to interpret. The
//! certificate layer turns a proof that states such a concept into one
//! `open_concept` obligation (`::std_deduce_cert::open_concept_dependency`),
//! and the command layer prints `此处需人判断：…`. This module answers the next
//! question: which of the **declared** interpretations relate to the concept
//! that is in the way, and which of those can actually be run?
//!
//! ## What counts as a candidate
//!
//! The candidate set is never guessed or generated: it is enumerated from the
//! loaded environment's `interpret` declarations only. A declared
//! interpretation is a candidate when its `to` relates, in the kernel's
//! sense, to one of the blocked open-concept propositions:
//!
//! * **exact** — `to` is kernel-equivalent to the blocked proposition (up to
//!   beta / `def` / zeta and eta), so enabling it licenses exactly that
//!   conclusion or premise;
//! * **same head** — `to` normalizes to an application of the same predicate
//!   with the same number of arguments, but is a different proposition of the
//!   same open concept (for example another individual). Enabling it does not
//!   license the blocked proposition; the branch report shows that outcome
//!   rather than hiding it.
//!
//! Only the `to` side is compared. An interpretation whose `from` matches the
//! blocked proposition while its `to` does not reads the concept as something
//! else — the direction is the opposite of what the blocked conclusion needs,
//! so it is not a candidate and is not listed. The comparison normalizes both
//! sides (beta, `def` delta, zeta) and compares constants by name, never the
//! printed form.
//!
//! ## Usable and unavailable
//!
//! A related interpretation is usable only when its `from` already holds in
//! the fact set the interpretation stage reads: registered facts and rule
//! conclusions, without any interpretation application. A related
//! interpretation whose `from` does not hold cannot license anything in this
//! case; it is reported as unavailable with the reason instead of being
//! silently dropped. A related interpretation whose `to` is kernel-equivalent
//! to the `to` of an interpretation the session already enabled cannot be
//! enabled beside it (the reasoner refuses two enabled interpretations with
//! indistinguishable conclusions); it is likewise unavailable, naming the
//! enabled declaration.
//!
//! ## Bounds and determinism
//!
//! Every relevant interpretation is collected in declaration-id order, so the
//! report does not depend on load order. At most [`MAX_BRANCH_CANDIDATES`]
//! usable candidates are offered, and the same bound applies to the
//! unavailable list; everything beyond a bound is listed by id as truncated.
//! The branches themselves are run one interpretation at a time — this module
//! never enumerates a combination of interpretations.

use std_deduce_kernel::conv::convertible;
use std_deduce_kernel::norm::normalize;
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{Ctx, Env, Expr, Name};

use crate::{GapTree, Reasoner};

/// The maximum number of interpretation branches one report runs.
///
/// One interpretation at a time, never a combination: a legal reading is a
/// single explicit choice, and N interpretations would already be 2^N
/// combinations if they were combined. The bound keeps a report reproducible
/// and readable; the omitted branches are always named.
pub const MAX_BRANCH_CANDIDATES: usize = 8;

/// How a candidate's `to` relates to the blocked open-concept proposition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CandidateRelation {
    /// `to` is kernel-equivalent to the blocked proposition.
    Exact,
    /// `to` applies the same predicate with the same arity, but states a
    /// different proposition of the same open concept.
    SameHead,
}

impl CandidateRelation {
    /// The Chinese label the command layer prints.
    pub fn label_zh(self) -> &'static str {
        match self {
            CandidateRelation::Exact => "内核等价",
            CandidateRelation::SameHead => "同谓词",
        }
    }
}

/// One declared interpretation whose `to` relates to a blocked open concept.
#[derive(Debug, Clone, PartialEq)]
pub struct BranchCandidate {
    /// The declaration's id.
    pub id: Name,
    /// The proposition the interpretation consumes.
    pub from: Expr,
    /// The proposition it licenses.
    pub to: Expr,
    /// The blocked open-concept proposition the `to` relates to.
    pub blocked: Expr,
    /// How the two relate (exact versus same predicate head).
    pub relation: CandidateRelation,
}

/// A related interpretation that cannot be run as a branch, with the reason.
#[derive(Debug, Clone, PartialEq)]
pub struct UnavailableBranch {
    pub candidate: BranchCandidate,
    /// Why enabling it cannot produce a different branch here.
    pub reason: String,
}

/// The interpretations related to the blocked open concepts.
///
/// `candidates` are the usable ones, `unavailable` the related ones that
/// cannot be enabled; both are sorted by id and truncated to
/// [`MAX_BRANCH_CANDIDATES`]. `truncated` and `unavailable_truncated` name what
/// the bounds left out, so a reader never mistakes a built-in bound for
/// "there are no more declarations".
#[derive(Debug, Clone, PartialEq)]
pub struct BranchCandidateScan {
    /// The blocked open-concept propositions, deduplicated by structural key
    /// and sorted, so the report is stable. Only propositions whose head
    /// really is an `open` concept are kept.
    pub blocked: Vec<Expr>,
    /// Usable candidates, sorted by id.
    pub candidates: Vec<BranchCandidate>,
    /// Usable candidates the bound left out, sorted by id.
    pub truncated: Vec<Name>,
    /// Related but unusable interpretations, sorted by id.
    pub unavailable: Vec<UnavailableBranch>,
    /// Unusable interpretations the bound left out, sorted by id.
    pub unavailable_truncated: Vec<Name>,
}

impl BranchCandidateScan {
    /// Whether the scan found no related interpretation at all.
    pub fn is_empty(&self) -> bool {
        self.candidates.is_empty() && self.unavailable.is_empty()
    }
}

impl Reasoner<'_> {
    /// Every proposition on a gap tree whose predicate head is an `open`
    /// concept, deduplicated by structural key and sorted.
    ///
    /// The tree is the reasoner's own recursion, so this names exactly where a
    /// rules-only derivation is blocked by a concept a human has to interpret;
    /// a proved conclusion never appears on a gap tree.
    pub fn open_concept_goals(&self, tree: &GapTree) -> Result<Vec<Expr>, String> {
        let mut out: Vec<Expr> = Vec::new();
        let mut seen: Vec<String> = Vec::new();
        let mut pending: Vec<&GapTree> = vec![tree];
        while let Some(node) = pending.pop() {
            if is_open_head(self.env(), &node.goal)? {
                let key = self.key_of(&node.goal);
                if !seen.contains(&key) {
                    seen.push(key);
                    out.push(node.goal.clone());
                }
            }
            for rule in &node.candidates {
                for premise in &rule.missing {
                    if let Some(gap) = &premise.gap {
                        pending.push(gap);
                    }
                }
            }
        }
        out.sort_by_key(|goal| self.key_of(goal));
        Ok(out)
    }

    /// The interpretations related to the blocked open concepts, and which of
    /// them can be run as one-interpretation branches.
    ///
    /// Call this after [`Reasoner::saturate`]: the availability check reads
    /// the settled rule-visible fact set. A reasoner without a settled fact
    /// base is an error, not an empty candidate set.
    pub fn branch_candidates(&self, blocked: &[Expr]) -> Result<BranchCandidateScan, String> {
        let Some(fixed) = &self.fixed else {
            return Err(
                "推理器尚未完成饱和：候选解释的 from 需要在解释应用前的事实集上判定，请先 saturate"
                    .to_owned(),
            );
        };

        // One stable, deduplicated blocked list. The relation is decided in
        // this order, so a `to` matching several propositions reports the
        // first by structural key.
        let mut blocked_list: Vec<Expr> = Vec::new();
        let mut seen: Vec<String> = Vec::new();
        for proposition in blocked {
            let key = self.key_of(proposition);
            if !seen.contains(&key) {
                seen.push(key);
                blocked_list.push(proposition.clone());
            }
        }
        blocked_list.sort_by_key(|proposition| self.key_of(proposition));

        // Only propositions whose head really is an open concept can anchor a
        // candidate; anything else would let an unrelated interpretation in
        // through a caller bug.
        let mut open_blocked: Vec<Expr> = Vec::new();
        for proposition in blocked_list {
            if is_open_head(self.env(), &proposition)? {
                open_blocked.push(proposition);
            }
        }

        let enabled = self.enabled_interpretations();
        let records = self.interpretation_records();
        let mut candidates: Vec<BranchCandidate> = Vec::new();
        let mut unavailable: Vec<UnavailableBranch> = Vec::new();
        for record in &records {
            if enabled.contains(&record.id) {
                // The session already enabled it: it is part of the baseline,
                // not a branch of its own.
                continue;
            }
            let Some((relation, blocked_proposition)) =
                relate(self.env(), &record.to, &open_blocked)?
            else {
                continue;
            };
            let candidate = BranchCandidate {
                id: record.id.clone(),
                from: record.from.clone(),
                to: record.to.clone(),
                blocked: blocked_proposition,
                relation,
            };
            if !self.holds(&fixed.rule_facts, &candidate.from)? {
                unavailable.push(UnavailableBranch {
                    candidate,
                    reason: "from 在解释应用前的事实集（已登记事实与规则结论）里不成立".to_owned(),
                });
                continue;
            }
            if let Some(collision) =
                equivalent_enabled_to(self.env(), &enabled, &records, &candidate.to)?
            {
                unavailable.push(UnavailableBranch {
                    candidate,
                    reason: format!(
                        "to 与已启用的解释 `{collision}` 在内核下等价，两者不能同时启用"
                    ),
                });
                continue;
            }
            candidates.push(candidate);
        }

        let mut truncated: Vec<Name> = Vec::new();
        if candidates.len() > MAX_BRANCH_CANDIDATES {
            truncated = candidates
                .split_off(MAX_BRANCH_CANDIDATES)
                .into_iter()
                .map(|candidate| candidate.id)
                .collect();
        }
        let mut unavailable_truncated: Vec<Name> = Vec::new();
        if unavailable.len() > MAX_BRANCH_CANDIDATES {
            unavailable_truncated = unavailable
                .split_off(MAX_BRANCH_CANDIDATES)
                .into_iter()
                .map(|entry| entry.candidate.id)
                .collect();
        }
        Ok(BranchCandidateScan {
            blocked: open_blocked,
            candidates,
            truncated,
            unavailable,
            unavailable_truncated,
        })
    }
}

/// Whether a proposition states an `open` concept, in the kernel's sense.
///
/// The proposition is normalized first, so a `def` alias that unfolds to an
/// open predicate is recognized. A head that is not a constant (a bound
/// variable, a quantified form, a sort) is never read as an open concept.
fn is_open_head(env: &Env, proposition: &Expr) -> Result<bool, String> {
    let normalized = normalize(env, &Ctx::new(), proposition).map_err(|error| {
        format!(
            "无法规范化「{}」以判定开放概念：{error}",
            print_expr(proposition)
        )
    })?;
    let open = env.open_predicates();
    Ok(normalized.head_const().is_some_and(|head| {
        open.iter()
            .any(|predicate| predicate.as_ref() == head.as_ref())
    }))
}

/// The first blocked proposition a `to` relates to, if any.
///
/// `None` means the interpretation is not about the blocked concept. A `to`
/// that is equivalent to the blocked proposition is exact; a `to` whose
/// normalized head and arity match its head states the same concept about
/// something else.
fn relate(
    env: &Env,
    to: &Expr,
    blocked: &[Expr],
) -> Result<Option<(CandidateRelation, Expr)>, String> {
    let normalized_to = normalize(env, &Ctx::new(), to)
        .map_err(|error| format!("无法规范化解释的 to「{}」：{error}", print_expr(to)))?;
    for proposition in blocked {
        if convertible(env, &Ctx::new(), to, proposition).map_err(|error| {
            format!(
                "无法判定解释的 to「{}」与受阻命题「{}」是否内核等价：{error}",
                print_expr(to),
                print_expr(proposition)
            )
        })? {
            return Ok(Some((CandidateRelation::Exact, proposition.clone())));
        }
        let normalized_blocked = normalize(env, &Ctx::new(), proposition).map_err(|error| {
            format!("无法规范化受阻命题「{}」：{error}", print_expr(proposition))
        })?;
        if let (Some(left), Some(right)) = (
            head_and_arity(&normalized_to),
            head_and_arity(&normalized_blocked),
        ) {
            if left == right {
                return Ok(Some((CandidateRelation::SameHead, proposition.clone())));
            }
        }
    }
    Ok(None)
}

/// The already enabled interpretation whose `to` is kernel-equivalent to
/// `to`, if any.
fn equivalent_enabled_to(
    env: &Env,
    enabled: &[Name],
    records: &[crate::InterpretationRecord],
    to: &Expr,
) -> Result<Option<Name>, String> {
    for record in records {
        if !enabled.contains(&record.id) {
            continue;
        }
        let same = key(env, &record.to) == key(env, to)
            || convertible(env, &Ctx::new(), &record.to, to)
                .map_err(|error| format!("无法判定解释的 to 是否与已启用解释等价：{error}"))?;
        if same {
            return Ok(Some(record.id.clone()));
        }
    }
    Ok(None)
}

/// The constant head and argument count of an application.
fn head_and_arity(expression: &Expr) -> Option<(Name, usize)> {
    let mut arity = 0usize;
    let mut current = expression;
    while let Expr::App { func, .. } = current {
        arity += 1;
        current = func;
    }
    match current {
        Expr::Const(name) => Some((name.clone(), arity)),
        _ => None,
    }
}

/// The structural key of an expression, with the environment's definitions
/// unfolded. `:branches` deduplicates and sorts by the same key the reasoner
/// uses, so the report order never depends on traversal order.
fn key(env: &Env, expression: &Expr) -> String {
    crate::key(env, expression)
}
