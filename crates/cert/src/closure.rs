//! A conservative over-approximation of what the environment's rules can
//! derive.
//!
//! [`crate::check`] must reject a rule step whose `unless` condition is not
//! proved by the certificate but *is* derivable from the environment. The
//! certificate can simply omit the blocker's node, so looking only at the
//! certificate's nodes and the environment's axioms is not enough.
//!
//! This module therefore computes a superset of the ground propositions the
//! environment's rules can derive. It starts from the certificate's
//! propositions and the environment's axioms, ignores `unless` conditions,
//! conflicts and priorities, and applies every environment rule until a fixed
//! point. This is the checker's own conservative evaluator, not a second
//! reasoner: it does not claim to be exactly the reasoner's semantics, and
//! its purpose is to refuse a false green, not to prove reachability.
//!
//! A rule that cannot be evaluated statically (it references a premise binder
//! such as `premise h : ...`, or its conclusion's predicate head cannot be
//! extracted) contributes that head to [`Possible::opaque_heads`]; when not
//! even the head can be extracted, the whole closure is marked opaque
//! ([`Possible::opaque_any`]). Opaque heads then propagate through every rule
//! until a fixed point: if a premise mentions an opaque head anywhere, or its
//! head is a parameter that could match an opaque fact, the rule's conclusion
//! head is opaque too. Opaque rules stay in this graph with their normalized
//! premises and conclusion, even though they are not used to derive facts.
//! The caller rejects an unproved `unless` that touches an opaque head.
//! Iteration, fact count and matching work are bounded; exceeding a bound is
//! an error, never an empty result.

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};

use std_deduce_kernel::env::{DeclKind, Env, RuleDecl};
use std_deduce_kernel::norm::normalize;
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::term::{is_closed, Expr};
use std_deduce_kernel::Ctx;

use crate::check::{mentioned_premise_binder, premise_binder_names};

/// The fixed-point iteration bound. A monotone closure of `n` facts settles in
/// at most `n` productive rounds; this bound exists so a bug cannot loop.
const MAX_ROUNDS: usize = 1000;
/// The fact bound. A larger closure is not useful to a certificate check.
const MAX_FACTS: usize = 10_000;
/// The matching-work bound per round, counted in premise-to-fact attempts.
const MAX_MATCH_ATTEMPTS: usize = 1_000_000;

/// The result of the conservative closure.
pub(crate) struct Possible {
    /// Every proposition that may be derived, including the seeds. A fact is
    /// matched against a blocker with kernel conversion, not by its printed
    /// form: alpha- and eta-variants are the same proposition.
    pub(crate) facts: Vec<Expr>,
    /// Predicate heads that may appear on a blocker the checker cannot rule
    /// out: heads of rules whose conclusions could not be evaluated
    /// statically, plus heads propagated through evaluable rules that can
    /// consume an opaque fact. An unproved `unless` with one of these heads
    /// cannot be cleared.
    pub(crate) opaque_heads: BTreeSet<String>,
    /// Some rule's conclusion head could not be extracted. Any unproved
    /// `unless` cannot be cleared.
    pub(crate) opaque_any: bool,
}

/// Compute the closure seeded by `seeds`.
pub(crate) fn possible<'a>(
    env: &Env,
    seeds: impl IntoIterator<Item = &'a Expr>,
) -> Result<Possible, String> {
    let mut facts: BTreeMap<String, Expr> = BTreeMap::new();
    for seed in seeds {
        insert_fact(env, &mut facts, seed)?;
    }
    if facts.len() > MAX_FACTS {
        return Err(fact_limit());
    }

    let mut rules: Vec<OpenedRule> = Vec::new();
    let mut opaque_heads: BTreeSet<String> = BTreeSet::new();
    let mut opaque_any = false;
    for decl in env.iter() {
        let DeclKind::Rule(rule) = &decl.kind else {
            continue;
        };
        let opened = open_rule(env, &decl.name, rule)?;
        if !opened.evaluable {
            // An opaque rule cannot derive facts, but its conclusion head is
            // still a head the checker cannot rule out. It stays in `rules`
            // so its premises can relay opacity from other rules.
            match concrete_head(env, &opened.conclusion)? {
                Some(head) => {
                    opaque_heads.insert(head);
                }
                None => opaque_any = true,
            }
        }
        rules.push(opened);
    }
    propagate_opaque_heads(env, &rules, &mut opaque_heads, &mut opaque_any)?;

    let mut rounds = 0usize;
    loop {
        let mut derived: Vec<Expr> = Vec::new();
        let mut attempts = 0usize;
        for rule in rules.iter().filter(|rule| rule.evaluable) {
            let binding = BTreeMap::new();
            enumerate(
                env,
                rule,
                &facts,
                &binding,
                0,
                &mut attempts,
                &mut derived,
                &mut opaque_heads,
                &mut opaque_any,
            )?;
        }

        let mut changed = false;
        for fact in derived {
            let normalized = normalize_fact(env, &fact)?;
            let key = print_expr(&normalized);
            if let Entry::Vacant(entry) = facts.entry(key) {
                entry.insert(normalized);
                changed = true;
                if facts.len() > MAX_FACTS {
                    return Err(fact_limit());
                }
            }
        }
        if !changed {
            break;
        }
        rounds += 1;
        if rounds >= MAX_ROUNDS {
            return Err(format!(
                "环境规则闭包在 {MAX_ROUNDS} 轮内没有稳定，无法确认阻断状态"
            ));
        }
    }

    // A defensive evaluation may have exposed an opaque head while deriving
    // facts. Close the head set again so the caller always sees a fixed point.
    propagate_opaque_heads(env, &rules, &mut opaque_heads, &mut opaque_any)?;

    Ok(Possible {
        facts: facts.into_values().collect(),
        opaque_heads,
        opaque_any,
    })
}

/// Propagate opaque conclusion heads through all rules to a fixed point.
///
/// The graph includes opaque rules as well as evaluable ones: an opaque rule
/// can relay opacity from one head to another. A rule spreads opacity when
/// one of its premises can consume an opaque fact. Two spellings count:
///
/// * the premise mentions an opaque head anywhere, not only as its outer
///   head: `R (P x)` mentions `P` too;
/// * the premise's outer head is a parameter (`?p` / `?p x`), which can match
///   a fact of any head; this only matters while `opaque_heads` is non-empty.
///
/// The rule's conclusion head then becomes opaque. If that head cannot be
/// extracted, the whole closure becomes opaque. The loop is monotone: each
/// round only adds heads, so it terminates.
fn propagate_opaque_heads(
    env: &Env,
    rules: &[OpenedRule],
    opaque_heads: &mut BTreeSet<String>,
    opaque_any: &mut bool,
) -> Result<(), String> {
    loop {
        let mut changed = false;
        for rule in rules {
            let reaches_opaque = rule.premises.iter().any(|premise| {
                let parameter_head = !opaque_heads.is_empty()
                    && premise
                        .head_const()
                        .is_some_and(|head| head.starts_with('?'));
                parameter_head || mentions_opaque_head(premise, opaque_heads)
            });
            if !reaches_opaque {
                continue;
            }
            match concrete_head(env, &rule.conclusion)? {
                Some(head) => changed |= opaque_heads.insert(head),
                None => {
                    *opaque_any = true;
                    return Ok(());
                }
            }
        }
        if !changed {
            return Ok(());
        }
    }
}

/// Does the expression mention any constant in `opaque_heads`, at any depth?
fn mentions_opaque_head(expression: &Expr, opaque_heads: &BTreeSet<String>) -> bool {
    match expression {
        Expr::Const(name) => opaque_heads.contains(name.as_ref()),
        Expr::Sort(_) | Expr::Var(_) => false,
        Expr::Pi {
            domain, codomain, ..
        } => {
            mentions_opaque_head(domain, opaque_heads)
                || mentions_opaque_head(codomain, opaque_heads)
        }
        Expr::Lam { domain, body, .. } => {
            mentions_opaque_head(domain, opaque_heads) || mentions_opaque_head(body, opaque_heads)
        }
        Expr::App { func, arg } => {
            mentions_opaque_head(func, opaque_heads) || mentions_opaque_head(arg, opaque_heads)
        }
        Expr::Let { value, body, .. } => {
            mentions_opaque_head(value, opaque_heads) || mentions_opaque_head(body, opaque_heads)
        }
    }
}

/// The concrete predicate head of a proposition, if it has one.
///
/// A pattern variable (`?p`) is not a concrete head: the rule could conclude
/// any predicate through that parameter, so the caller must treat the rule as
/// fully opaque instead.
pub(crate) fn concrete_head(env: &Env, expression: &Expr) -> Result<Option<String>, String> {
    let normalized = normalize(env, &Ctx::new(), expression)
        .map_err(|error| format!("规范化命题失败，无法提取谓词头：{error}"))?;
    Ok(normalized
        .head_const()
        .map(|name| name.to_string())
        .filter(|name| !name.starts_with('?')))
}

fn fact_limit() -> String {
    format!("环境规则闭包超过 {MAX_FACTS} 条事实上限，无法确认阻断状态")
}

fn normalize_fact(env: &Env, fact: &Expr) -> Result<Expr, String> {
    normalize(env, &Ctx::new(), fact)
        .map_err(|error| format!("保守闭包无法规范化命题「{}」：{error}", print_expr(fact)))
}

fn insert_fact(
    env: &Env,
    facts: &mut BTreeMap<String, Expr>,
    expression: &Expr,
) -> Result<(), String> {
    let normalized = normalize_fact(env, expression)?;
    facts.entry(print_expr(&normalized)).or_insert(normalized);
    Ok(())
}

struct OpenedRule {
    /// Opened and normalized premise patterns.
    premises: Vec<Expr>,
    /// Opened and normalized conclusion pattern.
    conclusion: Expr,
    /// Whether the closure may use this rule to derive facts. A rule that
    /// mentions a premise binder cannot be evaluated statically; it stays in
    /// the propagation graph but not in the fact derivation.
    evaluable: bool,
}

fn open_rule(env: &Env, name: &str, rule: &RuleDecl) -> Result<OpenedRule, String> {
    let evaluable = !mentions_premise_binder(rule);
    // A normalization failure is an error even for an opaque rule. Skipping
    // the rule would drop it from the propagation graph and could hide an
    // opaque blocker behind it.
    let mut premises = Vec::with_capacity(rule.premises.len());
    for i in 0..rule.premises.len() {
        let opened = rule.open_premise(i);
        let part = format!("第 {} 个前提", i + 1);
        premises.push(normalize_rule_part(env, name, &opened, &part)?);
    }
    let opened = rule.open_conclusion();
    let conclusion = normalize_rule_part(env, name, &opened, "结论")?;
    Ok(OpenedRule {
        premises,
        conclusion,
        evaluable,
    })
}

/// Does the rule reference one of its own premise binders anywhere?
fn mentions_premise_binder(rule: &RuleDecl) -> bool {
    let binders = premise_binder_names(rule);
    if binders.is_empty() {
        return false;
    }
    let premise_uses = (0..rule.premises.len())
        .any(|i| mentioned_premise_binder(&rule.open_premise(i), &binders).is_some());
    let unless_uses = rule
        .unlesses
        .iter()
        .any(|unless| mentioned_premise_binder(&rule.open_unless_text(unless), &binders).is_some());
    let conclusion_uses = mentioned_premise_binder(&rule.open_conclusion(), &binders).is_some();
    premise_uses || unless_uses || conclusion_uses
}

fn normalize_rule_part(env: &Env, name: &str, opened: &Expr, part: &str) -> Result<Expr, String> {
    normalize(env, &Ctx::new(), opened)
        .map_err(|error| format!("规则 `{name}` 的{part}无法规范化，无法静态求值：{error}"))
}

/// Enumerate every complete premise match and derive its conclusion.
///
/// This is plain ground matching: facts are normalized and ground, so a
/// `?parameter` constant is bound to the corresponding subterm of a fact.
#[allow(clippy::too_many_arguments)]
fn enumerate(
    env: &Env,
    rule: &OpenedRule,
    facts: &BTreeMap<String, Expr>,
    binding: &BTreeMap<String, Expr>,
    index: usize,
    attempts: &mut usize,
    derived: &mut Vec<Expr>,
    opaque_heads: &mut BTreeSet<String>,
    opaque_any: &mut bool,
) -> Result<(), String> {
    if index == rule.premises.len() {
        let conclusion = substitute(&rule.conclusion, binding);
        if is_ground(&conclusion) {
            derived.push(conclusion);
        } else if let Some(head) = concrete_head(env, &conclusion)? {
            opaque_heads.insert(head);
        } else {
            *opaque_any = true;
        }
        return Ok(());
    }

    for fact in facts.values() {
        *attempts += 1;
        if *attempts > MAX_MATCH_ATTEMPTS {
            return Err(format!(
                "环境规则闭包的匹配尝试超过 {MAX_MATCH_ATTEMPTS} 次上限，无法确认阻断状态"
            ));
        }
        let mut next = binding.clone();
        if match_pattern(&rule.premises[index], fact, &mut next) {
            enumerate(
                env,
                rule,
                facts,
                &next,
                index + 1,
                attempts,
                derived,
                opaque_heads,
                opaque_any,
            )?;
        }
    }
    Ok(())
}

/// Is `pattern` (containing `?x` constants) matchable against ground `fact`?
///
/// This matcher belongs to the conservative checker evaluator. It is not a
/// second reasoner and does not promise the reasoner's exact semantics; a
/// missed match would be a false green, so it matches every structure it can.
fn match_pattern(pattern: &Expr, fact: &Expr, binding: &mut BTreeMap<String, Expr>) -> bool {
    match (pattern, fact) {
        (Expr::Const(name), _) => match name.strip_prefix('?') {
            Some(parameter) => match binding.get(parameter) {
                Some(bound) => bound == fact,
                None => {
                    binding.insert(parameter.to_owned(), fact.clone());
                    true
                }
            },
            None => matches!(fact, Expr::Const(other) if other == name),
        },
        (Expr::Sort(left), Expr::Sort(right)) => left == right,
        (Expr::Var(left), Expr::Var(right)) => left == right,
        (
            Expr::App {
                func: pattern_func,
                arg: pattern_arg,
            },
            Expr::App {
                func: fact_func,
                arg: fact_arg,
            },
        ) => {
            match_pattern(pattern_func, fact_func, binding)
                && match_pattern(pattern_arg, fact_arg, binding)
        }
        (
            Expr::Pi {
                domain: pattern_domain,
                codomain: pattern_codomain,
                ..
            },
            Expr::Pi {
                domain: fact_domain,
                codomain: fact_codomain,
                ..
            },
        ) => {
            match_pattern(pattern_domain, fact_domain, binding)
                && match_pattern(pattern_codomain, fact_codomain, binding)
        }
        (
            Expr::Lam {
                domain: pattern_domain,
                body: pattern_body,
                ..
            },
            Expr::Lam {
                domain: fact_domain,
                body: fact_body,
                ..
            },
        ) => {
            match_pattern(pattern_domain, fact_domain, binding)
                && match_pattern(pattern_body, fact_body, binding)
        }
        (
            Expr::Let {
                value: pattern_value,
                body: pattern_body,
                ..
            },
            Expr::Let {
                value: fact_value,
                body: fact_body,
                ..
            },
        ) => {
            match_pattern(pattern_value, fact_value, binding)
                && match_pattern(pattern_body, fact_body, binding)
        }
        _ => false,
    }
}

/// Substitute the `?parameter` constants of an opened pattern.
fn substitute(pattern: &Expr, binding: &BTreeMap<String, Expr>) -> Expr {
    match pattern {
        Expr::Const(name) => match name.strip_prefix('?') {
            Some(parameter) => binding
                .get(parameter)
                .cloned()
                .unwrap_or_else(|| pattern.clone()),
            None => pattern.clone(),
        },
        Expr::Sort(_) | Expr::Var(_) => pattern.clone(),
        Expr::Pi {
            name,
            domain,
            codomain,
        } => Expr::Pi {
            name: name.clone(),
            domain: Box::new(substitute(domain, binding)),
            codomain: Box::new(substitute(codomain, binding)),
        },
        Expr::Lam { name, domain, body } => Expr::Lam {
            name: name.clone(),
            domain: Box::new(substitute(domain, binding)),
            body: Box::new(substitute(body, binding)),
        },
        Expr::App { func, arg } => Expr::App {
            func: Box::new(substitute(func, binding)),
            arg: Box::new(substitute(arg, binding)),
        },
        Expr::Let { name, value, body } => Expr::Let {
            name: name.clone(),
            value: Box::new(substitute(value, binding)),
            body: Box::new(substitute(body, binding)),
        },
    }
}

/// A proposition with no free variable and no unbound `?parameter`.
fn is_ground(expression: &Expr) -> bool {
    is_closed(expression) && !mentions_pattern(expression)
}

fn mentions_pattern(expression: &Expr) -> bool {
    match expression {
        Expr::Const(name) => name.starts_with('?'),
        Expr::Sort(_) | Expr::Var(_) => false,
        Expr::Pi {
            domain, codomain, ..
        } => mentions_pattern(domain) || mentions_pattern(codomain),
        Expr::Lam { domain, body, .. } => mentions_pattern(domain) || mentions_pattern(body),
        Expr::App { func, arg } => mentions_pattern(func) || mentions_pattern(arg),
        Expr::Let { value, body, .. } => mentions_pattern(value) || mentions_pattern(body),
    }
}
