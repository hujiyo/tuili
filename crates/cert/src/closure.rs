//! A conservative over-approximation of what the environment's rules can
//! derive.
//!
//! [`crate::check`] must reject a rule step whose `unless` condition is not
//! proved by the certificate but *is* derivable from the environment. The
//! certificate can simply omit the blocker's node, so looking only at the
//! certificate's nodes and the environment's axioms is not enough.
//!
//! This module therefore computes a superset of the propositions the
//! environment's rules may derive. It starts from the certificate's
//! propositions and the environment's axioms, ignores `unless` conditions,
//! conflicts and priorities, and applies every environment rule until a fixed
//! point. This is the checker's own conservative evaluator, not a second
//! reasoner: it does not claim to be exactly the reasoner's semantics, and
//! its purpose is to refuse a false green, not to prove reachability.
//!
//! The superset has two layers:
//!
//! * [`Possible::facts`] are ground propositions the evaluable rules derive
//!   from the seeds by ordinary premise matching. Facts are stored
//!   eta-shortened and compared with a blocker by kernel conversion, so
//!   alpha- and eta-variants match.
//! * [`Possible::patterns`] are conclusion schemas. A rule that cannot be
//!   evaluated statically (it references a premise binder such as
//!   `premise h : ...`, or a premise applies a function parameter so that a
//!   concrete fact cannot be matched exactly) contributes its opened
//!   conclusion, which may carry the rule's parameters as `?` variables and
//!   any structure. Such a rule may still fire, so its conclusion cannot be
//!   cleared merely because it was not derived: `无辜 ?p` may block
//!   `无辜 张三` as well as `无辜 李四`, while `无辜 李四` blocks only
//!   `无辜 李四` and leaves `无辜 张三` clear.
//!
//! Patterns propagate through the statically evaluable rules to a fixed
//! point. For every such rule, every premise subterm and every stored
//! pattern, the premise subterm and the pattern are unified; a successful
//! unification instantiates the rule's conclusion, which becomes another
//! pattern. A conclusion reached this way stays a pattern even when it is
//! ground: it depends on an opaque rule, so it is only possible, not
//! established. A rule that is not evaluable needs no propagation: its own
//! conclusion schema is already the most general one.
//! Unification is first-order and capture-avoiding: a variable is bound only
//! to a closed term, and the most general unifier keeps every instance a
//! real premise could consume. Patterns and blockers are eta-shortened
//! before matching, and the substituted pattern is compared with the blocker
//! by kernel conversion, so alpha- and eta-variants do not slip through.
//!
//! A pattern variable in function position is not first-order: `?f` may be
//! `λ _. B`, so `?f 甲` can denote any proposition and first-order matching of
//! the syntactic function part would miss its instances. The whole
//! application is therefore represented as one variable. Under a binder the
//! argument may mention the bound variable, so no top-level variable can
//! stand for the result; that conclusion becomes one wildcard, which matches
//! every blocker. Both replacements only make the pattern larger, never
//! smaller. A premise that needs the same widening makes its rule not
//! statically evaluable: the reasoner's raw fact may still match the
//! unnormalized application, so the rule contributes its conclusion schema
//! instead of a fact.
//!
//! Iteration, fact and pattern counts and matching work are bounded;
//! exceeding a bound is an error, never an empty result.

use std::collections::btree_map::Entry;
use std::collections::BTreeMap;

use std_deduce_kernel::env::{DeclKind, Env, RuleDecl};
use std_deduce_kernel::norm::normalize;
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::term::{free_vars, is_closed, shift, Expr};
use std_deduce_kernel::{conv::convertible, Ctx};

use crate::check::{mentioned_premise_binder, premise_binder_names};
use crate::key::expression_key;

/// The fixed-point iteration bound. A monotone closure of `n` facts settles in
/// at most `n` productive rounds; this bound exists so a bug cannot loop.
const MAX_ROUNDS: usize = 1000;
/// The fact bound. A larger closure is not useful to a certificate check.
const MAX_FACTS: usize = 10_000;
/// The pattern bound. Pattern propagation may instantiate a rule with an
/// ever-growing term, so it needs its own bound.
const MAX_PATTERNS: usize = 10_000;
/// The node bound for one stored fact or pattern. A pattern can double in size
/// each round without increasing the pattern count, so a separate size bound
/// is needed before normalization and key construction walk it.
const MAX_TERM_NODES: usize = 10_000;
/// The matching-work bound, counted in fact comparisons and unification
/// steps across one closure query.
const MAX_MATCH_ATTEMPTS: usize = 1_000_000;

/// The result of the conservative closure.
pub(crate) struct Possible {
    /// Ground propositions the evaluable rules derive from the seeds. A fact
    /// is matched against a blocker with kernel conversion, not by its printed
    /// form: alpha- and eta-variants are the same proposition.
    pub(crate) facts: Vec<Expr>,
    /// Conclusion schemas of rules that cannot be evaluated statically, and
    /// the conclusions reached by propagating them. A pattern may contain
    /// `?#n` variables and arbitrary structure. A blocker that matches a
    /// pattern cannot be cleared.
    pub(crate) patterns: Vec<Expr>,
}

/// Why the closure contains a blocker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PossibleMatch {
    /// An environment rule certainly derives the blocker from ground facts
    /// the certificate's own propositions and the environment's axioms
    /// establish.
    Fact,
    /// An environment rule that cannot be evaluated statically may derive
    /// the blocker. The blocker cannot be confirmed clear.
    Opaque,
}

/// Whether `proposition` is in the closure, and on which layer.
///
/// Facts are compared with [`convertible`]. For patterns the blocker is
/// eta-shortened, unified with the pattern, and the resulting instance is
/// compared with the original blocker by [`convertible`]. A negative answer
/// is only reported after every pattern has been tried; any conversion or
/// normalization failure is an error, never a non-match.
pub(crate) fn contains(
    env: &Env,
    possible: &Possible,
    proposition: &Expr,
) -> Result<Option<PossibleMatch>, String> {
    let mut attempts = 0usize;
    for fact in &possible.facts {
        charge_attempt(&mut attempts)?;
        if convertible(env, &Ctx::new(), fact, proposition)
            .map_err(|error| format!("无法判定阻断条件是否可能推出：{error}"))?
        {
            return Ok(Some(PossibleMatch::Fact));
        }
    }
    if possible.patterns.is_empty() {
        return Ok(None);
    }
    let target = eta_short(env, proposition)
        .map_err(|error| format!("无法判定阻断条件是否可能推出：{error}"))?;
    for pattern in &possible.patterns {
        let mut binding = BTreeMap::new();
        if unify(pattern, &target, &mut binding, &mut attempts)? {
            charge_attempt(&mut attempts)?;
            let instance = substitute(pattern, &binding);
            if is_ground(&instance)
                && convertible(env, &Ctx::new(), &instance, proposition).map_err(|error| {
                    format!("无法判定阻断条件是否可能由无法静态求值的规则推出：{error}")
                })?
            {
                return Ok(Some(PossibleMatch::Opaque));
            }
        }
    }
    Ok(None)
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
    let mut patterns: BTreeMap<String, Expr> = BTreeMap::new();
    for decl in env.iter() {
        let DeclKind::Rule(rule) = &decl.kind else {
            continue;
        };
        let opened = open_rule(env, &decl.name, rule)?;
        if opened.evaluable {
            rules.push(opened);
        } else {
            // An inexact rule cannot derive facts, but its conclusion is a
            // schema every ground instance of which may fire. The schema is
            // already the most general conclusion, so its premises are not
            // needed for propagation.
            insert_pattern(env, &mut patterns, &opened.conclusion)?;
        }
    }

    let mut attempts = 0usize;
    let mut rounds = 0usize;
    loop {
        let mut changed = false;

        // Ground closure: every evaluable rule whose premises are all facts.
        let mut derived: Vec<Expr> = Vec::new();
        for rule in &rules {
            let binding = BTreeMap::new();
            enumerate(rule, &facts, &binding, 0, &mut attempts, &mut derived)?;
        }
        for conclusion in derived {
            let normalized = normalize_fact(env, &conclusion)?;
            check_term_size(&normalized)?;
            if is_ground(&normalized) {
                let key = expression_key(&normalized);
                if let Entry::Vacant(entry) = facts.entry(key) {
                    entry.insert(normalized);
                    changed = true;
                    if facts.len() > MAX_FACTS {
                        return Err(fact_limit());
                    }
                }
            } else {
                // A full premise match should ground every parameter, since
                // the kernel requires each of them to occur in a premise. An
                // open conclusion is still a possible one and must not be
                // dropped.
                changed |= insert_pattern(env, &mut patterns, &normalized)?;
            }
        }

        // Pattern propagation. Every premise of every rule is tried as a
        // whole and at its nested subterms, so `中间 李四` also reaches a rule
        // whose premise is `可信 (中间 p)`. The sweep works on a snapshot;
        // conclusions added here are propagated in the next round, which
        // keeps the loop monotone.
        if !patterns.is_empty() {
            let current: Vec<Expr> = patterns.values().cloned().collect();
            for rule in &rules {
                for premise in &rule.premises {
                    let mut subterms = Vec::new();
                    collect_subterms(premise, true, &mut subterms);
                    for subterm in &subterms {
                        for pattern in &current {
                            let mut binding = BTreeMap::new();
                            if unify(pattern, subterm, &mut binding, &mut attempts)? {
                                let conclusion = substitute(&rule.conclusion, &binding);
                                changed |= insert_pattern(env, &mut patterns, &conclusion)?;
                            }
                        }
                    }
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

    let facts: Vec<Expr> = facts.into_values().collect();
    let patterns: Vec<Expr> = patterns.into_values().collect();
    Ok(Possible { facts, patterns })
}

/// The concrete predicate head of a proposition, if it has one.
///
/// A pattern variable (`?p`) is not a concrete head: the rule could conclude
/// any predicate through that parameter, so a blocker spelled with one cannot
/// be reasoned about by head. Blockers are closed, so this only guards
/// against a proposition shaped like a quantified formula or a lambda.
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

fn pattern_limit() -> String {
    format!("环境规则闭包超过 {MAX_PATTERNS} 条结论模式上限，无法确认阻断状态")
}

fn match_limit() -> String {
    format!("环境规则闭包的匹配尝试超过 {MAX_MATCH_ATTEMPTS} 次上限，无法确认阻断状态")
}

fn term_limit() -> String {
    format!("环境规则闭包的单条命题超过 {MAX_TERM_NODES} 个节点上限，无法确认阻断状态")
}

/// Charge one unit of matching work against the shared query budget.
fn charge_attempt(attempts: &mut usize) -> Result<(), String> {
    *attempts += 1;
    if *attempts > MAX_MATCH_ATTEMPTS {
        return Err(match_limit());
    }
    Ok(())
}

/// Reject a fact or pattern whose expression tree is too large.
///
/// The bound is checked before canonicalization and key construction, so an
/// ever-growing propagation chain fails with an error instead of exhausting
/// memory or spending a long time in the key printer.
fn check_term_size(expression: &Expr) -> Result<(), String> {
    let mut nodes = 0usize;
    if count_nodes(expression, &mut nodes) {
        Ok(())
    } else {
        Err(term_limit())
    }
}

fn count_nodes(expression: &Expr, nodes: &mut usize) -> bool {
    *nodes += 1;
    if *nodes > MAX_TERM_NODES {
        return false;
    }
    match expression {
        Expr::Sort(_) | Expr::Var(_) | Expr::Const(_) => true,
        Expr::Pi {
            domain, codomain, ..
        } => count_nodes(domain, nodes) && count_nodes(codomain, nodes),
        Expr::Lam { domain, body, .. } => count_nodes(domain, nodes) && count_nodes(body, nodes),
        Expr::App { func, arg } => count_nodes(func, nodes) && count_nodes(arg, nodes),
        Expr::Let { value, body, .. } => count_nodes(value, nodes) && count_nodes(body, nodes),
    }
}

/// Normalize a proposition and eta-contract it.
///
/// Kernel conversion treats `λ x, f x` and `f` as the same term, so matching
/// two terms structurally after beta/delta/zeta normalization is not enough:
/// an eta-expanded argument would be missed. Eta-contraction gives a short
/// normal form, which makes alpha- and eta-variants structurally matchable.
fn eta_short(env: &Env, expression: &Expr) -> Result<Expr, String> {
    let normalized = normalize(env, &Ctx::new(), expression)
        .map_err(|error| format!("无法规范化命题「{}」：{error}", print_expr(expression)))?;
    Ok(eta_reduce(&normalized))
}

/// Bring a conclusion schema into the shape the matcher understands.
///
/// First `eta_short` gives a common normal form. Then every application whose
/// head is a pattern variable is replaced by a single fresh pattern variable
/// (`saturate_applied_variables`): a rule parameter of function type may be
/// instantiated by `λ _. B`, so such an application denotes *any* proposition
/// at that position, and first-order matching of the syntactic function part
/// would miss instances that need beta-reduction.
fn normalize_pattern(env: &Env, expression: &Expr) -> Result<Expr, String> {
    let normalized = eta_short(env, expression)?;
    Ok(saturate_applied_variables(&normalized))
}

/// Replace applied pattern variables with fresh pattern variables.
///
/// `?f 甲` is replaced by a single fresh variable: `f` may be `λ _. B`, so the
/// application can denote any proposition, which a first-order variable in a
/// non-applied position matches exactly. The same holds for a longer
/// application spine and for an application nested in another term, which is
/// replaced position by position.
///
/// Under a binder the application can depend on the bound variable: `?f x` is
/// `(λ y. y) x` and denotes `x`. A top-level pattern variable cannot denote a
/// term mentioning a binder, so such a conclusion is not matched structurally
/// at all; the whole schema becomes one wildcard variable, which matches every
/// blocker. That is deliberately coarse, but it only ever refuses more.
fn saturate_applied_variables(expression: &Expr) -> Expr {
    if applied_variable_under_binder(expression, 0) {
        return Expr::constant("?#any");
    }
    let mut fresh = 0usize;
    saturate_expression(expression, &mut fresh)
}

fn saturate_expression(expression: &Expr, fresh: &mut usize) -> Expr {
    match expression {
        Expr::App { .. } if applied_variable_head(expression).is_some() => {
            let replacement = format!("?#applied{fresh}");
            *fresh += 1;
            Expr::constant(replacement)
        }
        Expr::App { func, arg } => Expr::App {
            func: Box::new(saturate_expression(func, fresh)),
            arg: Box::new(saturate_expression(arg, fresh)),
        },
        Expr::Pi {
            name,
            domain,
            codomain,
        } => Expr::Pi {
            name: name.clone(),
            domain: Box::new(saturate_expression(domain, fresh)),
            codomain: Box::new(saturate_expression(codomain, fresh)),
        },
        Expr::Lam { name, domain, body } => Expr::Lam {
            name: name.clone(),
            domain: Box::new(saturate_expression(domain, fresh)),
            body: Box::new(saturate_expression(body, fresh)),
        },
        Expr::Let { name, value, body } => Expr::Let {
            name: name.clone(),
            value: Box::new(saturate_expression(value, fresh)),
            body: Box::new(saturate_expression(body, fresh)),
        },
        Expr::Sort(_) | Expr::Var(_) | Expr::Const(_) => expression.clone(),
    }
}

/// The variable at the head of an application spine, if there is one.
fn applied_variable_head(expression: &Expr) -> Option<&str> {
    let mut head = expression;
    while let Expr::App { func, .. } = head {
        head = func;
    }
    match head {
        Expr::Const(name) => name.strip_prefix('?'),
        _ => None,
    }
}

/// Does an application of a pattern variable occur under a binder?
fn applied_variable_under_binder(expression: &Expr, depth: usize) -> bool {
    match expression {
        Expr::App { func, arg } => {
            (depth > 0 && applied_variable_head(expression).is_some())
                || applied_variable_under_binder(func, depth)
                || applied_variable_under_binder(arg, depth)
        }
        Expr::Pi {
            domain, codomain, ..
        } => {
            applied_variable_under_binder(domain, depth)
                || applied_variable_under_binder(codomain, depth + 1)
        }
        Expr::Lam { domain, body, .. } => {
            applied_variable_under_binder(domain, depth)
                || applied_variable_under_binder(body, depth + 1)
        }
        Expr::Let { value, body, .. } => {
            applied_variable_under_binder(value, depth)
                || applied_variable_under_binder(body, depth + 1)
        }
        Expr::Sort(_) | Expr::Var(_) | Expr::Const(_) => false,
    }
}

/// Eta-contract `λ x, f x` when `x` does not occur in `f`.
///
/// The body is reduced first, so cascaded eta-redexes are removed too.
/// Substitutions in this module only ever bind a variable to a closed term,
/// so no binder of the schema can capture the removed variable.
fn eta_reduce(expression: &Expr) -> Expr {
    match expression {
        Expr::Sort(_) | Expr::Var(_) | Expr::Const(_) => expression.clone(),
        Expr::Pi {
            name,
            domain,
            codomain,
        } => Expr::Pi {
            name: name.clone(),
            domain: Box::new(eta_reduce(domain)),
            codomain: Box::new(eta_reduce(codomain)),
        },
        Expr::Lam { name, domain, body } => {
            let domain = eta_reduce(domain);
            let body = eta_reduce(body);
            if let Expr::App { func, arg } = &body {
                if matches!(arg.as_ref(), Expr::Var(0)) && !free_vars(func, 0).contains(&0) {
                    return shift(func, -1, 0);
                }
            }
            Expr::Lam {
                name: name.clone(),
                domain: Box::new(domain),
                body: Box::new(body),
            }
        }
        Expr::App { func, arg } => Expr::App {
            func: Box::new(eta_reduce(func)),
            arg: Box::new(eta_reduce(arg)),
        },
        Expr::Let { name, value, body } => Expr::Let {
            name: name.clone(),
            value: Box::new(eta_reduce(value)),
            body: Box::new(eta_reduce(body)),
        },
    }
}

fn normalize_fact(env: &Env, fact: &Expr) -> Result<Expr, String> {
    eta_short(env, fact)
        .map_err(|error| format!("保守闭包无法规范化命题「{}」：{error}", print_expr(fact)))
}

fn insert_fact(
    env: &Env,
    facts: &mut BTreeMap<String, Expr>,
    expression: &Expr,
) -> Result<(), String> {
    let normalized = normalize_fact(env, expression)?;
    check_term_size(&normalized)?;
    facts
        .entry(expression_key(&normalized))
        .or_insert(normalized);
    Ok(())
}

/// Insert a conclusion schema, deduplicated up to variable renaming and
/// binder names.
///
/// Patterns are stored in a canonical shape: every `?` variable is renamed by
/// first occurrence to `?#0`, `?#1`, ... and binder names are erased, since
/// neither a variable name nor a binder name changes what the pattern can
/// match. The `#` keeps pattern variables apart from the kernel's opened rule
/// parameters (`?p`), so unification can treat both as independent variables.
/// Returns whether a new pattern was inserted.
fn insert_pattern(
    env: &Env,
    patterns: &mut BTreeMap<String, Expr>,
    expression: &Expr,
) -> Result<bool, String> {
    let normalized = normalize_pattern(env, expression)?;
    check_term_size(&normalized)?;
    let canonical = canonicalize(&normalized);
    let key = expression_key(&canonical);
    if !patterns.contains_key(&key) && patterns.len() >= MAX_PATTERNS {
        return Err(pattern_limit());
    }
    Ok(patterns.insert(key, canonical).is_none())
}

/// Rename `?` variables by first occurrence and erase binder names.
fn canonicalize(expression: &Expr) -> Expr {
    let mut variables: BTreeMap<String, String> = BTreeMap::new();
    canonicalize_with(expression, &mut variables)
}

fn canonicalize_with(expression: &Expr, variables: &mut BTreeMap<String, String>) -> Expr {
    match expression {
        Expr::Sort(_) | Expr::Var(_) => expression.clone(),
        Expr::Const(constant) => match constant.strip_prefix('?') {
            Some(parameter) => {
                let next = variables.len();
                let fresh = variables
                    .entry(parameter.to_owned())
                    .or_insert_with(|| format!("?#{next}"));
                Expr::constant(fresh)
            }
            None => expression.clone(),
        },
        Expr::Pi {
            domain, codomain, ..
        } => Expr::Pi {
            name: None,
            domain: Box::new(canonicalize_with(domain, variables)),
            codomain: Box::new(canonicalize_with(codomain, variables)),
        },
        Expr::Lam { domain, body, .. } => Expr::Lam {
            name: None,
            domain: Box::new(canonicalize_with(domain, variables)),
            body: Box::new(canonicalize_with(body, variables)),
        },
        Expr::App { func, arg } => Expr::App {
            func: Box::new(canonicalize_with(func, variables)),
            arg: Box::new(canonicalize_with(arg, variables)),
        },
        Expr::Let { value, body, .. } => Expr::Let {
            name: None,
            value: Box::new(canonicalize_with(value, variables)),
            body: Box::new(canonicalize_with(body, variables)),
        },
    }
}

struct OpenedRule {
    /// Opened, normalized and eta-shortened premise patterns. A premise that
    /// applied-variable saturation had to widen is stored widened as well.
    premises: Vec<Expr>,
    /// Opened, normalized and eta-shortened conclusion pattern.
    conclusion: Expr,
    /// Whether the closure may use this rule to derive facts and to propagate
    /// patterns. False when the rule references a premise binder, or when a
    /// premise had to be widened because it applies a function parameter:
    /// such a rule's premise cannot be matched to a concrete fact exactly, so
    /// only its conclusion schema is used.
    evaluable: bool,
}

fn open_rule(env: &Env, name: &str, rule: &RuleDecl) -> Result<OpenedRule, String> {
    let mut evaluable = !mentions_premise_binder(rule);
    // A normalization failure is an error even for an opaque rule. Skipping
    // the rule would drop its conclusion and could hide an opaque blocker
    // behind it.
    let mut premises = Vec::with_capacity(rule.premises.len());
    for i in 0..rule.premises.len() {
        let opened = rule.open_premise(i);
        let part = format!("第 {} 个前提", i + 1);
        let normalized = normalize_rule_part(env, name, &opened, &part)?;
        let reduced = eta_reduce(&normalized);
        let saturated = saturate_applied_variables(&reduced);
        if saturated != reduced {
            // The reasoner may match an unnormalized application of a lambda
            // against the raw premise, and the normalized fact can lose that
            // application structure. A rule whose premise applies a function
            // parameter therefore cannot be matched against concrete facts
            // exactly; its conclusion schema is used instead.
            evaluable = false;
        }
        premises.push(saturated);
    }
    let opened = rule.open_conclusion();
    let normalized = normalize_rule_part(env, name, &opened, "结论")?;
    Ok(OpenedRule {
        premises,
        conclusion: eta_reduce(&normalized),
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

/// Enumerate every complete premise match and collect the conclusion.
///
/// This is ground matching against `facts`: a `?parameter` constant is bound
/// to the corresponding subterm of a fact.
fn enumerate(
    rule: &OpenedRule,
    facts: &BTreeMap<String, Expr>,
    binding: &BTreeMap<String, Expr>,
    index: usize,
    attempts: &mut usize,
    derived: &mut Vec<Expr>,
) -> Result<(), String> {
    if index == rule.premises.len() {
        derived.push(substitute(&rule.conclusion, binding));
        return Ok(());
    }

    for fact in facts.values() {
        let mut next = binding.clone();
        if unify(&rule.premises[index], fact, &mut next, attempts)? {
            enumerate(rule, facts, &next, index + 1, attempts, derived)?;
        }
    }
    Ok(())
}

/// Collect the subterms a pattern may be unified with.
///
/// The whole premise is always included. Nested subterms are included so a
/// pattern such as `中间 李四` reaches the `p` inside a premise `可信 (中间 p)`.
/// A nested bare variable is skipped: it would let any pattern instantiate the
/// rule's parameter on its own, without the surrounding structure, which is
/// neither needed to cover a real derivation nor precise. A subterm that
/// mentions a de Bruijn variable bound outside it is skipped as well: a
/// pattern variable may not be bound to such a term.
///
/// Subterms are eta-contracted like the stored patterns. A pattern that was
/// eta-contracted must still meet a premise whose argument is the expanded
/// form; unifying the two without a common short normal form would miss a
/// derivation, and a missed derivation is a false green.
fn collect_subterms(expression: &Expr, root: bool, out: &mut Vec<Expr>) {
    if !root && matches!(expression, Expr::Const(_) | Expr::Var(_)) {
        return;
    }
    if is_closed(expression) {
        out.push(eta_reduce(expression));
    }
    match expression {
        Expr::Sort(_) | Expr::Var(_) | Expr::Const(_) => {}
        Expr::Pi {
            domain, codomain, ..
        } => {
            collect_subterms(domain, false, out);
            collect_subterms(codomain, false, out);
        }
        Expr::Lam { domain, body, .. } => {
            collect_subterms(domain, false, out);
            collect_subterms(body, false, out);
        }
        Expr::App { func, arg } => {
            collect_subterms(func, false, out);
            collect_subterms(arg, false, out);
        }
        Expr::Let { value, body, .. } => {
            collect_subterms(value, false, out);
            collect_subterms(body, false, out);
        }
    }
}

/// First-order unification of two opened patterns over `?` variables.
///
/// A variable is only bound to a closed term. Rule parameters are instantiated
/// by closed certificate bindings, so a value that mentions a binder of the
/// expression is a capture, not an instance; refusing it keeps the matcher
/// from inventing a blocker. The unifier is complete for the patterns the
/// closure builds: every ground premise that is an instance of both sides is
/// an instance of the returned substitution.
fn unify(
    left: &Expr,
    right: &Expr,
    binding: &mut BTreeMap<String, Expr>,
    attempts: &mut usize,
) -> Result<bool, String> {
    *attempts += 1;
    if *attempts > MAX_MATCH_ATTEMPTS {
        return Err(match_limit());
    }
    let left = resolve(left, binding);
    let right = resolve(right, binding);
    if let Expr::Const(left_name) = &left {
        if let Some(left_var) = left_name.strip_prefix('?') {
            if let Expr::Const(right_name) = &right {
                if right_name.strip_prefix('?') == Some(left_var) {
                    return Ok(true);
                }
            }
            return bind_variable(left_var, &right, binding);
        }
    }
    if let Expr::Const(right_name) = &right {
        if let Some(right_var) = right_name.strip_prefix('?') {
            return bind_variable(right_var, &left, binding);
        }
    }
    match (&left, &right) {
        (Expr::Const(left), Expr::Const(right)) => Ok(left == right),
        (Expr::Sort(left), Expr::Sort(right)) => Ok(left == right),
        (Expr::Var(left), Expr::Var(right)) => Ok(left == right),
        (
            Expr::App {
                func: left_func,
                arg: left_arg,
            },
            Expr::App {
                func: right_func,
                arg: right_arg,
            },
        ) => Ok(unify(left_func, right_func, binding, attempts)?
            && unify(left_arg, right_arg, binding, attempts)?),
        (
            Expr::Pi {
                domain: left_domain,
                codomain: left_codomain,
                ..
            },
            Expr::Pi {
                domain: right_domain,
                codomain: right_codomain,
                ..
            },
        ) => Ok(unify(left_domain, right_domain, binding, attempts)?
            && unify(left_codomain, right_codomain, binding, attempts)?),
        (
            Expr::Lam {
                domain: left_domain,
                body: left_body,
                ..
            },
            Expr::Lam {
                domain: right_domain,
                body: right_body,
                ..
            },
        ) => Ok(unify(left_domain, right_domain, binding, attempts)?
            && unify(left_body, right_body, binding, attempts)?),
        (
            Expr::Let {
                value: left_value,
                body: left_body,
                ..
            },
            Expr::Let {
                value: right_value,
                body: right_body,
                ..
            },
        ) => Ok(unify(left_value, right_value, binding, attempts)?
            && unify(left_body, right_body, binding, attempts)?),
        _ => Ok(false),
    }
}

/// Follow a top-level variable binding.
fn resolve(expression: &Expr, binding: &BTreeMap<String, Expr>) -> Expr {
    let mut current = expression.clone();
    while let Expr::Const(constant) = &current {
        let Some(variable) = constant.strip_prefix('?') else {
            break;
        };
        let Some(value) = binding.get(variable) else {
            break;
        };
        current = value.clone();
    }
    current
}

/// Bind an unbound variable, keeping every stored binding fully applied.
fn bind_variable(
    variable: &str,
    value: &Expr,
    binding: &mut BTreeMap<String, Expr>,
) -> Result<bool, String> {
    let value = substitute(value, binding);
    if !is_closed(&value) || mentions_variable(&value, variable) {
        return Ok(false);
    }
    let mut composition = BTreeMap::new();
    composition.insert(variable.to_owned(), value.clone());
    for bound in binding.values_mut() {
        *bound = substitute(bound, &composition);
    }
    binding.insert(variable.to_owned(), value);
    Ok(true)
}

/// Does the expression contain the `?variable` constant anywhere?
fn mentions_variable(expression: &Expr, variable: &str) -> bool {
    match expression {
        Expr::Const(constant) => constant.strip_prefix('?') == Some(variable),
        Expr::Sort(_) | Expr::Var(_) => false,
        Expr::Pi {
            domain, codomain, ..
        } => mentions_variable(domain, variable) || mentions_variable(codomain, variable),
        Expr::Lam { domain, body, .. } => {
            mentions_variable(domain, variable) || mentions_variable(body, variable)
        }
        Expr::App { func, arg } => {
            mentions_variable(func, variable) || mentions_variable(arg, variable)
        }
        Expr::Let { value, body, .. } => {
            mentions_variable(value, variable) || mentions_variable(body, variable)
        }
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
