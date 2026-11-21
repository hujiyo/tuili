//! Independent checking of certificates against an environment.
//!
//! [`check`] rebuilds every rule application from the rule declaration, the
//! recorded parameter bindings and the cited premise nodes. It depends on the
//! kernel only: it does not use the reasoner, its search state or its
//! derivation type.
//!
//! ## What is checked
//!
//! * Every assumption node cites an existing assumption whose proposition is
//!   a proposition.
//! * Every rule application names a rule, cites exactly as many premises as
//!   the rule has and cites them in the rule's own order, and cites only
//!   earlier nodes.
//! * The bindings name only rule parameters, bind each parameter exactly once
//!   and are closed terms.
//! * Instantiating the rule's premises with those bindings yields exactly the
//!   propositions of the cited nodes; instantiating the conclusion yields
//!   exactly the node's conclusion.
//! * No instantiated `unless` condition is proved anywhere in the
//!   certificate, and none holds as a proposition asserted by an environment
//!   axiom. The check is against all proved propositions, not only the ones
//!   reached from the root: a blocker proved in another branch, or declared
//!   by an `axiom` whose declared type is a proposition, retracts the step
//!   too. Every assumption in the certificate's table counts, whether or not
//!   a node cites it, and must itself be a proposition. Propositions are
//!   compared by kernel definitional equality, so alpha- and eta-variants of
//!   a proved blocker retract the step as well.
//! * No instantiated `unless` condition is derivable from the environment's
//!   rules when the certificate merely omits its derivation. The checker
//!   computes a conservative fixed-point superset of the propositions the
//!   environment's rules can derive, ignoring `unless`, conflicts and
//!   priorities. The superset has two layers. Ground facts are the
//!   conclusions of the statically evaluable rules. Conclusion patterns come
//!   from rules that cannot be evaluated statically (for example one that
//!   references a premise binder), and propagate through every rule premise
//!   until a fixed point. A blocker in that superset but not among the proved
//!   propositions rejects the step: a fact match says the environment can
//!   derive the blocker without the certificate showing the derivation, a
//!   pattern match says the blocker cannot be confirmed clear. Both
//!   comparisons use kernel conversion, and pattern matching is followed by
//!   conversion too, so alpha- and eta-variants match. The closure is
//!   computed only when a rule step that Pass 2 rebuilds has an `unless`. A
//!   blocker with no extractable predicate head is rejected as well.
//!   Exceeding the closure's bounds is an error, never a pass.
//! * A rule whose opened premises, conclusion or `unless` conditions mention a
//!   premise binder (`premise h : ...` referenced as `?h`) is rejected:
//!   dependent premises are not supported, and a checker that left `?h`
//!   uninstantiated would silently miss the condition.
//!
//! The derivability superset is not a second reasoner and does not claim the
//! reasoner's exact semantics; it is deliberately larger. It may therefore
//! reject a step whose blocker has a counter-argument elsewhere in the
//! environment. That is the intended direction: refuse a false green rather
//! than certify an omitted blocker.
//!
//! A [`Node::Gap`] proves nothing, so it cannot be a premise. It may be the
//! root; the report then says `root_proved = false`.
//!
//! ## Root and conflicts
//!
//! `root_proved` means the root has a legal proof *under the assumptions the
//! certificate lists*; it is not an unconditional legal conclusion. A root
//! that is itself an assumption is still proved, but the report says so
//! (`root_is_assumption`) and gives the condition count (`assumption_count`).
//!
//! If the root proposition occurs in a recorded conflict, the check rejects an
//! unresolved conflict and a root on the losing side. A root on the winning
//! side is accepted and the report sets `conflict_resolved`. The priorities
//! behind `defeated_by` / `prefer` are *not* validated against the
//! environment: `priority_sources_checked` is always false in this layer, so a
//! resolved conflict must not be read as a checked priority source.
//!
//! ## What is not checked here
//!
//! Sources and priorities are recorded by the certificate but are not
//! compared with the environment. Open obligations do not fail the check; they
//! set `requires_human`. Conflicts that do not involve the root are preserved
//! but not adjudicated here. Those are side conditions of a later layer.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use std_deduce_kernel::conv::convertible;
use std_deduce_kernel::env::{DeclKind, RuleDecl};
use std_deduce_kernel::norm::normalize;
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::term::is_closed;
use std_deduce_kernel::{check as kernel_check, Ctx, Env, Expr};

use crate::closure;
use crate::expr::CertExpr;
use crate::key::expression_key;
use crate::model::{Certificate, Node, NodeId, Resolution, Side};

/// The result of a successful certificate check.
///
/// The report does not claim that the root is an unconditional legal
/// conclusion. `root_proved` means the root has a legal proof *under the
/// assumptions the certificate lists*; `assumption_count` and
/// `root_is_assumption` make that conditionality visible.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckReport {
    /// Whether the root node has a legal proof under the certificate's
    /// assumptions. False when the root is a gap or when the certificate has
    /// no root. A root that is an assumption is still proved: the proof is the
    /// assumption itself, and `root_is_assumption` reports that.
    pub root_proved: bool,
    /// Whether the root node is an assumption node, i.e. the conclusion is
    /// assumed rather than derived by a rule.
    pub root_is_assumption: bool,
    /// The number of assumptions in the certificate's assumption table.
    /// `root_proved` is relative to all of them: every listed assumption is in
    /// scope whether or not a node cites it.
    pub assumption_count: usize,
    /// Whether the root proposition takes part in a recorded conflict and is
    /// on the winning side. The priority behind that resolution is not
    /// validated here; see `priority_sources_checked`.
    pub conflict_resolved: bool,
    /// Whether the certificate records open obligations, which need a human
    /// decision. They do not make the check fail.
    pub requires_human: bool,
    /// Whether the priority sources recorded with defeated conflicts were
    /// validated against the environment. Always false in this layer: a
    /// resolution is reported, not its priority provenance.
    pub priority_sources_checked: bool,
    /// How many nodes were validated. Every node is checked, not only those
    /// reachable from the root.
    pub nodes_checked: usize,
}

/// A certificate check failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckError {
    /// The offending node, when the failure belongs to one.
    pub node: Option<NodeId>,
    /// The failed criterion, including the values that were compared.
    pub message: String,
}

impl CheckError {
    fn at(node: NodeId, message: impl Into<String>) -> Self {
        CheckError {
            node: Some(node),
            message: message.into(),
        }
    }
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.node {
            Some(node) => write!(f, "节点 {node}：{}", self.message),
            None => f.write_str(&self.message),
        }
    }
}

impl std::error::Error for CheckError {}

/// Check that every node of `cert` is a legal step against `env`.
///
/// See the module documentation for the checked criteria and the boundaries.
pub fn check(env: &Env, cert: &Certificate) -> Result<CheckReport, CheckError> {
    if let Some(root) = cert.root {
        if root >= cert.nodes.len() {
            return Err(CheckError::at(
                root,
                format!("根节点索引越界：证书只有 {} 个节点", cert.nodes.len()),
            ));
        }
    }

    // Pass 1: every node that proves something must prove a proposition, and
    // its proposition is collected for the `unless` check. Gaps prove
    // nothing, so they contribute nothing here.
    let mut proved: BTreeMap<String, Expr> = BTreeMap::new();
    for (id, node) in cert.nodes.iter().enumerate() {
        let (what, proposition) = match node {
            Node::Assumption { assumption } => {
                let Some(entry) = cert.assumptions.get(*assumption) else {
                    return Err(CheckError::at(
                        id,
                        format!(
                            "引用了不存在的假设 {assumption}：证书只有 {} 条假设",
                            cert.assumptions.len()
                        ),
                    ));
                };
                ("假设", Expr::from(&entry.proposition))
            }
            Node::RuleApplication { conclusion, .. } => ("结论", Expr::from(conclusion)),
            Node::Gap { .. } => continue,
        };
        kernel_check::check(env, &Ctx::new(), &proposition, &Expr::Sort(0))
            .map_err(|e| CheckError::at(id, format!("{what}不是命题：{e}")))?;
        proved.insert(
            key(env, &proposition).map_err(|m| CheckError::at(id, m))?,
            proposition,
        );
    }

    // Every listed assumption is part of the context the root is proved
    // relative to, whether or not a node cites it. An unused blocker
    // assumption must still retract the step, and an unused assumption must
    // still be a proposition rather than an arbitrary term.
    for (index, entry) in cert.assumptions.iter().enumerate() {
        let proposition = Expr::from(&entry.proposition);
        kernel_check::check(env, &Ctx::new(), &proposition, &Expr::Sort(0)).map_err(|error| {
            CheckError {
                node: None,
                message: format!("第 {} 条假设不是命题：{error}", index + 1),
            }
        })?;
        let fact_key = key(env, &proposition).map_err(|message| CheckError {
            node: None,
            message: format!("第 {} 条假设：{message}", index + 1),
        })?;
        proved.insert(fact_key, proposition);
    }

    // A proposition asserted by an environment axiom is known whether or not
    // the certificate carries a node for it. Without this, a trimmed
    // certificate could drop the blocker's own node and pass.
    for (fact_key, proposition) in environment_propositions(env)? {
        proved.insert(fact_key, proposition);
    }

    // The closure is only needed when a rule step that Pass 2 will rebuild
    // actually has an `unless`. Scanning first avoids its cost — and its
    // bounds — for a certificate that never consults a blocker. Unknown
    // rules and non-rule declarations are still rejected by Pass 2 below.
    let needs_closure = cert.nodes.iter().any(|node| node_has_unless(env, node));
    // Ignoring `unless`, conflicts and priorities gives a superset of what the
    // environment may prove. A blocker in that superset but not in `proved`
    // is derivable without the certificate showing the derivation, so the
    // step must not pass.
    let possible = if needs_closure {
        Some(
            closure::possible(env, proved.values()).map_err(|message| CheckError {
                node: None,
                message,
            })?,
        )
    } else {
        None
    };

    // Pass 2: rebuild each rule application from its own evidence.
    for (id, node) in cert.nodes.iter().enumerate() {
        let Node::RuleApplication {
            rule,
            conclusion,
            premises,
            bindings,
            ..
        } = node
        else {
            continue;
        };

        let decl = env
            .get(rule)
            .ok_or_else(|| CheckError::at(id, format!("未知规则 `{rule}`")))?;
        let DeclKind::Rule(r) = &decl.kind else {
            return Err(CheckError::at(id, format!("`{rule}` 不是规则")));
        };

        if premises.len() != r.premises.len() {
            return Err(CheckError::at(
                id,
                format!(
                    "规则 `{rule}` 有 {} 个前提，本步引用了 {} 个节点",
                    r.premises.len(),
                    premises.len()
                ),
            ));
        }
        for premise in premises {
            if *premise >= cert.nodes.len() {
                return Err(CheckError::at(
                    id,
                    format!(
                        "前提节点索引 {premise} 越界：证书只有 {} 个节点",
                        cert.nodes.len()
                    ),
                ));
            }
            if *premise >= id {
                return Err(CheckError::at(
                    id,
                    format!("前提 {premise} 必须是当前节点之前的节点"),
                ));
            }
        }

        let mut binding: BTreeMap<&str, Expr> = BTreeMap::new();
        for entry in bindings {
            if !r
                .params
                .iter()
                .any(|(parameter, _)| parameter.as_ref() == entry.parameter)
            {
                return Err(CheckError::at(
                    id,
                    format!("绑定参数 `{}` 不是规则 `{rule}` 的参数", entry.parameter),
                ));
            }
            if binding.contains_key(entry.parameter.as_str()) {
                return Err(CheckError::at(
                    id,
                    format!("参数 `{}` 被重复绑定", entry.parameter),
                ));
            }
            let value = Expr::from(&entry.value);
            if !is_closed(&value) {
                return Err(CheckError::at(
                    id,
                    format!("参数 `{}` 的绑定值不是闭合项", entry.parameter),
                ));
            }
            binding.insert(entry.parameter.as_str(), value);
        }
        for (parameter, _) in &r.params {
            if !binding.contains_key(parameter.as_ref()) {
                return Err(CheckError::at(
                    id,
                    format!("参数 `{parameter}` 没有绑定；本步不是规则 `{rule}` 的完整实例"),
                ));
            }
        }

        // Only parameters are instantiated by `bindings`. A `?name` constant
        // belonging to a premise binder would be left open; comparing it with
        // the cited node would produce a misleading mismatch, and checking it
        // as a blocker would never match, silently letting the step through.
        let premise_binders = premise_binder_names(r);
        if !premise_binders.is_empty() {
            for (i, _) in r.premises.iter().enumerate() {
                if let Some(binder) = mentioned_premise_binder(&r.open_premise(i), &premise_binders)
                {
                    return Err(CheckError::at(
                        id,
                        format!(
                            "规则 `{rule}` 的第 {} 个前提依赖前提绑定 `?{binder}`：依赖前提暂不支持",
                            i + 1
                        ),
                    ));
                }
            }
            for (i, unless) in r.unlesses.iter().enumerate() {
                if let Some(binder) =
                    mentioned_premise_binder(&r.open_unless_text(unless), &premise_binders)
                {
                    return Err(CheckError::at(
                        id,
                        format!(
                            "规则 `{rule}` 的第 {} 个 unless 依赖前提绑定 `?{binder}`：依赖前提暂不支持",
                            i + 1
                        ),
                    ));
                }
            }
            if let Some(binder) = mentioned_premise_binder(&r.open_conclusion(), &premise_binders) {
                return Err(CheckError::at(
                    id,
                    format!("规则 `{rule}` 的结论依赖前提绑定 `?{binder}`：依赖前提暂不支持"),
                ));
            }
        }

        for (i, premise) in premises.iter().enumerate() {
            let proof = node_prop(cert, &cert.nodes[*premise]).ok_or_else(|| {
                CheckError::at(id, format!("前提 {premise} 是未闭合的缺口，不能充当前提"))
            })?;
            let actual = Expr::from(proof);
            let expected = close_pattern(&r.open_premise(i), &binding);
            let expected_key = key(env, &expected).map_err(|m| CheckError::at(id, m))?;
            let actual_key = key(env, &actual).map_err(|m| CheckError::at(id, m))?;
            if expected_key != actual_key {
                return Err(CheckError::at(
                    id,
                    format!(
                        "规则 `{rule}` 的第 {} 个前提实例是 `{}`，而引用的节点 {premise} 证明的是 `{}`",
                        i + 1,
                        print_expr(&expected),
                        print_expr(&actual)
                    ),
                ));
            }
        }

        let actual = Expr::from(conclusion);
        let expected = close_pattern(&r.open_conclusion(), &binding);
        let expected_key = key(env, &expected).map_err(|m| CheckError::at(id, m))?;
        let actual_key = key(env, &actual).map_err(|m| CheckError::at(id, m))?;
        if expected_key != actual_key {
            return Err(CheckError::at(
                id,
                format!(
                    "绑定确立的实例结论是 `{}`，而本步写的是 `{}`",
                    print_expr(&expected),
                    print_expr(&actual)
                ),
            ));
        }

        for unless in &r.unlesses {
            let closed = close_pattern(&r.open_unless_text(unless), &binding);
            if proved_contains(env, &proved, &closed)
                .map_err(|message| CheckError::at(id, message))?
            {
                return Err(CheckError::at(
                    id,
                    format!(
                        "规则 `{rule}` 的阻断条件「{}」已成立，本步不该成立",
                        print_expr(&closed)
                    ),
                ));
            }
            let Some(possible) = possible.as_ref() else {
                // The pre-scan computes the closure for every rule step with
                // an `unless`; reaching this point without it would be an
                // internal inconsistency, not a clean pass.
                return Err(CheckError::at(
                    id,
                    format!("规则 `{rule}` 有阻断条件，但环境闭包没有计算：内部检查状态不一致"),
                ));
            };
            match closure::contains(env, possible, &closed)
                .map_err(|message| CheckError::at(id, message))?
            {
                Some(closure::PossibleMatch::Fact) => {
                    return Err(CheckError::at(
                        id,
                        format!(
                            "规则 `{rule}` 的阻断条件「{}」可能由环境规则推出，但证书没有给出它的推导；\
                             请补 blocker 证明，或缩小规则/环境",
                            print_expr(&closed)
                        ),
                    ));
                }
                Some(closure::PossibleMatch::Opaque) => {
                    return Err(CheckError::at(
                        id,
                        format!(
                            "规则 `{rule}` 的阻断条件「{}」无法确认阻断状态：\
                             环境中有无法静态求值的规则可能推出该阻断条件",
                            print_expr(&closed)
                        ),
                    ));
                }
                None => {}
            }
            if closure::concrete_head(env, &closed)
                .map_err(|m| CheckError::at(id, m))?
                .is_none()
            {
                return Err(CheckError::at(
                    id,
                    format!(
                        "规则 `{rule}`：阻断条件没有可提取的谓词头，无法确认阻断状态（「{}」）",
                        print_expr(&closed)
                    ),
                ));
            }
        }
    }

    let root_proved = cert
        .root
        .is_some_and(|root| node_prop(cert, &cert.nodes[root]).is_some());
    let root_is_assumption = cert
        .root
        .is_some_and(|root| matches!(&cert.nodes[root], Node::Assumption { .. }));
    let conflict_resolved = match cert.root {
        Some(root) => match node_prop(cert, &cert.nodes[root]) {
            Some(proposition) => root_conflict_resolved(env, cert, root, proposition)?,
            None => false,
        },
        None => false,
    };
    Ok(CheckReport {
        root_proved,
        root_is_assumption,
        assumption_count: cert.assumptions.len(),
        conflict_resolved,
        requires_human: !cert.open_obligations.is_empty(),
        priority_sources_checked: false,
        nodes_checked: cert.nodes.len(),
    })
}

/// Check the root proposition against the certificate's recorded conflicts.
///
/// An unresolved conflict, or one where the root is on the losing side, makes
/// the certificate invalid. A root on the winning side is allowed and returns
/// `true`. This does not validate the priority behind a defeat; the caller
/// reports that through `priority_sources_checked = false`.
fn root_conflict_resolved(
    env: &Env,
    cert: &Certificate,
    root: NodeId,
    proposition: &CertExpr,
) -> Result<bool, CheckError> {
    let root_key = key(env, &Expr::from(proposition)).map_err(|m| CheckError::at(root, m))?;
    let mut resolved = false;
    for (index, conflict) in cert.conflicts.iter().enumerate() {
        let left = key(env, &Expr::from(&conflict.left)).map_err(|m| CheckError::at(root, m))?;
        let right = key(env, &Expr::from(&conflict.right)).map_err(|m| CheckError::at(root, m))?;
        let side = if left == root_key {
            Side::Left
        } else if right == root_key {
            Side::Right
        } else {
            continue;
        };
        match &conflict.resolution {
            Resolution::Unresolved => {
                return Err(CheckError::at(
                    root,
                    format!(
                        "根命题「{}」处于第 {} 个冲突的未决状态，不能作为结论",
                        print_expr(&Expr::from(proposition)),
                        index + 1
                    ),
                ));
            }
            Resolution::Defeated { winner } if winner != &side => {
                return Err(CheckError::at(
                    root,
                    format!(
                        "根命题「{}」在第 {} 个冲突中位于败方，不能作为结论",
                        print_expr(&Expr::from(proposition)),
                        index + 1
                    ),
                ));
            }
            Resolution::Defeated { .. } => resolved = true,
        }
    }
    Ok(resolved)
}

/// Every environment axiom whose declared type is a proposition, keyed by its
/// normalized form.
///
/// `axiom h : 侵占 张三` asserts the proposition `侵占 张三`; a declaration
/// whose declared type is not a proposition (`axiom 假 : Prop`) only names a
/// proposition constant and is skipped. The kernel's inference decides the
/// sort; the name is never guessed at.
fn environment_propositions(env: &Env) -> Result<BTreeMap<String, Expr>, CheckError> {
    let mut facts = BTreeMap::new();
    for decl in env.iter() {
        if !matches!(decl.kind, DeclKind::Axiom) {
            continue;
        }
        let declared_sort = kernel_check::infer(env, &Ctx::new(), &decl.ty)
            .and_then(|ty| normalize(env, &Ctx::new(), &ty))
            .map_err(|error| CheckError {
                node: None,
                message: format!("环境公理 `{}` 的类型无法检查：{error}", decl.name),
            })?;
        if declared_sort != Expr::Sort(0) {
            continue;
        }
        let proposition = normalize(env, &Ctx::new(), &decl.ty).map_err(|error| CheckError {
            node: None,
            message: format!("环境公理 `{}` 无法规范化，无法比较：{error}", decl.name),
        })?;
        facts.insert(expression_key(&proposition), proposition);
    }
    Ok(facts)
}

/// Does this node rebuild a rule step that has at least one `unless`?
///
/// Unknown rules and non-rule declarations return false here and are rejected
/// by Pass 2 with their own diagnostics. This scan decides whether the
/// conservative closure is needed at all.
fn node_has_unless(env: &Env, node: &Node) -> bool {
    let Node::RuleApplication { rule, .. } = node else {
        return false;
    };
    let Some(decl) = env.get(rule) else {
        return false;
    };
    matches!(&decl.kind, DeclKind::Rule(rule) if !rule.unlesses.is_empty())
}

/// Whether `proposition` is already proved, up to kernel conversion.
///
/// The normalized printed key is an exact fast path. Alpha- or eta-equivalent
/// facts have different printed keys, so a miss falls back to
/// [`convertible`]. A conversion error is a failed check, never a non-match.
fn proved_contains(
    env: &Env,
    proved: &BTreeMap<String, Expr>,
    proposition: &Expr,
) -> Result<bool, String> {
    let exact = key(env, proposition)?;
    if proved.contains_key(&exact) {
        return Ok(true);
    }
    for fact in proved.values() {
        if convertible(env, &Ctx::new(), fact, proposition)
            .map_err(|error| format!("无法判定阻断条件是否已成立：{error}"))?
        {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The names of a rule's premise binders, as opened to `?name`.
///
/// Parameters are excluded: they are instantiated from the certificate's
/// `bindings`. Unnamed premises get the same generated `_p{i}` name the kernel
/// uses, so a reference to it is detected as well.
pub(crate) fn premise_binder_names(rule: &RuleDecl) -> BTreeSet<String> {
    let params: BTreeSet<&str> = rule.params.iter().map(|(name, _)| name.as_ref()).collect();
    rule.binder_names()
        .into_iter()
        .skip(rule.params.len())
        .map(|name| name.to_string())
        .filter(|name| !params.contains(name.as_str()))
        .collect()
}

/// The first premise binder an opened pattern mentions, if any.
pub(crate) fn mentioned_premise_binder(
    pattern: &Expr,
    premise_binders: &BTreeSet<String>,
) -> Option<String> {
    match pattern {
        Expr::Const(name) => name
            .strip_prefix('?')
            .filter(|binder| premise_binders.contains(*binder))
            .map(str::to_owned),
        Expr::Sort(_) | Expr::Var(_) => None,
        Expr::Pi {
            domain, codomain, ..
        } => mentioned_premise_binder(domain, premise_binders)
            .or_else(|| mentioned_premise_binder(codomain, premise_binders)),
        Expr::Lam { domain, body, .. } => mentioned_premise_binder(domain, premise_binders)
            .or_else(|| mentioned_premise_binder(body, premise_binders)),
        Expr::App { func, arg } => mentioned_premise_binder(func, premise_binders)
            .or_else(|| mentioned_premise_binder(arg, premise_binders)),
        Expr::Let { value, body, .. } => mentioned_premise_binder(value, premise_binders)
            .or_else(|| mentioned_premise_binder(body, premise_binders)),
    }
}

/// The proposition a node proves, if it proves one.
fn node_prop<'a>(cert: &'a Certificate, node: &'a Node) -> Option<&'a CertExpr> {
    match node {
        Node::Assumption { assumption } => cert
            .assumptions
            .get(*assumption)
            .map(|entry| &entry.proposition),
        Node::RuleApplication { conclusion, .. } => Some(conclusion),
        Node::Gap { .. } => None,
    }
}

/// Substitute the `?parameter` constants of an opened rule expression.
///
/// Rule declarations are opened by the kernel with `?<binder>` constants for
/// the variables in scope (see [`std_deduce_kernel::env::RuleDecl`]). Only
/// parameters have bindings. A constant that is not a bound parameter is left
/// alone; the caller rejects premise binders before reaching this function,
/// and any other mismatch is caught by the ordinary proposition comparison.
fn close_pattern(pattern: &Expr, binding: &BTreeMap<&str, Expr>) -> Expr {
    match pattern {
        Expr::Const(n) => match n.strip_prefix('?') {
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
            domain: Box::new(close_pattern(domain, binding)),
            codomain: Box::new(close_pattern(codomain, binding)),
        },
        Expr::Lam { name, domain, body } => Expr::Lam {
            name: name.clone(),
            domain: Box::new(close_pattern(domain, binding)),
            body: Box::new(close_pattern(body, binding)),
        },
        Expr::App { func, arg } => Expr::App {
            func: Box::new(close_pattern(func, binding)),
            arg: Box::new(close_pattern(arg, binding)),
        },
        Expr::Let { name, value, body } => Expr::Let {
            name: name.clone(),
            value: Box::new(close_pattern(value, binding)),
            body: Box::new(close_pattern(body, binding)),
        },
    }
}

/// A comparison key that is stable under kernel definitional unfolding.
pub(crate) fn key(env: &Env, expression: &Expr) -> Result<String, String> {
    normalize(env, &Ctx::new(), expression)
        .map(|normalized| expression_key(&normalized))
        .map_err(|error| format!("规范化命题失败，无法比较：{error}"))
}
