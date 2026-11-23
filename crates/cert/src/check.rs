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
//! * Every conflict's two propositions must be propositions, and every
//!   conflict resolution is validated against the declared priorities: the
//!   basis must be the strictness of an assumption or the environment's
//!   effective priority edges, an unusable priority must record exactly the
//!   declared edges between the sides, and an unresolved reason must match the
//!   provenances and the graph. The provenances themselves are checked first:
//!   a rule witness must be a rule of the environment that no other witness on
//!   the same side repeats, its conclusion head must agree with the conflict
//!   proposition when both heads are concrete, and an assumption side's
//!   proposition must occur in the certificate's assumption table. See "Root
//!   and conflicts" below.
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
//! side is accepted and the report sets `conflict_resolved`.
//!
//! Every recorded conflict resolution is validated against the environment's
//! declared priorities, not just the root's. Both conflict propositions must be
//! propositions, checked the same way as node propositions. Before the
//! resolution is read, each side's provenance is checked: a rule witness must
//! be an environment rule that no other witness on the same side repeats and
//! whose conclusion head agrees with the conflict proposition when both heads
//! are concrete; an assumption side's proposition must occur in the
//! certificate's assumption table. The checker rebuilds the priority graph from
//! the kernel declarations (top-level `priority` declarations plus rule-internal
//! `defeated_by` / `prefer` clauses of one package) and computes its strongly
//! connected components, so an edge on a cycle is known to be unusable. A
//! priority-based defeat must cite, for every winning-side x losing-side rule
//! pair, at least one edge that the environment really declares, with the same
//! direction, declaring module or rule, clause and sources in the same order;
//! every cited edge must be effective (not on a cycle); and the checker
//! recomputes that the winning side covers every pair and the losing side does
//! not. An unusable priority must list at least one and exactly the
//! environment's declared edges between the two sides (both directions, all
//! sources), and no side may fully cover the other. An assumption-based defeat
//! must name the assumption side as the winner, and both sides must not be
//! assumptions. An unresolved reason must match the provenances: both
//! assumption, a lost witness list with no assumption side, no declared edge at
//! all, or exactly the declared but unusable edges. The report's
//! `priority_sources_checked` says the edges recorded by the certificate
//! passed; it does not mean every priority in the environment was inspected,
//! and an order no conflict cites is never compared.
//!
//! ## What is not checked here
//!
//! The rule instances named by a conflict's `left_by` / `right_by` are not
//! re-derived: the certificate lists rule names, not instances, so the checker
//! verifies that each name is an environment rule, that no side repeats one,
//! that the rule's conclusion head agrees with the conflict proposition when
//! both are concrete, and that an assumption side's proposition is in the
//! certificate's assumption table, but a rule that can conclude that predicate
//! is trusted to be the actual instance. Conflicts the certificate omits are
//! not reconstructed, so a truncated certificate can hide a conflict; the
//! derivation layer is what records them. Citations are compared as data, and
//! their legal effect is not judged. Open obligations do not fail the check;
//! they set `requires_human`. Whether the root is proved depends only on the
//! conflicts the root takes part in; a conflict elsewhere is validated but does
//! not change `root_proved`.

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
use crate::model::{
    Certificate, Conflict, Node, NodeId, PriorityClause, PriorityEdge, PriorityOrigin, Provenance,
    Resolution, ResolutionBasis, Side, UnresolvedReason,
};
use crate::source::Source;

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
    /// on the winning side. The recorded resolution, including its priority
    /// edges, has been validated against the environment.
    pub conflict_resolved: bool,
    /// Whether the certificate records open obligations, which need a human
    /// decision. They do not make the check fail.
    pub requires_human: bool,
    /// Whether every priority edge recorded by a `Defeated` conflict with a
    /// priority basis was validated against the environment: each one must be
    /// a declaration the environment really makes, in the recorded direction
    /// and with the recorded origin and sources, and must not lie on a
    /// priority cycle. True when the certificate records no such conflict.
    ///
    /// This reports the *recorded* defeats, not every priority of the
    /// environment: an order that no conflict cites is not compared, so a
    /// true value does not mean the whole priority ledger was audited.
    pub priority_sources_checked: bool,
    /// How many priority edges were compared with the environment: every edge
    /// recorded by a priority-based defeat plus every edge recorded by an
    /// unusable priority.
    pub priority_edges_checked: usize,
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

    // Every recorded conflict resolution is validated independently of the
    // reasoner, against the priority graph rebuilt from the kernel ledger.
    // This happens before the root is judged so a forged resolution is
    // reported even when the root does not take part in it.
    let priority = PriorityGraph::from_env(env)?;
    let mut priority_edges_checked = 0;
    for (index, conflict) in cert.conflicts.iter().enumerate() {
        // A conflict records two propositions. Check them with the same
        // criterion as node propositions before reading what the record claims
        // about their provenances or resolution.
        for (label, proposition) in [("左", &conflict.left), ("右", &conflict.right)] {
            kernel_check::check(env, &Ctx::new(), &Expr::from(proposition), &Expr::Sort(0))
                .map_err(|error| CheckError {
                    node: None,
                    message: format!("第 {} 个冲突的{label}侧不是命题：{error}", index + 1),
                })?;
        }
        validate_provenance(env, cert, index, conflict)?;
        priority_edges_checked += validate_resolution(&priority, index, conflict)?;
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
        // Every recorded priority edge has just been validated; a failure
        // returned above. This is true even when there is no such edge.
        priority_sources_checked: true,
        priority_edges_checked,
        nodes_checked: cert.nodes.len(),
    })
}

/// Check the root proposition against the certificate's recorded conflicts.
///
/// An unresolved conflict, or one where the root is on the losing side, makes
/// the certificate invalid. A root on the winning side is allowed and returns
/// `true`. The resolution itself was already validated by
/// [`validate_resolution`], so a root that reaches this point is not relying on
/// a forged priority.
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
            Resolution::Unresolved { .. } => {
                return Err(CheckError::at(
                    root,
                    format!(
                        "根命题「{}」处于第 {} 个冲突的未决状态，不能作为结论",
                        print_expr(&Expr::from(proposition)),
                        index + 1
                    ),
                ));
            }
            Resolution::Defeated { winner, .. } if winner != &side => {
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

/// The environment's declared priority order, rebuilt from the kernel ledger.
///
/// This is the checker's own graph; it shares no code with the reasoner. Nodes
/// are the environment's rules, edges are top-level `priority` declarations
/// and rule-internal `defeated_by` / `prefer` clauses of one package.
struct PriorityGraph {
    /// Every rule name of the environment.
    rules: BTreeSet<String>,
    /// Declared edges, keyed by `(winner, loser)`.
    declared: BTreeMap<(String, String), Vec<PriorityEdge>>,
    /// Edges between different components, i.e. the ones that can decide a
    /// conflict. An edge inside a cycle can never decide anything.
    effective: BTreeMap<String, BTreeSet<String>>,
}

impl PriorityGraph {
    fn from_env(env: &Env) -> Result<Self, CheckError> {
        let rules: BTreeSet<String> = env
            .rules()
            .iter()
            .map(|decl| decl.name.to_string())
            .collect();
        let mut declared: BTreeMap<(String, String), Vec<PriorityEdge>> = BTreeMap::new();
        for priority in env.priorities() {
            // An order whose endpoint is not a declared rule cannot order a
            // derivation, so it is never one of the edges between two rules.
            if !rules.contains(priority.winner.as_ref()) || !rules.contains(priority.loser.as_ref())
            {
                continue;
            }
            insert_priority(
                &mut declared,
                PriorityEdge {
                    winner: priority.winner.to_string(),
                    loser: priority.loser.to_string(),
                    origin: PriorityOrigin::PriorityDeclaration {
                        declared_in: priority.declared_in.to_string(),
                        sources: priority.sources.iter().map(Source::from).collect(),
                    },
                },
            );
        }
        for decl in env.rules() {
            let DeclKind::Rule(rule) = &decl.kind else {
                continue;
            };
            for (clause, targets) in [
                (PriorityClause::DefeatedBy, &rule.exceptions),
                (PriorityClause::Prefer, &rule.prefers),
            ] {
                for target in targets {
                    let Some(target_decl) = env.get(target) else {
                        continue;
                    };
                    let DeclKind::Rule(target_rule) = &target_decl.kind else {
                        continue;
                    };
                    // The loader refuses a cross-package clause; a directly
                    // built environment must not hide one from this checker.
                    if target_rule.declared_in != rule.declared_in {
                        return Err(CheckError {
                            node: None,
                            message: format!(
                                "环境中的规则 `{}` 用 `{}` 指向另一个包 `{}` 的规则 `{}`；\
                                 跨包优先关系必须用顶层 priority 声明，规则内子句只用于同一包内",
                                decl.name,
                                clause_label(clause),
                                package_label(target_rule.declared_in.as_deref()),
                                target
                            ),
                        });
                    }
                    let (winner, loser) = match clause {
                        PriorityClause::DefeatedBy => (target.to_string(), decl.name.to_string()),
                        PriorityClause::Prefer => (decl.name.to_string(), target.to_string()),
                    };
                    insert_priority(
                        &mut declared,
                        PriorityEdge {
                            winner,
                            loser,
                            origin: PriorityOrigin::RuleClause {
                                declaring_rule: decl.name.to_string(),
                                clause,
                                rule_sources: decl.sources.iter().map(Source::from).collect(),
                            },
                        },
                    );
                }
            }
        }
        let mut adjacency: BTreeMap<String, Vec<String>> = rules
            .iter()
            .map(|name| (name.clone(), Vec::new()))
            .collect();
        for (winner, loser) in declared.keys() {
            if let Some(neighbors) = adjacency.get_mut(winner) {
                neighbors.push(loser.clone());
            }
        }
        for neighbors in adjacency.values_mut() {
            neighbors.sort();
            neighbors.dedup();
        }
        let scc = components(&adjacency);
        let mut effective: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (winner, losers) in &adjacency {
            for loser in losers {
                if scc.get(winner) != scc.get(loser) {
                    effective
                        .entry(winner.clone())
                        .or_default()
                        .insert(loser.clone());
                }
            }
        }
        Ok(PriorityGraph {
            rules,
            declared,
            effective,
        })
    }

    fn is_effective(&self, winner: &str, loser: &str) -> bool {
        self.effective
            .get(winner)
            .is_some_and(|beaten| beaten.contains(loser))
    }

    fn beats(&self, winners: &[String], losers: &[String]) -> bool {
        !winners.is_empty()
            && !losers.is_empty()
            && winners
                .iter()
                .all(|winner| losers.iter().all(|loser| self.is_effective(winner, loser)))
    }

    /// Every declared edge between the two sides in either direction.
    fn declared_between(&self, left: &[String], right: &[String]) -> Vec<PriorityEdge> {
        let mut edges = Vec::new();
        for (winners, losers) in [(left, right), (right, left)] {
            for winner in winners {
                for loser in losers {
                    if let Some(declared) = self.declared.get(&(winner.clone(), loser.clone())) {
                        edges.extend(declared.iter().cloned());
                    }
                }
            }
        }
        edges.sort_by_key(PriorityEdge::sort_key);
        edges
    }
}

fn insert_priority(
    declared: &mut BTreeMap<(String, String), Vec<PriorityEdge>>,
    edge: PriorityEdge,
) {
    declared
        .entry((edge.winner.clone(), edge.loser.clone()))
        .or_default()
        .push(edge);
}

fn clause_label(clause: PriorityClause) -> &'static str {
    match clause {
        PriorityClause::Prefer => "prefer",
        PriorityClause::DefeatedBy => "defeated_by",
    }
}

fn package_label(declared_in: Option<&str>) -> &str {
    declared_in.unwrap_or("无 namespace（案件/示例文件）")
}

/// Iterative Kosaraju over the priority graph. Nodes and neighbours are
/// ordered by name, so the component ids are reproducible.
fn components(adjacency: &BTreeMap<String, Vec<String>>) -> BTreeMap<String, u32> {
    let mut visited: BTreeSet<String> = BTreeSet::new();
    let mut finished: Vec<String> = Vec::new();
    for start in adjacency.keys() {
        if visited.contains(start) {
            continue;
        }
        visited.insert(start.clone());
        let mut stack: Vec<(String, usize)> = vec![(start.clone(), 0)];
        while let Some(top) = stack.last_mut() {
            let neighbors = adjacency.get(&top.0).map(Vec::as_slice).unwrap_or(&[]);
            if top.1 < neighbors.len() {
                let next = neighbors[top.1].clone();
                top.1 += 1;
                if visited.insert(next.clone()) {
                    stack.push((next, 0));
                }
            } else {
                let (node, _) = stack.pop().expect("the DFS stack is not empty");
                finished.push(node);
            }
        }
    }

    let mut reverse: BTreeMap<String, Vec<String>> = adjacency
        .keys()
        .map(|name| (name.clone(), Vec::new()))
        .collect();
    for (winner, losers) in adjacency {
        for loser in losers {
            if let Some(predecessors) = reverse.get_mut(loser) {
                predecessors.push(winner.clone());
            }
        }
    }
    for predecessors in reverse.values_mut() {
        predecessors.sort();
        predecessors.dedup();
    }

    let mut component: BTreeMap<String, u32> = BTreeMap::new();
    let mut next_component = 0u32;
    for start in finished.iter().rev() {
        if component.contains_key(start) {
            continue;
        }
        let id = next_component;
        next_component += 1;
        component.insert(start.clone(), id);
        let mut stack = vec![start.clone()];
        while let Some(node) = stack.pop() {
            let predecessors = reverse.get(&node).map(Vec::as_slice).unwrap_or(&[]);
            for predecessor in predecessors {
                if !component.contains_key(predecessor) {
                    component.insert(predecessor.clone(), id);
                    stack.push(predecessor.clone());
                }
            }
        }
    }
    component
}

/// Validate what a conflict's provenance claims, independently of how it was
/// resolved.
///
/// A hand-edited certificate can repeat a rule name on one side, name a rule
/// whose conclusion is a different predicate, or label a side as an assumption
/// that the certificate's assumption table does not list. The reasoner cannot:
/// it builds each side from a `BTreeSet` of real rule instances, records only
/// rules that really concluded the proposition, and lists every assumption it
/// used. This function checks those claims before any resolution is read:
///
/// * every rule witness must name a rule of the environment, and the same side
///   must not name it twice;
/// * the rule's conclusion head must agree with the conflict proposition on
///   that side when both heads are concrete. An opaque head (a parameter or a
///   quantified formula) is not judged, which keeps the check conservative;
/// * an assumption side's proposition must occur in the certificate's
///   assumption table, compared as a `CertExpr` and independent of order.
///
/// The rule instances themselves are still not re-derived: the certificate
/// lists names, not instances.
fn validate_provenance(
    env: &Env,
    cert: &Certificate,
    index: usize,
    conflict: &Conflict,
) -> Result<(), CheckError> {
    let fail = |message: String| CheckError {
        node: None,
        message: format!("第 {} 个冲突：{message}", index + 1),
    };
    for (label, proposition, provenance) in [
        ("左", &conflict.left, &conflict.left_by),
        ("右", &conflict.right, &conflict.right_by),
    ] {
        match provenance {
            Provenance::Rules { rules } => {
                let mut seen: BTreeSet<&str> = BTreeSet::new();
                for rule in rules {
                    if !seen.insert(rule.as_str()) {
                        return Err(fail(format!(
                            "同一侧的规则见证重复：`{rule}` 在{label}侧出现了不止一次"
                        )));
                    }
                    let Some(declaration) = env.get(rule) else {
                        return Err(fail(format!("{label}侧引用的规则 `{rule}` 不在环境中")));
                    };
                    let DeclKind::Rule(declared) = &declaration.kind else {
                        return Err(fail(format!("{label}侧引用的 `{rule}` 不是规则")));
                    };
                    let Some(rule_head) =
                        closure::concrete_head(env, &declared.open_conclusion()).map_err(fail)?
                    else {
                        // The rule's conclusion head is not concrete (it is a
                        // parameter or a quantified form), so head agreement
                        // cannot be judged. Stay conservative.
                        continue;
                    };
                    let Some(proposition_head) =
                        closure::concrete_head(env, &Expr::from(proposition)).map_err(fail)?
                    else {
                        continue;
                    };
                    if rule_head != proposition_head {
                        return Err(fail(format!(
                            "规则 `{rule}` 的结论头与冲突命题不符：规则结论是 `{rule_head}`，\
                             冲突命题的头是 `{proposition_head}`"
                        )));
                    }
                }
            }
            Provenance::Assumption => {
                if !cert
                    .assumptions
                    .iter()
                    .any(|entry| &entry.proposition == proposition)
                {
                    return Err(fail(format!(
                        "{label}侧记录为已知事实，但证书的假设表里没有这个命题"
                    )));
                }
            }
        }
    }
    Ok(())
}

/// Validate one recorded conflict resolution against the environment, and
/// return how many priority edges it compared.
fn validate_resolution(
    priority: &PriorityGraph,
    index: usize,
    conflict: &Conflict,
) -> Result<usize, CheckError> {
    let fail = |message: String| CheckError {
        node: None,
        message: format!("第 {} 个冲突：{message}", index + 1),
    };
    match &conflict.resolution {
        Resolution::Defeated { winner, basis } => match basis {
            ResolutionBasis::Assumption => {
                let (winner_by, loser_by) = provenance_by_side(conflict, *winner);
                if !matches!(winner_by, Provenance::Assumption) {
                    return Err(fail(format!(
                        "以严格事实为裁决依据，但胜方（{}）不是假设",
                        side_label(*winner)
                    )));
                }
                if matches!(loser_by, Provenance::Assumption) {
                    return Err(fail(
                        "两侧都是严格事实：假设之间没有先后，不能判出一方胜出".to_owned(),
                    ));
                }
                Ok(0)
            }
            ResolutionBasis::Priority { edges } => {
                let left = rule_side(priority, conflict, Side::Left).map_err(fail)?;
                let right = rule_side(priority, conflict, Side::Right).map_err(fail)?;
                let (winners, losers) = match winner {
                    Side::Left => (&left, &right),
                    Side::Right => (&right, &left),
                };
                if edges.is_empty() {
                    return Err(fail("以优先关系裁决，但没有记录任何优先边".to_owned()));
                }
                for edge in edges {
                    if !winners.iter().any(|rule| rule == &edge.winner)
                        || !losers.iter().any(|rule| rule == &edge.loser)
                    {
                        return Err(fail(format!(
                            "优先边「{} over {}」的方向与裁决不符：胜方必须指向败方",
                            edge.winner, edge.loser
                        )));
                    }
                    let declared = priority
                        .declared
                        .get(&(edge.winner.clone(), edge.loser.clone()))
                        .is_some_and(|declared| declared.contains(edge));
                    if !declared {
                        return Err(fail(format!(
                            "环境中没有与记录完全相同的优先声明「{} over {}」：\
                             方向、声明者、子句和出处必须逐项一致",
                            edge.winner, edge.loser
                        )));
                    }
                    if !priority.is_effective(&edge.winner, &edge.loser) {
                        return Err(fail(format!(
                            "优先边「{} over {}」落在优先级环内，不能用于裁决",
                            edge.winner, edge.loser
                        )));
                    }
                }
                for winner_rule in winners {
                    for loser_rule in losers {
                        if !edges
                            .iter()
                            .any(|edge| &edge.winner == winner_rule && &edge.loser == loser_rule)
                        {
                            return Err(fail(format!(
                                "胜方规则 `{winner_rule}` 与败方规则 `{loser_rule}` 之间没有记录优先边"
                            )));
                        }
                    }
                }
                if !priority.beats(winners, losers) {
                    return Err(fail(
                        "按环境的优先关系重算，胜方没有完整覆盖败方，不能判为已裁决".to_owned(),
                    ));
                }
                if priority.beats(losers, winners) {
                    return Err(fail(
                        "按环境的优先关系重算，败方也完整覆盖了胜方：双方互斥，不能判出一方胜出"
                            .to_owned(),
                    ));
                }
                Ok(edges.len())
            }
        },
        Resolution::Unresolved { reason } => match reason {
            UnresolvedReason::ConflictingAssumptions => {
                if !matches!(conflict.left_by, Provenance::Assumption)
                    || !matches!(conflict.right_by, Provenance::Assumption)
                {
                    return Err(fail("记录为严格事实冲突，但至少一侧不是假设".to_owned()));
                }
                Ok(0)
            }
            UnresolvedReason::UnknownWitnesses => {
                // A strict fact can only win; it never leaves a conflict
                // unresolved for want of witnesses. The reasoner records
                // `Defeated { basis: Assumption }` when either side is an
                // assumption, so a hand-edited record must not relabel that
                // outcome as a lost witness.
                if matches!(conflict.left_by, Provenance::Assumption)
                    || matches!(conflict.right_by, Provenance::Assumption)
                {
                    return Err(fail(
                        "一侧是已知事实时，只能是事实胜出，不能记录为见证无法重建".to_owned(),
                    ));
                }
                let lost = matches!(&conflict.left_by, Provenance::Rules { rules } if rules.is_empty())
                    || matches!(&conflict.right_by, Provenance::Rules { rules } if rules.is_empty());
                if !lost {
                    return Err(fail("记录为见证无法重建，但两侧都有规则见证".to_owned()));
                }
                Ok(0)
            }
            UnresolvedReason::NoPriority => {
                let left = rule_side(priority, conflict, Side::Left).map_err(fail)?;
                let right = rule_side(priority, conflict, Side::Right).map_err(fail)?;
                let declared = priority.declared_between(&left, &right);
                if !declared.is_empty() {
                    return Err(fail(format!(
                        "环境在两侧规则之间声明了 {} 条优先边，不能记录为没有优先关系",
                        declared.len()
                    )));
                }
                Ok(0)
            }
            UnresolvedReason::PriorityUnusable { declared } => {
                // An empty list is not "declared but unusable": the reasoner
                // only records this reason when at least one priority is
                // declared between the sides. With no edge at all, the honest
                // record is `NoPriority`.
                if declared.is_empty() {
                    return Err(fail(
                        "记录为已有优先声明但不足以裁决，却没有任何已声明边；\
                         这种情况应记录为没有优先关系（no_priority）"
                            .to_owned(),
                    ));
                }
                let left = rule_side(priority, conflict, Side::Left).map_err(fail)?;
                let right = rule_side(priority, conflict, Side::Right).map_err(fail)?;
                let expected = priority.declared_between(&left, &right);
                if !same_edge_multiset(&expected, declared).map_err(fail)? {
                    return Err(fail(
                        "记录的优先边与环境中两侧之间的全部声明不一致：漏列、多列或出处不符"
                            .to_owned(),
                    ));
                }
                if priority.beats(&left, &right) || priority.beats(&right, &left) {
                    return Err(fail(
                        "按环境重算，一侧已能完整覆盖另一侧，应判为已裁决".to_owned(),
                    ));
                }
                Ok(declared.len())
            }
        },
    }
}

/// The two sides' provenances, winner first.
fn provenance_by_side(conflict: &Conflict, winner: Side) -> (&Provenance, &Provenance) {
    match winner {
        Side::Left => (&conflict.left_by, &conflict.right_by),
        Side::Right => (&conflict.right_by, &conflict.left_by),
    }
}

fn side_label(side: Side) -> &'static str {
    match side {
        Side::Left => "左",
        Side::Right => "右",
    }
}

/// The rules of one side of a conflict, checked to be a non-empty list of
/// rules that exist in the environment.
///
/// The checker does not re-derive the instances (the certificate's node graph
/// is checked separately and the provenance lists no bindings), but a rule
/// that is not in the environment cannot carry a priority either.
fn rule_side(
    priority: &PriorityGraph,
    conflict: &Conflict,
    side: Side,
) -> Result<Vec<String>, String> {
    let (label, provenance) = match side {
        Side::Left => ("左", &conflict.left_by),
        Side::Right => ("右", &conflict.right_by),
    };
    let Provenance::Rules { rules } = provenance else {
        return Err(format!("{label}侧不是规则推出的结论，不能按优先关系判断"));
    };
    if rules.is_empty() {
        return Err(format!(
            "{label}侧的规则见证为空：无法核对优先关系，这种情况应记录为见证无法重建"
        ));
    }
    for rule in rules {
        if !priority.rules.contains(rule) {
            return Err(format!("{label}侧引用的规则 `{rule}` 不在环境中"));
        }
    }
    Ok(rules.clone())
}

/// Compare two lists of priority edges as multisets, independent of order.
///
/// The full serialized edge is the comparison key, so the declaring module or
/// rule, the clause and every source field (in order) must match.
fn same_edge_multiset(expected: &[PriorityEdge], actual: &[PriorityEdge]) -> Result<bool, String> {
    if expected.len() != actual.len() {
        return Ok(false);
    }
    let mut expected = canonical_edges(expected)?;
    let mut actual = canonical_edges(actual)?;
    expected.sort();
    actual.sort();
    Ok(expected == actual)
}

fn canonical_edges(edges: &[PriorityEdge]) -> Result<Vec<String>, String> {
    edges
        .iter()
        .map(|edge| {
            serde_json::to_string(edge)
                .map_err(|error| format!("优先边无法序列化，不能比较：{error}"))
        })
        .collect()
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
