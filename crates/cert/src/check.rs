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
//!   a proposition. Every listed assumption carries the identity of the fact
//!   it records: a disputed proposition is not an assumption, and one
//!   proposition cannot appear under two identities, because conflict
//!   resolution reads that identity as evidence. Those comparisons use kernel
//!   conversion, so alpha- and eta-variants count as the same proposition. The
//!   recorded identity must also agree with the loaded environment: when the
//!   environment registers the same proposition as a fact, the certificate
//!   must write the same identity, and a strict identity (`verified` /
//!   `stipulated`) must be backed by such a registration. A non-strict identity
//!   with no loaded fact is a session fact (`:given`), whose truth the checker
//!   cannot verify; only its consistency with the certificate's resolution is
//!   checked.
//! * Every rule application names a rule, cites exactly as many premises as
//!   the rule has and cites them in the rule's own order, and cites only
//!   earlier nodes.
//! * Every axiom instance names an environment `Fact` declaration whose
//!   declared type is a telescope of named universal binders ending in a
//!   proposition, and whose identity the certificate records verbatim (a
//!   `disputed` fact is not a source). It binds every binder exactly once, in
//!   the declaration's order, to a closed value; the kernel checks each value
//!   against the instantiated binder domain. The conclusion must be exactly the
//!   declaration's body with those values substituted, compared by kernel
//!   conversion, and must be closed: a free variable, a bound-variable capture
//!   or a leaked binder variable is rejected. The node has no premise; the
//!   universal declaration is its evidence, and its recorded identity is
//!   compared with the environment's registration. Its recorded `sources` are
//!   the declaration's provenance: the count, order and every field (text,
//!   locator, version, effective date, note, quote, link, jurisdiction,
//!   retrieval time and hash) must equal the environment's `sources`; an added
//!   or dropped citation is rejected, so a certificate cannot claim a
//!   different article for the universal fact than the ledger declares.
//! * The bindings name only rule parameters, bind each parameter exactly once
//!   and are closed terms.
//! * Instantiating the rule's premises with those bindings yields exactly the
//!   propositions of the cited nodes; instantiating the conclusion yields
//!   exactly the node's conclusion.
//! * Every interpretation application cites an entry of the interpretations
//!   table and an earlier node proving the declared `from`, and concludes the
//!   declared `to`. A node whose conclusion was interpretation-derived may not
//!   be a rule premise or another interpretation's premise: rules never consume
//!   an interpretation conclusion, and interpretations never chain.
//! * Every rule application's applicability record is recomputed from the
//!   rule's loaded declaration and the occurrence records the environment
//!   registers for each cited premise proposition (a derived premise does not
//!   change the input), with the session values read from the certificate's
//!   environment identity. The verdict, reference dates/places, rule scope,
//!   session fallback and reason must match field by field; a rule step whose
//!   recomputed verdict is `inapplicable` or `undecidable` is rejected. A gap
//!   candidate's record is recomputed from its bindings and held premises:
//!   they must partition the rule's instantiated premises in order, the
//!   instantiated conclusion must equal the gap proposition, and the anchor is
//!   rebuilt from the held propositions' environment occurrences.
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
//!   basis must be a strict fact (`verified` or `stipulated`) or the
//!   environment's effective priority edges, an unusable priority must record
//!   exactly the declared edges between the sides, and an unresolved reason
//!   must match the provenances, the recorded identities and the graph. A
//!   fact-based defeat requires a strict winner and a non-strict loser; an
//!   unresolved conflict between two facts requires both to be strict or both
//!   to be claims; the non-strict-fact reason requires one claim side and one
//!   rule side, with the table recording the stated identity. The provenances
//!   themselves are checked first: a rule witness must be a rule of the
//!   environment that no other witness on the same side repeats, its
//!   conclusion head must agree with the conflict proposition when both heads
//!   are concrete, and an assumption side's proposition must occur in the
//!   certificate's assumption table. See "Root and conflicts" below.
//!
//! The derivability superset is not a second reasoner and does not claim the
//! reasoner's exact semantics; it is deliberately larger. It may therefore
//! reject a step whose blocker has a counter-argument elsewhere in the
//! environment. That is the intended direction: refuse a false green rather
//! than certify an omitted blocker.
//!
//! Open obligations are otherwise reported, not judged: they set
//! [`CheckReport::requires_human`] and leave `root_proved` alone. The exception
//! is the `open_concept` obligation, which is derived data rather than a note.
//! It is recomputed from the environment's `open` markers and the proof graph
//! reachable from the root ([`crate::open::dependency`]), and a certificate that
//! records a different one — or none, or several — is rejected. A rule step
//! concluding an open concept (`重大`, `情节严重`), or a root that is such a
//! predicate, depends on a human judgement; the certificate must not report it
//! as unconditional.
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
//! must name a strict fact as the winner; the loser may be a rule conclusion or
//! a claim, never another strict fact. An unresolved reason must match the
//! provenances and the recorded identities: two facts that are both strict or
//! both claims, a lost witness list with no assumption side, no declared edge
//! at all, or exactly the declared but unusable edges. A claim against a rule
//! conclusion is recorded as `non_strict_fact` with the claim's identity. The
//! report's
//! `priority_sources_checked` says the edges recorded by the certificate
//! passed; it does not mean every priority in the environment was inspected,
//! and an order no conflict cites is never compared.
//!
//! ## Calling preconditions
//!
//! `check` takes the loaded environment and the certificate as separate
//! values. It validates the certificate's nodes, assumptions, interpretations,
//! conflicts and applicability records against that environment, but it does
//! **not** compare
//! [`Certificate::environment`](crate::Certificate::environment) with the
//! environment it was handed: the certificate's recorded identity is not
//! derived from `env`, and the caller must compare it first
//! ([`EnvironmentIdentity::differences`](crate::EnvironmentIdentity::differences)).
//! The CLI's `:verify-cert` does exactly that before calling this function, so
//! a library user that skips the identity comparison still gets the node
//! checks but not the guarantee that the certificate belongs to this
//! environment (profile, packs, corpora, `as_of`, jurisdiction).
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
//! their legal effect is not judged. Open obligations other than the
//! `open_concept` one do not fail the check; they set `requires_human`. The
//! `open_concept` obligation is recomputed instead, as described above.
//! Whether the root is proved depends only on the
//! conflicts the root takes part in; a conflict elsewhere is validated but does
//! not change `root_proved`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use std_deduce_kernel::conv::convertible;
use std_deduce_kernel::env::{escape_control, named_binders, DeclKind, RuleDecl};
use std_deduce_kernel::norm::normalize;
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::term::{instantiate_telescope, is_closed};
use std_deduce_kernel::{check as kernel_check, Ctx, Env, Expr};

use crate::applicability::{
    ApplicabilityAnchor, DatedEvidence, PlaceEvidence, RuleApplicability, ScopeEvidence,
    SessionEvidence,
};
use crate::closure;
use crate::environment::EnvironmentIdentity;
use crate::expr::CertExpr;
use crate::key::expression_key;
use crate::model::{
    Certificate, Conflict, Explicit, FactIdentity, InterpretationDirection, Node, NodeId,
    ObligationKind, OpenObligation, PriorityClause, PriorityEdge, PriorityOrigin, Provenance,
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

    // The assumption table's identities are evidence: the conflict layer
    // reads them to decide whether a defeat is legal. They are checked before
    // any node, so a forged identity is reported on its own terms. The
    // environment's facts are read once and shared by the identity and
    // provenance checks.
    let facts = environment_facts(env)?;
    validate_assumptions(env, cert, &facts)?;
    // The event time and place a certificate records for an assumption must be
    // the one the environment registers; the applicability check aligns a rule
    // application's reference dates with these entries, so a forged occurrence
    // is caught before the verdict is recomputed.
    validate_assumption_occurrences(env, cert, &facts)?;
    // The applicability anchor is rebuilt exactly as the reasoner builds it:
    // by each referenced premise proposition's key, looked up in the
    // environment's registered occurrences. A premise proved by a derived
    // conclusion is not missing by itself; only a proposition the environment
    // registers no occurrence for is.
    let fact_occurrences = fact_occurrence_index(&facts);
    validate_interpretations(env, cert)?;

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
            Node::InterpretationApplication { conclusion, .. } => ("结论", Expr::from(conclusion)),
            Node::AxiomInstance { conclusion, .. } => ("公理实例的结论", Expr::from(conclusion)),
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

    // A proposition asserted by an environment fact is known whether or not
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
    //
    // `interpretation_derived[id]` marks a node whose conclusion was licensed
    // by an interpretation, directly or through a premise. The reasoner never
    // produces either a chain (an interpretation reading another's
    // conclusion) or a rule consuming one, so a certificate that does is not a
    // derivation this build accepts, even if every individual step typechecks.
    let mut interpretation_derived = vec![false; cert.nodes.len()];
    for (id, node) in cert.nodes.iter().enumerate() {
        if let Node::InterpretationApplication {
            interpretation,
            premise,
            conclusion,
        } = node
        {
            let Some(entry) = cert.interpretations.get(*interpretation) else {
                return Err(CheckError::at(
                    id,
                    format!(
                        "引用了不存在的解释 {interpretation}：证书只有 {} 条解释",
                        cert.interpretations.len()
                    ),
                ));
            };
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
            if interpretation_derived[*premise] {
                return Err(CheckError::at(
                    id,
                    format!(
                        "前提 {premise} 由解释推出，而解释不能消费另一条解释的结论：\
                         禁止解释链，一次只前进一步"
                    ),
                ));
            }
            let Some(proved) = node_prop(cert, &cert.nodes[*premise]) else {
                return Err(CheckError::at(
                    id,
                    format!("前提 {premise} 是缺口，不能充当解释的前提"),
                ));
            };
            let premise_expr = Expr::from(proved);
            let from = Expr::from(&entry.from);
            let same_from =
                convertible(env, &Ctx::new(), &premise_expr, &from).map_err(|error| {
                    CheckError::at(id, format!("无法判定解释的前提是否等价：{error}"))
                })?;
            if !same_from {
                return Err(CheckError::at(
                    id,
                    format!(
                        "解释 `{}` 的 from 是 `{}`，而前提 {premise} 证成的是 `{}`",
                        entry.id,
                        print_expr(&from),
                        print_expr(&premise_expr)
                    ),
                ));
            }
            let conclusion_expr = Expr::from(conclusion);
            let to = Expr::from(&entry.to);
            let same_to =
                convertible(env, &Ctx::new(), &conclusion_expr, &to).map_err(|error| {
                    CheckError::at(id, format!("无法判定解释的结论是否等价：{error}"))
                })?;
            if !same_to {
                return Err(CheckError::at(
                    id,
                    format!(
                        "解释 `{}` 的 to 是 `{}`，而本步的结论是 `{}`",
                        entry.id,
                        print_expr(&to),
                        print_expr(&conclusion_expr)
                    ),
                ));
            }
            interpretation_derived[id] = true;
            continue;
        }
        // Universal elimination. The node claims that a declared universal
        // fact, asserted under a recorded identity, yields the conclusion when
        // its binding variables take the recorded closed values. Every part is
        // recomputed from the kernel declaration: a changed value, a changed
        // conclusion, an open value or a declaration that is not a universal
        // proposition is rejected.
        if let Node::AxiomInstance {
            axiom,
            identity,
            bindings,
            conclusion,
            sources,
        } = node
        {
            let Some(decl) = env.get(axiom) else {
                return Err(CheckError::at(
                    id,
                    format!("未知全称公理 `{axiom}`：当前环境没有这个声明"),
                ));
            };
            let DeclKind::Fact {
                identity: declared_identity,
            } = &decl.kind
            else {
                return Err(CheckError::at(
                    id,
                    format!("`{axiom}` 不是断言命题的事实声明，不能作为公理实例化的依据"),
                ));
            };
            if !declared_identity.seeds_derivation() {
                return Err(CheckError::at(
                    id,
                    format!(
                        "公理 `{axiom}` 登记为「{}」，断言的是对方的主张，不能作为公理实例化的依据",
                        declared_identity.label_zh()
                    ),
                ));
            }
            if std_deduce_kernel::FactIdentity::from(identity) != *declared_identity {
                return Err(CheckError::at(
                    id,
                    format!(
                        "公理 `{axiom}` 在环境中登记为「{}」，而本步记录的是「{}」",
                        declared_identity.label_zh(),
                        identity.label_zh()
                    ),
                ));
            }
            let declaration = format!("公理 `{axiom}`");
            // The recorded sources are the declaration's provenance, not
            // free text: compare every field with the environment's
            // registration, and allow neither an added nor a dropped source.
            compare_sources(&decl.sources, sources, |message| {
                CheckError::at(id, format!("{declaration}：{message}"))
            })?;
            let Some((variables, body)) = named_binders(env, &decl.ty).map_err(|error| {
                CheckError::at(id, format!("无法解析{declaration}的类型：{error}"))
            })?
            else {
                return Err(CheckError::at(
                    id,
                    format!("{declaration}的类型不是带命名绑定变量的全称命题，不能实例化"),
                ));
            };
            if bindings.len() != variables.len() {
                return Err(CheckError::at(
                    id,
                    format!(
                        "{declaration}有 {} 个绑定变量，本步记录了 {} 个绑定",
                        variables.len(),
                        bindings.len()
                    ),
                ));
            }
            let mut values = Vec::with_capacity(variables.len());
            for (index, (variable, binding)) in variables.iter().zip(bindings.iter()).enumerate() {
                if variable.as_ref() != binding.parameter.as_str() {
                    return Err(CheckError::at(
                        id,
                        format!(
                            "{declaration}的第 {} 个绑定变量是 `{variable}`，本步记录的是 `{}`",
                            index + 1,
                            binding.parameter
                        ),
                    ));
                }
                let value = Expr::from(&binding.value);
                if !is_closed(&value) {
                    return Err(CheckError::at(
                        id,
                        format!("绑定变量 `{variable}` 的取值不是闭合项"),
                    ));
                }
                values.push(value);
            }
            // The declared type must itself be a universal proposition: it must
            // type-check as a proposition, and `named_binders` above already
            // required at least one named binder.
            kernel_check::check(env, &Ctx::new(), &decl.ty, &Expr::Sort(0)).map_err(|error| {
                CheckError::at(
                    id,
                    format!("{declaration}的类型不是命题，不能是公理实例化：{error}"),
                )
            })?;
            let expected = instantiate_telescope(&body, &values);
            // Applying the declaration to the values asks the kernel to check
            // every value against the binder's domain and to confirm the
            // substituted body is the instance's type.
            let applied = Expr::apps(Expr::constant(axiom), values.iter().cloned());
            kernel_check::check(env, &Ctx::new(), &applied, &expected).map_err(|error| {
                CheckError::at(
                    id,
                    format!("{declaration}的绑定值不满足其参数类型：{error}"),
                )
            })?;
            if !is_closed(&expected) {
                return Err(CheckError::at(
                    id,
                    format!("{declaration}的实例结论不是闭合命题：绑定不足或发生变量捕获"),
                ));
            }
            let conclusion_expr = Expr::from(conclusion);
            // The conclusion must not carry the declaration's binders as free
            // variables: an open conclusion is not the result of substituting
            // closed values.
            if !is_closed(&conclusion_expr) {
                return Err(CheckError::at(
                    id,
                    format!(
                        "{declaration}的结论「{}」含有自由变量（绑定变量泄漏），不是闭合命题",
                        print_expr(&conclusion_expr)
                    ),
                ));
            }
            let same =
                convertible(env, &Ctx::new(), &expected, &conclusion_expr).map_err(|error| {
                    CheckError::at(id, format!("无法判定公理实例结论是否等价：{error}"))
                })?;
            if !same {
                return Err(CheckError::at(
                    id,
                    format!(
                        "{declaration}按绑定得到的结论是 `{}`，而本步写的是 `{}`",
                        print_expr(&expected),
                        print_expr(&conclusion_expr)
                    ),
                ));
            }
            continue;
        }
        let Node::RuleApplication {
            rule,
            conclusion,
            premises,
            bindings,
            applicability,
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
            if interpretation_derived[*premise] {
                return Err(CheckError::at(
                    id,
                    format!(
                        "前提 {premise} 由解释推出，而规则不消费解释结论：\
                         解释不触发规则，也不能伪装成规则前提"
                    ),
                ));
            }
        }

        // The applicability record is recomputed from the environment's rule
        // declaration and the occurrence records registered for each cited
        // premise proposition. The checker does not trust the recorded
        // verdict, basis or reason: it derives the anchor itself and compares
        // every field. The node that proves a premise does not decide the
        // input; the proposition does, exactly as the reasoner's occurrence
        // index does.
        let session = declared_session(cert, applicability);
        let expected = rule_applicability_expected(
            env,
            cert,
            premises,
            &fact_occurrences,
            rule,
            &decl.scope,
            session,
        )
        .map_err(|message| CheckError::at(id, message))?;
        compare_applicability(id, applicability, &expected)?;
        if !expected.verdict.allows_firing() {
            return Err(CheckError::at(
                id,
                format!(
                    "规则 `{rule}` 的适用性判定为「{}」，该步不应成立：\
                     不适用或无法判定的实例不触发",
                    expected.verdict.keyword()
                ),
            ));
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

    // A gap candidate's applicability record explains why the rule cannot
    // supply the missing conclusion. It is recomputed from the candidate's own
    // bindings and held premises (checked against the rule's declaration)
    // against the environment's registered occurrences, so an unrelated
    // fact's date cannot impersonate this candidate's event.
    for (id, node) in cert.nodes.iter().enumerate() {
        let Node::Gap {
            proposition,
            candidates,
            ..
        } = node
        else {
            continue;
        };
        for (index, candidate) in candidates.iter().enumerate() {
            validate_candidate_applicability(
                env,
                cert,
                index,
                proposition,
                candidate,
                &fact_occurrences,
            )
            .map_err(|message| CheckError::at(id, message))?;
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
        validate_provenance(env, cert, &facts, index, conflict)?;
        priority_edges_checked += validate_resolution(&priority, cert, index, conflict)?;
    }

    // An `open_concept` obligation is not free text: it is recomputed from the
    // environment's markers and the proof graph reachable from the root. The
    // check refuses a certificate that dropped it, invented it or edited its
    // node list or description, so an open concept can never be certified as
    // an unconditional conclusion by deleting one obligation.
    validate_open_concept_obligations(env, cert)?;

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

/// Validate the identity recorded for every assumption against the
/// environment.
///
/// The identity is evidence, not decoration: conflict resolution reads it to
/// decide whether a fact may defeat a rule conclusion or another fact. Three
/// rules follow:
///
/// * a `disputed` proposition records what the other side claims, so it is not
///   an assumption at all and cannot support a derivation;
/// * one proposition has exactly one identity. The same claim listed twice is
///   harmless, but the same proposition listed as both `verified` and
///   `user_asserted` would let the certificate choose the stronger identity
///   when it reads a conflict. Propositions are compared by kernel conversion,
///   so alpha- and eta-variants cannot list the same proposition twice under
///   two identities;
/// * the certificate's identity must agree with the loaded environment. A
///   proposition the environment registers as a fact has one recorded
///   identity, and the certificate cannot rewrite it. A strict identity
///   (`verified` / `stipulated`) must be backed by a matching loaded fact: a
///   certificate that merely claims a court found something is not evidence.
///   A non-strict identity may stand without a loaded fact, because a session
///   fact (`:given`, `:fact assumed`) is part of the certificate's own
///   context and the checker cannot verify its truth; the checker only verifies
///   that the certificate's resolution is consistent with the identity it
///   records.
fn validate_assumptions(
    env: &Env,
    cert: &Certificate,
    facts: &[EnvironmentFact],
) -> Result<(), CheckError> {
    // Pass 1: disputed identities and one identity per proposition. This
    // runs before the environment comparison so a certificate that lists the
    // same proposition twice is reported as such, not as a mismatch with the
    // environment.
    let mut recorded: Vec<(&CertExpr, FactIdentity)> = Vec::new();
    for (index, entry) in cert.assumptions.iter().enumerate() {
        let fail = |message: String| CheckError {
            node: None,
            message: format!("第 {} 条假设：{message}", index + 1),
        };
        if entry.identity == FactIdentity::Disputed {
            return Err(fail(
                "争议事实不能作为假设：它断言的是对方的主张，不是已证明的命题".to_owned(),
            ));
        }
        let proposition = Expr::from(&entry.proposition);
        for (previous, previous_identity) in &recorded {
            let same = if *previous == &entry.proposition {
                true
            } else {
                convertible(env, &Ctx::new(), &Expr::from(*previous), &proposition)
                    .map_err(|error| fail(format!("无法判定两条假设是否为同一命题：{error}")))?
            };
            if same && previous_identity != &entry.identity {
                return Err(fail(format!(
                    "同一命题只能有一种事实身份：`{}` 已登记为{}，不能同时是{}",
                    print_expr(&proposition),
                    previous_identity.label_zh(),
                    entry.identity.label_zh()
                )));
            }
        }
        recorded.push((&entry.proposition, entry.identity));
    }

    // Pass 2: the identity must match the environment's registration. A
    // strict identity with no loaded fact is rejected: the certificate would
    // otherwise upgrade a session claim by editing one field.
    for (index, entry) in cert.assumptions.iter().enumerate() {
        let fail = |message: String| CheckError {
            node: None,
            message: format!("第 {} 条假设：{message}", index + 1),
        };
        let proposition = Expr::from(&entry.proposition);
        let proposition_key = key(env, &proposition).map_err(fail)?;
        let certificate_identity = std_deduce_kernel::FactIdentity::from(&entry.identity);
        let mut found = false;
        let mut mismatched = None;
        for fact in facts {
            let same = fact.key == proposition_key
                || convertible(env, &Ctx::new(), &fact.proposition, &proposition).map_err(
                    |error| {
                        fail(format!(
                            "无法判定假设命题是否与环境中事实 `{}` 等价：{error}",
                            fact.name
                        ))
                    },
                )?;
            if !same {
                continue;
            }
            found = true;
            if fact.identity != certificate_identity {
                mismatched = Some(FactIdentity::from(&fact.identity));
                break;
            }
        }
        if let Some(registered) = mismatched {
            return Err(fail(format!(
                "`{}` 在环境中登记为「{}」，证书写作「{}」",
                print_expr(&proposition),
                registered.label_zh(),
                entry.identity.label_zh()
            )));
        }
        if !found && is_strict(entry.identity) {
            return Err(fail(format!(
                "证书声称「{}」，但当前环境没有登记该命题的事实；\
                 严格身份必须来自已加载的事实声明",
                entry.identity.label_zh()
            )));
        }
    }
    Ok(())
}

/// One assumption's recorded occurrence, in the form the environment
/// declarations use.
type OccurrenceRecord = (Option<String>, Option<String>);

/// Validate every assumption's recorded event time and place against the
/// environment's fact registrations.
///
/// The applicability judgement reads occurrences from the fact ledger. A
/// certificate that writes an `occurred_at` the environment does not register,
/// or drops one it does register, would make its own reference dates
/// unreproducible. Comparisons use the kernel's equivalence for the
/// proposition and compare the occurrence pairs as a multiset, because one
/// proposition may be registered by more than one fact declaration and every
/// such registration becomes its own assumption record. A proposition the
/// environment does not register (a hand-registered reasoner assumption) can
/// record no occurrence, and a certificate that records one is rejected.
fn validate_assumption_occurrences(
    env: &Env,
    cert: &Certificate,
    facts: &[EnvironmentFact],
) -> Result<(), CheckError> {
    let mut environment: BTreeMap<String, Vec<OccurrenceRecord>> = BTreeMap::new();
    for fact in facts {
        // Only a fact that seeds the derivation becomes an assumption; a
        // disputed fact records what the other side claims and is skipped by
        // the reasoner.
        if !fact.identity.seeds_derivation() {
            continue;
        }
        environment
            .entry(fact.key.clone())
            .or_default()
            .push((fact.occurred_at.clone(), fact.occurred_in.clone()));
    }

    let mut recorded: BTreeMap<String, (String, Vec<OccurrenceRecord>)> = BTreeMap::new();
    for (index, entry) in cert.assumptions.iter().enumerate() {
        let proposition = Expr::from(&entry.proposition);
        let key = key(env, &proposition).map_err(|message| CheckError {
            node: None,
            message: format!("第 {} 条假设：{message}", index + 1),
        })?;
        let occurrence: OccurrenceRecord = (
            entry.occurred_at.as_ref().cloned(),
            entry.occurred_in.as_ref().cloned(),
        );
        recorded
            .entry(key)
            .or_insert_with(|| (print_expr(&proposition), Vec::new()))
            .1
            .push(occurrence);
    }

    for (key, (proposition, actual)) in recorded {
        let Some(expected) = environment.get(&key) else {
            if actual
                .iter()
                .any(|(date, place)| date.is_some() || place.is_some())
            {
                return Err(CheckError {
                    node: None,
                    message: format!(
                        "假设 `{proposition}` 记录了事件时间或地点，\
                         但当前环境没有登记该命题的事实：\
                         适用性依据的事件只能来自环境登记的事实"
                    ),
                });
            }
            continue;
        };
        // A duplicate assumption entry is redundant, not another occurrence:
        // the recorded occurrence pairs are compared as sets. Dropping a
        // registered occurrence or inventing one is still a mismatch.
        let expected: BTreeSet<OccurrenceRecord> = expected.iter().cloned().collect();
        let actual: BTreeSet<OccurrenceRecord> = actual.iter().cloned().collect();
        if expected != actual {
            return Err(CheckError {
                node: None,
                message: format!(
                    "假设 `{proposition}` 记录的事件时间/地点与环境登记的事实不一致：\
                     证书为 {}，环境为 {}",
                    occurrences_text(actual.iter()),
                    occurrences_text(expected.iter())
                ),
            });
        }
    }
    Ok(())
}

/// Render occurrence pairs for a diagnostic: `（事件时间 2020-01-01，地点 CN-HN）`.
fn occurrences_text<'a>(records: impl Iterator<Item = &'a OccurrenceRecord>) -> String {
    records
        .map(|(date, place)| {
            format!(
                "（事件时间 {}，地点 {}）",
                match date {
                    Some(date) => escape_control(date),
                    None => "未记录".to_owned(),
                },
                match place {
                    Some(place) => escape_control(place),
                    None => "未记录".to_owned(),
                }
            )
        })
        .collect::<Vec<_>>()
        .join("、")
}

/// The environment's registered occurrence records, keyed by the normalised
/// proposition key.
///
/// The reasoner's `instance_anchor` looks a referenced premise up by its
/// proposition key, not by the node that proves it. This index is built the
/// same way: every environment fact that seeds a derivation contributes its
/// `occurred_at` / `occurred_in` under its proposition key, in declaration-name
/// order (the order the ledger registers assumptions in). A premise proved by
/// a derived conclusion therefore still sees the occurrence the environment
/// registers for the same proposition, and a proposition with no registration
/// is the only thing marked missing.
fn fact_occurrence_index(facts: &[EnvironmentFact]) -> BTreeMap<String, Vec<OccurrenceRecord>> {
    let mut seeding: Vec<&EnvironmentFact> = facts
        .iter()
        .filter(|fact| fact.identity.seeds_derivation())
        .collect();
    seeding.sort_by(|left, right| left.name.cmp(&right.name));
    let mut index: BTreeMap<String, Vec<OccurrenceRecord>> = BTreeMap::new();
    for fact in seeding {
        index
            .entry(fact.key.clone())
            .or_default()
            .push((fact.occurred_at.clone(), fact.occurred_in.clone()));
    }
    index
}

/// The session values the certificate declares.
///
/// An exported certificate records them in its environment identity, and the
/// checker recomputes the judgement from those values only; the
/// applicability record cannot smuggle in a different `:asof` or jurisdiction.
/// An in-memory certificate (the reasoner's own derivation, which `:why` and
/// `:explain` print and check before an identity is stamped) has no identity
/// to read: its record's session fields are the declared session input. That
/// path never reaches `:verify-cert`, which always deserializes a recorded
/// certificate.
fn declared_session(
    cert: &Certificate,
    recorded: &RuleApplicability,
) -> (Option<String>, Option<String>) {
    match &cert.environment {
        EnvironmentIdentity::Recorded(record) => (
            record.as_of.as_deref().map(ToOwned::to_owned),
            record.jurisdiction.as_deref().map(ToOwned::to_owned),
        ),
        EnvironmentIdentity::Unrecorded => (
            recorded.basis.session.as_of.as_ref().cloned(),
            recorded.basis.session.jurisdiction.as_ref().cloned(),
        ),
    }
}

/// Append the registered occurrence records of one proposition to the anchor,
/// deduplicating dates and places in first-seen order.
fn collect_occurrence_records(records: &[OccurrenceRecord], anchor: &mut ApplicabilityAnchor) {
    for (date, place) in records {
        match date {
            Some(date) => {
                if !anchor.event_dates.contains(date) {
                    anchor.event_dates.push(date.clone());
                }
            }
            None => anchor.missing_event_date = true,
        }
        match place {
            Some(place) => {
                if !anchor.event_places.contains(place) {
                    anchor.event_places.push(place.clone());
                }
            }
            None => anchor.missing_event_place = true,
        }
    }
}

/// Add the occurrence records registered for one proposition key to the
/// anchor. A key with no registration is missing input.
fn collect_proposition_occurrences(
    env: &Env,
    proposition: &CertExpr,
    occurrences: &BTreeMap<String, Vec<OccurrenceRecord>>,
    anchor: &mut ApplicabilityAnchor,
) -> Result<(), String> {
    let key = key(env, &Expr::from(proposition))?;
    match occurrences.get(&key) {
        Some(records) => collect_occurrence_records(records, anchor),
        None => {
            anchor.missing_event_date = true;
            anchor.missing_event_place = true;
        }
    }
    Ok(())
}

/// Rebuild the anchor for one rule application from the propositions its
/// cited premises prove.
///
/// The occurrence record is looked up by the premise proposition's key, not
/// by whether the premise node is an assumption: the reasoner's occurrence
/// index contains the environment registrations, so a derived conclusion of
/// the same proposition carries the same event record. Only a proposition
/// with no environment registration marks the input missing — a rule or
/// interpretation conclusion never inherits the event time of its own
/// premises.
fn rule_applicability_expected(
    env: &Env,
    cert: &Certificate,
    premises: &[NodeId],
    occurrences: &BTreeMap<String, Vec<OccurrenceRecord>>,
    rule: &str,
    scope: &std_deduce_kernel::meta::Scope,
    session: (Option<String>, Option<String>),
) -> Result<RuleApplicability, String> {
    let (as_of, jurisdiction) = session;
    let mut anchor = ApplicabilityAnchor {
        as_of,
        jurisdiction,
        ..ApplicabilityAnchor::default()
    };
    for premise in premises {
        let Some(proposition) = node_prop(cert, &cert.nodes[*premise]) else {
            return Err(format!(
                "规则 `{rule}` 的前提 {premise} 是缺口，不能充当适用性依据"
            ));
        };
        collect_proposition_occurrences(env, proposition, occurrences, &mut anchor)?;
    }
    Ok(crate::applicability::judge(scope, &anchor))
}

/// Validate one gap candidate's applicability record.
///
/// The candidate records the parameter bindings that produced it and the
/// premises it already holds. The checker re-instantiates the rule's premises,
/// verifies that the held and missing lists partition them in order, checks
/// that the instantiated conclusion is the gap proposition, and only then
/// rebuilds the anchor from the held propositions' environment occurrences.
/// The recorded dates are never read as input.
fn validate_candidate_applicability(
    env: &Env,
    cert: &Certificate,
    index: usize,
    proposition: &CertExpr,
    candidate: &crate::model::GapCandidate,
    occurrences: &BTreeMap<String, Vec<OccurrenceRecord>>,
) -> Result<(), String> {
    let rule = escape_control(&candidate.rule);
    let Some(declaration) = env.get(&candidate.rule) else {
        return Err(format!("缺口候选规则 `{rule}` 不存在于当前环境"));
    };
    let DeclKind::Rule(declared) = &declaration.kind else {
        return Err(format!("缺口候选 `{rule}` 不是规则"));
    };
    let place = format!("缺口节点的第 {} 个候选规则 `{rule}`", index + 1);
    let recorded = &candidate.applicability;

    let mut binding: BTreeMap<&str, Expr> = BTreeMap::new();
    for entry in &candidate.bindings {
        if !declared
            .params
            .iter()
            .any(|(parameter, _)| parameter.as_ref() == entry.parameter)
        {
            return Err(format!(
                "{place}：绑定参数 `{}` 不是规则 `{rule}` 的参数",
                entry.parameter
            ));
        }
        if binding.contains_key(entry.parameter.as_str()) {
            return Err(format!("{place}：参数 `{}` 被重复绑定", entry.parameter));
        }
        let value = Expr::from(&entry.value);
        if !is_closed(&value) {
            return Err(format!(
                "{place}：参数 `{}` 的绑定值不是闭合项",
                entry.parameter
            ));
        }
        binding.insert(entry.parameter.as_str(), value);
    }
    let expected_premises: Vec<Expr> = (0..declared.premises.len())
        .map(|i| close_pattern(&declared.open_premise(i), &binding))
        .collect();
    let conclusion = close_pattern(&declared.open_conclusion(), &binding);
    if key(env, &conclusion)? != key(env, &Expr::from(proposition))? {
        return Err(format!(
            "{place}：绑定确立的实例结论是 `{}`，而缺口命题是 `{}`",
            print_expr(&conclusion),
            print_expr(&Expr::from(proposition))
        ));
    }

    // Merge the held and missing lists against the rule's premise order. Both
    // lists are subsequences of the instantiated premise list; a premise in
    // neither list, a duplicate, or an unrelated proposition breaks the merge
    // and is rejected.
    let mut held_index = 0usize;
    let mut missing_index = 0usize;
    for (position, expected) in expected_premises.iter().enumerate() {
        let expected_key = key(env, expected)?;
        let held_matches = candidate.held.get(held_index).is_some_and(|held| {
            key(env, &Expr::from(held)).is_ok_and(|held_key| held_key == expected_key)
        });
        let missing_matches = candidate.missing.get(missing_index).is_some_and(|missing| {
            key(env, &Expr::from(missing)).is_ok_and(|missing_key| missing_key == expected_key)
        });
        if held_matches {
            held_index += 1;
        } else if missing_matches {
            missing_index += 1;
        } else {
            return Err(format!(
                "{place}：规则的第 {} 个前提实例是 `{}`，但候选既未把它列为已持有，\
                 也未把它列为缺失",
                position + 1,
                print_expr(expected)
            ));
        }
    }
    if held_index != candidate.held.len() {
        return Err(format!(
            "{place}：已持有前提列表与规则前提不匹配（多出 {} 条）",
            candidate.held.len() - held_index
        ));
    }
    if missing_index != candidate.missing.len() {
        return Err(format!(
            "{place}：缺失前提列表与规则前提不匹配（多出 {} 条）",
            candidate.missing.len() - missing_index
        ));
    }

    let (as_of, jurisdiction) = declared_session(cert, recorded);
    let mut anchor = ApplicabilityAnchor {
        as_of,
        jurisdiction,
        ..ApplicabilityAnchor::default()
    };
    for held in &candidate.held {
        collect_proposition_occurrences(env, held, occurrences, &mut anchor)?;
    }
    let expected = crate::applicability::judge(&declaration.scope, &anchor);
    compare_applicability_record(&place, recorded, &expected)
}

/// Compare a rule application's applicability record, reporting the node and
/// the first differing field.
fn compare_applicability(
    node: NodeId,
    recorded: &RuleApplicability,
    expected: &RuleApplicability,
) -> Result<(), CheckError> {
    let place = "适用性记录".to_owned();
    compare_applicability_record(&place, recorded, expected)
        .map_err(|message| CheckError::at(node, message))
}

fn compare_applicability_record(
    place: &str,
    recorded: &RuleApplicability,
    expected: &RuleApplicability,
) -> Result<(), String> {
    if recorded.verdict != expected.verdict {
        return Err(format!(
            "{place}的判定为 `{}`，按声明的输入与环境范围重算为 `{}`",
            recorded.verdict.keyword(),
            expected.verdict.keyword()
        ));
    }

    match (recorded.reason(), expected.reason()) {
        (None, None) => {}
        (Some(recorded), Some(expected)) => {
            if recorded.detail != expected.detail {
                return Err(format!(
                    "{place}的原因与重算不一致：证书代码 `{}`、说明「{}」；\
                     重算代码 `{}`、说明「{}」",
                    recorded.code(),
                    recorded.text,
                    expected.code(),
                    expected.text
                ));
            }
            if recorded.text != expected.text {
                return Err(format!(
                    "{place}的原因说明「{}」与重算的「{}」不同",
                    recorded.text, expected.text
                ));
            }
        }
        (Some(recorded), None) => {
            return Err(format!(
                "{place}记录了原因 `{}`，但重算的判定为适用，不应有原因",
                recorded.code()
            ));
        }
        (None, Some(expected)) => {
            return Err(format!(
                "{place}缺少原因，但重算给出了原因代码 `{}`（说明「{}」）",
                expected.code(),
                expected.text
            ));
        }
    }

    compare_scope(place, &recorded.basis.scope, &expected.basis.scope)?;
    compare_session(place, &recorded.basis.session, &expected.basis.session)?;
    if recorded.basis.missing_event_date != expected.basis.missing_event_date {
        return Err(format!(
            "{place}的 `missing_event_date` 为 {}，按引用的前提事实重算为 {}",
            recorded.basis.missing_event_date, expected.basis.missing_event_date
        ));
    }
    if recorded.basis.missing_event_place != expected.basis.missing_event_place {
        return Err(format!(
            "{place}的 `missing_event_place` 为 {}，按引用的前提事实重算为 {}",
            recorded.basis.missing_event_place, expected.basis.missing_event_place
        ));
    }
    compare_dates(place, &recorded.basis.dates, &expected.basis.dates)?;
    compare_places(place, &recorded.basis.places, &expected.basis.places)?;
    Ok(())
}

fn compare_scope(
    place: &str,
    recorded: &ScopeEvidence,
    expected: &ScopeEvidence,
) -> Result<(), String> {
    for (field, same) in [
        (
            "effective_from",
            recorded.effective_from == expected.effective_from,
        ),
        (
            "effective_to",
            recorded.effective_to == expected.effective_to,
        ),
        (
            "jurisdiction",
            recorded.jurisdiction == expected.jurisdiction,
        ),
        ("territory", recorded.territory == expected.territory),
        (
            "effective_from_origin",
            recorded.effective_from_origin == expected.effective_from_origin,
        ),
        (
            "effective_to_origin",
            recorded.effective_to_origin == expected.effective_to_origin,
        ),
        (
            "jurisdiction_origin",
            recorded.jurisdiction_origin == expected.jurisdiction_origin,
        ),
        (
            "territory_origin",
            recorded.territory_origin == expected.territory_origin,
        ),
    ] {
        if !same {
            return Err(format!(
                "{place}的规则范围字段 `{field}` 与当前环境声明的规则范围不一致"
            ));
        }
    }
    Ok(())
}

fn compare_session(
    place: &str,
    recorded: &SessionEvidence,
    expected: &SessionEvidence,
) -> Result<(), String> {
    if recorded.as_of != expected.as_of {
        return Err(format!(
            "{place}的会话兜底 `as_of` 为 {}，按证书声明的会话值与前提事实重算为 {}",
            explicit_text(&recorded.as_of),
            explicit_text(&expected.as_of)
        ));
    }
    if recorded.jurisdiction != expected.jurisdiction {
        return Err(format!(
            "{place}的会话管辖为 {}，按证书声明的会话值重算为 {}",
            explicit_text(&recorded.jurisdiction),
            explicit_text(&expected.jurisdiction)
        ));
    }
    Ok(())
}

fn explicit_text(value: &Explicit<String>) -> String {
    match value.as_ref() {
        Some(value) => format!("`{}`", escape_control(value)),
        None => "null".to_owned(),
    }
}

fn compare_dates(
    place: &str,
    recorded: &[DatedEvidence],
    expected: &[DatedEvidence],
) -> Result<(), String> {
    if recorded.len() != expected.len() {
        return Err(format!(
            "{place}记录了 {} 个事件时间，按引用的前提事实重算为 {} 个",
            recorded.len(),
            expected.len()
        ));
    }
    for (index, (recorded, expected)) in recorded.iter().zip(expected.iter()).enumerate() {
        if recorded.date != expected.date {
            return Err(format!(
                "{place}的 `dates[{index}].date` 为 `{}`，重算为 `{}`",
                escape_control(&recorded.date),
                escape_control(&expected.date)
            ));
        }
        if recorded.query_date_fallback != expected.query_date_fallback {
            return Err(format!(
                "{place}的 `dates[{index}].query_date_fallback` 为 {}，重算为 {}",
                recorded.query_date_fallback, expected.query_date_fallback
            ));
        }
        if recorded.covered != expected.covered {
            return Err(format!(
                "{place}的 `dates[{index}].covered` 为 {}，重算为 {}",
                recorded.covered, expected.covered
            ));
        }
    }
    Ok(())
}

fn compare_places(
    place: &str,
    recorded: &[PlaceEvidence],
    expected: &[PlaceEvidence],
) -> Result<(), String> {
    if recorded.len() != expected.len() {
        return Err(format!(
            "{place}记录了 {} 个事件地点，按引用的前提事实重算为 {} 个",
            recorded.len(),
            expected.len()
        ));
    }
    for (index, (recorded, expected)) in recorded.iter().zip(expected.iter()).enumerate() {
        if recorded.place != expected.place {
            return Err(format!(
                "{place}的 `places[{index}].place` 为 `{}`，重算为 `{}`",
                escape_control(&recorded.place),
                escape_control(&expected.place)
            ));
        }
        if recorded.covered != expected.covered {
            return Err(format!(
                "{place}的 `places[{index}].covered` 与重算不一致：证书为 {}，重算为 {}",
                coverage_text(recorded.covered),
                coverage_text(expected.covered)
            ));
        }
    }
    Ok(())
}

fn coverage_text(covered: Option<bool>) -> String {
    match covered {
        Some(true) => "覆盖".to_owned(),
        Some(false) => "不覆盖".to_owned(),
        None => "层级未声明".to_owned(),
    }
}

/// Validate the certificate's interpretation table against the environment.
///
/// The certificate lists the interpretations the derivation enabled. Each entry must
/// name an environment declaration of kind `Interpretation`, whose `from` and
/// `to` are kernel-equivalent to the recorded ones, whose direction and
/// sources agree field by field, and the table must be sorted by `id` with no
/// duplicate. A missing entry is a refusal, never a silent downgrade: the
/// proof's interpretation step would lose its licence.
fn validate_interpretations(env: &Env, cert: &Certificate) -> Result<(), CheckError> {
    for pair in cert.interpretations.windows(2) {
        if pair[0].id >= pair[1].id {
            return Err(CheckError {
                node: None,
                message: format!(
                    "证书的解释表必须按 id 严格排序且不能重复：`{}` 与 `{}` 顺序不符",
                    pair[0].id, pair[1].id
                ),
            });
        }
    }
    for (index, entry) in cert.interpretations.iter().enumerate() {
        let fail = |message: String| CheckError {
            node: None,
            message: format!("第 {} 条解释 `{}`：{message}", index + 1, entry.id),
        };
        let Some(decl) = env.get(&entry.id) else {
            return Err(fail("当前环境没有声明这个解释".to_owned()));
        };
        let DeclKind::Interpretation(declared) = &decl.kind else {
            return Err(fail("环境中的同名声明不是解释".to_owned()));
        };
        let from = Expr::from(&entry.from);
        let same_from = convertible(env, &Ctx::new(), &from, &declared.from)
            .map_err(|error| fail(format!("无法判定 from 是否与环境的解释声明等价：{error}")))?;
        if !same_from {
            return Err(fail(format!(
                "证书的 from 是 `{}`，环境声明的 from 是 `{}`，两者在内核下不等价",
                print_expr(&from),
                print_expr(&declared.from)
            )));
        }
        let to = Expr::from(&entry.to);
        let same_to = convertible(env, &Ctx::new(), &to, &declared.to)
            .map_err(|error| fail(format!("无法判定 to 是否与环境的解释声明等价：{error}")))?;
        if !same_to {
            return Err(fail(format!(
                "证书的 to 是 `{}`，环境声明的 to 是 `{}`，两者在内核下不等价",
                print_expr(&to),
                print_expr(&declared.to)
            )));
        }
        if InterpretationDirection::from(&declared.direction) != entry.direction {
            return Err(fail(format!(
                "证书的方向是 `{}`，环境声明的方向是 `{}`",
                entry.direction.keyword(),
                InterpretationDirection::from(&declared.direction).keyword()
            )));
        }
        compare_sources(&declared.sources, &entry.sources, fail)?;
    }

    // Every listed interpretation must be referenced by an application node
    // or by a conflict witness, and two listed interpretations may not license
    // kernel-equivalent conclusions: the reasoner refuses to enable such a
    // pair, so a certificate that lists both was not produced by it.
    let mut referenced = BTreeSet::new();
    for node in &cert.nodes {
        if let Node::InterpretationApplication { interpretation, .. } = node {
            referenced.insert(*interpretation);
        }
    }
    for conflict in &cert.conflicts {
        for provenance in [&conflict.left_by, &conflict.right_by] {
            if let Provenance::Interpretation { interpretation } = provenance {
                referenced.insert(*interpretation);
            }
        }
    }
    for index in &referenced {
        if *index >= cert.interpretations.len() {
            return Err(CheckError {
                node: None,
                message: format!(
                    "解释应用或冲突见证引用了不存在的解释 {index}：证书只有 {} 条解释",
                    cert.interpretations.len()
                ),
            });
        }
    }
    for index in 0..cert.interpretations.len() {
        if !referenced.contains(&index) {
            return Err(CheckError {
                node: None,
                message: format!(
                    "第 {} 条解释 `{}` 没有被任何解释应用节点或冲突见证引用；\
                     证书只列本次启用且被引用的解释",
                    index + 1,
                    cert.interpretations[index].id
                ),
            });
        }
    }
    for left in 0..cert.interpretations.len() {
        for right in (left + 1)..cert.interpretations.len() {
            let same = convertible(
                env,
                &Ctx::new(),
                &Expr::from(&cert.interpretations[left].to),
                &Expr::from(&cert.interpretations[right].to),
            )
            .map_err(|error| CheckError {
                node: None,
                message: format!("无法判定两条解释的 to 是否等价：{error}"),
            })?;
            if same {
                return Err(CheckError {
                    node: None,
                    message: format!(
                        "解释 `{}` 与 `{}` 的 to 在内核下等价，不能同时启用",
                        cert.interpretations[left].id, cert.interpretations[right].id
                    ),
                });
            }
        }
    }
    Ok(())
}

/// Compare a certificate's recorded sources with an environment declaration's
/// sources, field by field.
///
/// This is the one comparison used for every certificate record whose sources
/// claim to be a declaration's provenance (an interpretation table entry and an
/// `axiom_instance` node). A source is a citation, not free text: the reasoner
/// copies the declaration's sources verbatim, so a certificate that names a
/// different article, quote, version, jurisdiction or any other field is
/// rejected. The length is compared first, so a certificate cannot add a source
/// the declaration does not have, or drop one it does have, while keeping the
/// rest plausible. Every differing field is named with both values; `fail`
/// attaches the node or table entry the comparison belongs to.
fn compare_sources(
    expected: &[std_deduce_kernel::env::SourceRef],
    actual: &[Source],
    fail: impl Fn(String) -> CheckError,
) -> Result<(), CheckError> {
    if actual.len() != expected.len() {
        return Err(fail(format!(
            "证书记录了 {} 条来源，环境声明有 {} 条",
            actual.len(),
            expected.len()
        )));
    }
    for (index, source) in actual.iter().enumerate() {
        let differences = source_differences(&expected[index], source);
        if !differences.is_empty() {
            return Err(fail(format!(
                "第 {} 条来源与环境中声明不一致：{}",
                index + 1,
                differences.join("；")
            )));
        }
    }
    Ok(())
}

/// The fields on which a certificate source differs from the declaration.
///
/// Each entry names the field and shows both values, so a hand-edited citation
/// is reported on its own terms rather than as a generic inequality. The
/// comparison uses the kernel's field names and the certificate-to-kernel
/// conversion, so it cannot drift from the ledger's own `SourceRef`.
fn source_differences(
    expected: &std_deduce_kernel::env::SourceRef,
    actual: &Source,
) -> Vec<String> {
    let actual = std_deduce_kernel::env::SourceRef::from(actual);
    let mut differences = Vec::new();
    push_source_field(&mut differences, "文本", &expected.text, &actual.text);
    push_source_field(&mut differences, "条号", &expected.locator, &actual.locator);
    push_source_field(&mut differences, "版本", &expected.version, &actual.version);
    if expected.effective != actual.effective {
        differences.push(format!(
            "「生效」证书是 {}，环境是 {}",
            effective_text(&actual.effective),
            effective_text(&expected.effective)
        ));
    }
    push_source_field(&mut differences, "备注", &expected.note, &actual.note);
    push_source_field(&mut differences, "引文", &expected.quote, &actual.quote);
    push_source_field(&mut differences, "链接", &expected.url, &actual.url);
    push_source_field(
        &mut differences,
        "管辖",
        &expected.jurisdiction,
        &actual.jurisdiction,
    );
    push_source_field(
        &mut differences,
        "抓取时间",
        &expected.retrieved_at,
        &actual.retrieved_at,
    );
    push_source_field(&mut differences, "哈希", &expected.hash, &actual.hash);
    differences
}

/// Record one differing source field, naming the field and both values.
fn push_source_field(differences: &mut Vec<String>, label: &str, expected: &str, actual: &str) {
    if expected != actual {
        differences.push(format!(
            "「{}」证书是 `{}`，环境是 `{}`",
            label,
            escape_control(actual),
            escape_control(expected)
        ));
    }
}

/// Render an optional effective date in a source difference.
fn effective_text(value: &Option<String>) -> String {
    match value {
        Some(value) => format!("`{}`", escape_control(value)),
        None => "未记录".to_owned(),
    }
}

/// Recompute the certificate's `open_concept` obligation and compare it with
/// what the certificate records.
///
/// An `open` marker says a predicate such as 「重大」 needs a human judgement.
/// A rule step that concludes it, or a root that is itself such a predicate,
/// therefore cannot be certified as an unconditional proof. The obligation is
/// derived data, not a free-text note: [`crate::open::dependency`] rebuilds it
/// from the environment's markers and the proof graph reachable from the root,
/// and this check requires exactly that obligation. Deleting it makes the open
/// concept look proved; adding one to an unrelated conclusion would be just as
/// dishonest. Both are rejected.
fn validate_open_concept_obligations(env: &Env, cert: &Certificate) -> Result<(), CheckError> {
    let expected = crate::open::dependency(env, cert)
        .map_err(|message| CheckError {
            node: None,
            message,
        })?
        .map(|dependency| dependency.obligation());
    let recorded: Vec<&OpenObligation> = cert
        .open_obligations
        .iter()
        .filter(|obligation| obligation.kind == ObligationKind::OpenConcept)
        .collect();
    let Some(expected) = expected else {
        if recorded.is_empty() {
            return Ok(());
        }
        return Err(CheckError {
            node: None,
            message: format!(
                "证书记录了开放概念义务 `{}`，但按当前环境的 open 标记与证明节点重算，\
                 根推导不依赖任何开放概念：开放概念义务不能手工添加",
                escape_control(&recorded[0].id)
            ),
        });
    };
    match recorded.as_slice() {
        [] => Err(CheckError {
            node: None,
            message: format!(
                "根推导依赖开放概念，但证书没有记录开放概念义务（应为：{}）；\
                 删掉该义务会把带开放概念的结论伪装成无保留的证明",
                expected.description
            ),
        }),
        [only] if *only == &expected => Ok(()),
        [only] => Err(CheckError {
            node: None,
            message: format!(
                "证书记录的开放概念义务与按环境与节点重算的结果不一致：\
                 id、描述与节点必须逐字段相同（记录：id `{}`，节点 {:?}，描述「{}」；\
                 重算：id `{}`，节点 {:?}，描述「{}」）",
                escape_control(&only.id),
                only.nodes,
                escape_control(&only.description),
                escape_control(&expected.id),
                expected.nodes,
                expected.description
            ),
        }),
        many => Err(CheckError {
            node: None,
            message: format!(
                "证书记录了 {} 条开放概念义务：一条根推导只能记录一条（{}）",
                many.len(),
                expected.description
            ),
        }),
    }
}

/// One environment fact, with the normalized proposition and its comparison key.
struct EnvironmentFact {
    name: String,
    proposition: Expr,
    key: String,
    identity: std_deduce_kernel::FactIdentity,
    /// The `occurred_at` the declaration records, if any.
    occurred_at: Option<String>,
    /// The `occurred_in` the declaration records, if any.
    occurred_in: Option<String>,
}

/// Every environment declaration that registers a proposition as a fact.
///
/// `Env::insert` already refuses a `Fact` whose declared type is not a
/// proposition; the sort is checked again here because a directly built
/// ledger is part of the checker's input too. A disputed fact is included:
/// it is a registration of who says what, and the certificate must not write
/// a different identity for the same proposition.
fn environment_facts(env: &Env) -> Result<Vec<EnvironmentFact>, CheckError> {
    let mut facts = Vec::new();
    for decl in env.iter() {
        let DeclKind::Fact { identity } = &decl.kind else {
            continue;
        };
        let declared_sort = kernel_check::infer(env, &Ctx::new(), &decl.ty)
            .and_then(|ty| normalize(env, &Ctx::new(), &ty))
            .map_err(|error| CheckError {
                node: None,
                message: format!("环境事实 `{}` 的类型无法检查：{error}", decl.name),
            })?;
        if declared_sort != Expr::Sort(0) {
            continue;
        }
        let proposition = normalize(env, &Ctx::new(), &decl.ty).map_err(|error| CheckError {
            node: None,
            message: format!("环境事实 `{}` 无法规范化，无法比较：{error}", decl.name),
        })?;
        facts.push(EnvironmentFact {
            name: decl.name.to_string(),
            key: expression_key(&proposition),
            proposition,
            // `DeclKind::Fact` carries the kernel's identity; the certificate
            // uses its own wire type. The comparison converts the certificate
            // side, so the stored value stays the ledger's own.
            identity: *identity,
            occurred_at: decl.occurred_at.clone(),
            occurred_in: decl.occurred_in.clone(),
        });
    }
    Ok(facts)
}

/// The identity the certificate's assumption table records for `proposition`.
///
/// [`validate_provenance`] has already established that an assumption side's
/// proposition is listed, so a miss is reported as an error rather than read
/// as an identity-free fact.
fn recorded_identity(
    cert: &Certificate,
    side: Side,
    proposition: &CertExpr,
) -> Result<FactIdentity, String> {
    cert.assumptions
        .iter()
        .find(|entry| &entry.proposition == proposition)
        .map(|entry| entry.identity)
        .ok_or_else(|| {
            format!(
                "{}侧记录为已知事实，但证书的假设表里没有这个命题",
                side_label(side)
            )
        })
}

/// Whether a certificate identity is a strict fact.
///
/// The kernel owns the distinction; the certificate reads it through the
/// conversion instead of restating which identities are strict.
fn is_strict(identity: FactIdentity) -> bool {
    std_deduce_kernel::FactIdentity::from(&identity).is_strict()
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
/// * a rule side's proposition must not also occur in the certificate's
///   assumption table or be registered as a non-disputed fact in the
///   environment: a proposition is one thing, and a fact cannot be relabelled
///   as a rule derivation to hide the evidence;
/// * an assumption side's proposition must occur in the certificate's
///   assumption table, compared as a `CertExpr` and independent of order.
///
/// The rule instances themselves are still not re-derived: the certificate
/// lists names, not instances.
fn validate_provenance(
    env: &Env,
    cert: &Certificate,
    facts: &[EnvironmentFact],
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
                // A proposition is one thing: a side the certificate lists as
                // an assumed fact (or the environment registers as one)
                // cannot also be recorded as a rule derivation. The reasoner
                // never produces this combination — a fact side is supported by
                // the fact, not by rules — so it is a hand-edited record trying
                // to hide the fact that the side is an assumption.
                let proposition_expr = Expr::from(proposition);
                for entry in &cert.assumptions {
                    let same = entry.proposition == *proposition
                        || convertible(
                            env,
                            &Ctx::new(),
                            &Expr::from(&entry.proposition),
                            &proposition_expr,
                        )
                        .map_err(|error| {
                            fail(format!(
                                "无法判定{label}侧命题是否与证书假设表等价：{error}"
                            ))
                        })?;
                    if same {
                        return Err(fail(format!(
                            "{label}侧命题「{}」已作为事实列在假设表里，不能同时记为规则推导",
                            print_expr(&proposition_expr)
                        )));
                    }
                }
                let proposition_key = key(env, &proposition_expr).map_err(fail)?;
                for fact in facts {
                    if !fact.identity.seeds_derivation() {
                        continue;
                    }
                    let same = fact.key == proposition_key
                        || convertible(env, &Ctx::new(), &fact.proposition, &proposition_expr)
                            .map_err(|error| {
                                fail(format!(
                                    "无法判定{label}侧命题是否与环境中事实 `{}` 等价：{error}",
                                    fact.name
                                ))
                            })?;
                    if same {
                        return Err(fail(format!(
                            "{label}侧命题「{}」已在环境中登记为事实，不能同时记为规则推导",
                            print_expr(&proposition_expr)
                        )));
                    }
                }
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
            Provenance::Axiom { axiom } => {
                // A universal elimination is a derivation, so it cannot also be
                // an assumed fact or an environment fact: the reasoner records
                // a fact side as `assumption`, and a hand-edited record must
                // not relabel evidence as a derivation.
                let proposition_expr = Expr::from(proposition);
                for entry in &cert.assumptions {
                    let same = entry.proposition == *proposition
                        || convertible(
                            env,
                            &Ctx::new(),
                            &Expr::from(&entry.proposition),
                            &proposition_expr,
                        )
                        .map_err(|error| {
                            fail(format!(
                                "无法判定{label}侧命题是否与证书假设表等价：{error}"
                            ))
                        })?;
                    if same {
                        return Err(fail(format!(
                            "{label}侧命题「{}」已作为事实列在假设表里，不能同时记为公理实例",
                            print_expr(&proposition_expr)
                        )));
                    }
                }
                let proposition_key = key(env, &proposition_expr).map_err(fail)?;
                for fact in facts {
                    if !fact.identity.seeds_derivation() {
                        continue;
                    }
                    let same = fact.key == proposition_key
                        || convertible(env, &Ctx::new(), &fact.proposition, &proposition_expr)
                            .map_err(|error| {
                                fail(format!(
                                    "无法判定{label}侧命题是否与环境中事实 `{}` 等价：{error}",
                                    fact.name
                                ))
                            })?;
                    if same {
                        return Err(fail(format!(
                            "{label}侧命题「{}」已在环境中登记为事实，不能同时记为公理实例",
                            print_expr(&proposition_expr)
                        )));
                    }
                }
                let Some(declaration) = env.get(axiom) else {
                    return Err(fail(format!(
                        "{label}侧引用的全称公理 `{axiom}` 不在环境中"
                    )));
                };
                let DeclKind::Fact { identity } = &declaration.kind else {
                    return Err(fail(format!(
                        "{label}侧引用的 `{axiom}` 不是断言命题的事实声明，不能是公理实例的来源"
                    )));
                };
                if !identity.seeds_derivation() {
                    return Err(fail(format!(
                        "{label}侧引用的 `{axiom}` 登记为「{}」，不能作为公理实例化的依据",
                        identity.label_zh()
                    )));
                }
                let Some((_, body)) = named_binders(env, &declaration.ty)
                    .map_err(|error| fail(format!("无法解析全称公理 `{axiom}` 的类型：{error}")))?
                else {
                    return Err(fail(format!(
                        "{label}侧引用的 `{axiom}` 的类型不是带命名绑定变量的全称命题"
                    )));
                };
                let Some(axiom_head) = closure::concrete_head(env, &body).map_err(fail)? else {
                    // The body's head is not concrete (for example a
                    // proposition-valued variable), so head agreement cannot
                    // be judged. Stay conservative.
                    continue;
                };
                let Some(proposition_head) =
                    closure::concrete_head(env, &Expr::from(proposition)).map_err(fail)?
                else {
                    continue;
                };
                if axiom_head != proposition_head {
                    return Err(fail(format!(
                        "全称公理 `{axiom}` 的命题体头是 `{axiom_head}`，\
                         而{label}侧冲突命题的头是 `{proposition_head}`"
                    )));
                }
            }
            Provenance::Interpretation { interpretation } => {
                let Some(entry) = cert.interpretations.get(*interpretation) else {
                    return Err(fail(format!(
                        "{label}侧记录为解释推出，但证书只有 {} 条解释，没有第 {interpretation} 条",
                        cert.interpretations.len()
                    )));
                };
                let proposition_expr = Expr::from(proposition);
                let to = Expr::from(&entry.to);
                let same =
                    convertible(env, &Ctx::new(), &to, &proposition_expr).map_err(|error| {
                        fail(format!("无法判定{label}侧命题是否等于解释的 to：{error}"))
                    })?;
                if !same {
                    return Err(fail(format!(
                        "{label}侧命题「{}」与解释 `{}` 的 to「{}」在内核下不等价",
                        print_expr(&proposition_expr),
                        entry.id,
                        print_expr(&to)
                    )));
                }
                // A proposition is one thing: a side recorded as licensed by
                // an interpretation cannot also be an assumed fact or an
                // environment fact. The reasoner never produces that
                // combination, so it is a hand-edited record.
                for assumption in &cert.assumptions {
                    let same = assumption.proposition == *proposition
                        || convertible(
                            env,
                            &Ctx::new(),
                            &Expr::from(&assumption.proposition),
                            &proposition_expr,
                        )
                        .map_err(|error| {
                            fail(format!(
                                "无法判定{label}侧命题是否与证书假设表等价：{error}"
                            ))
                        })?;
                    if same {
                        return Err(fail(format!(
                            "{label}侧命题「{}」已作为事实列在假设表里，不能同时记为解释推出",
                            print_expr(&proposition_expr)
                        )));
                    }
                }
                let proposition_key = key(env, &proposition_expr).map_err(fail)?;
                for fact in facts {
                    if !fact.identity.seeds_derivation() {
                        continue;
                    }
                    let same = fact.key == proposition_key
                        || convertible(env, &Ctx::new(), &fact.proposition, &proposition_expr)
                            .map_err(|error| {
                                fail(format!(
                                    "无法判定{label}侧命题是否与环境中事实 `{}` 等价：{error}",
                                    fact.name
                                ))
                            })?;
                    if same {
                        return Err(fail(format!(
                            "{label}侧命题「{}」已在环境中登记为事实，不能同时记为解释推出",
                            print_expr(&proposition_expr)
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

/// Validate one recorded conflict resolution against the environment and the
/// assumptions' identities, and return how many priority edges it compared.
///
/// A fact identity decides whether a fact can win: only a strict fact
/// (`verified` or `stipulated`) defeats a rule conclusion or a claim, while a
/// claim (`user_asserted` or `assumed`) never does. The records the reasoner
/// writes follow that matrix; a hand-edited certificate that claims otherwise
/// is rejected here rather than read as a legal adjudication.
fn validate_resolution(
    priority: &PriorityGraph,
    cert: &Certificate,
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
                let (winner_prop, loser_prop) = proposition_by_side(conflict, *winner);
                let winner_identity =
                    recorded_identity(cert, *winner, winner_prop).map_err(fail)?;
                if !is_strict(winner_identity) {
                    return Err(fail(format!(
                        "以严格事实为裁决依据，但胜方（{}）登记为{}，不是严格事实",
                        side_label(*winner),
                        winner_identity.label_zh()
                    )));
                }
                // A fact loser must be a claim: two strict facts have no order
                // between them, so that conflict stays unresolved. A rule
                // loser is the ordinary strict-fact-beats-defeasible case.
                if matches!(loser_by, Provenance::Assumption) {
                    let loser_side = match winner {
                        Side::Left => Side::Right,
                        Side::Right => Side::Left,
                    };
                    let loser_identity =
                        recorded_identity(cert, loser_side, loser_prop).map_err(fail)?;
                    if is_strict(loser_identity) {
                        return Err(fail(
                            "两侧都是严格事实：严格事实之间没有先后，不能判出一方胜出".to_owned(),
                        ));
                    }
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
                    return Err(fail(
                        "记录为事实之间的未决冲突，但至少一侧不是假设".to_owned(),
                    ));
                }
                let left = recorded_identity(cert, Side::Left, &conflict.left).map_err(fail)?;
                let right = recorded_identity(cert, Side::Right, &conflict.right).map_err(fail)?;
                // Two strict facts have no order between them, and two claims
                // are both unproved. A strict fact against a claim is decided
                // by the strict fact and must be recorded as a defeat.
                if is_strict(left) != is_strict(right) {
                    return Err(fail(format!(
                        "记录为事实之间的未决冲突，但左侧登记为{}、右侧登记为{}：\
                         严格事实应当胜出",
                        left.label_zh(),
                        right.label_zh()
                    )));
                }
                Ok(0)
            }
            UnresolvedReason::NonStrictFact { identity } => {
                // The reason is about one claim facing one conclusion: a rule
                // application or an interpretation application.
                let (fact_side, fact_prop) = match (&conflict.left_by, &conflict.right_by) {
                    (
                        Provenance::Assumption,
                        Provenance::Rules { .. }
                        | Provenance::Axiom { .. }
                        | Provenance::Interpretation { .. },
                    ) => (Side::Left, &conflict.left),
                    (
                        Provenance::Rules { .. }
                        | Provenance::Axiom { .. }
                        | Provenance::Interpretation { .. },
                        Provenance::Assumption,
                    ) => (Side::Right, &conflict.right),
                    _ => {
                        return Err(fail(
                            "记录为未经证明的主张与规则、公理或解释结论之间的未决冲突，\
                             但两侧必须一侧是事实、另一侧是规则、公理或解释"
                                .to_owned(),
                        ));
                    }
                };
                // A claim never defeats a rule conclusion, and a rule
                // conclusion never proves a claim false. Only a claim may be
                // recorded under this reason; the identity the reason names
                // must be the one the assumption table records, so the
                // certificate cannot label a strict fact as merely asserted.
                if !matches!(
                    *identity,
                    FactIdentity::UserAsserted | FactIdentity::Assumed
                ) {
                    return Err(fail(format!(
                        "记录为未经证明的主张，但记录的身份是{}：\
                         该原因只记录 user_asserted 或 assumed",
                        identity.label_zh()
                    )));
                }
                let recorded = recorded_identity(cert, fact_side, fact_prop).map_err(fail)?;
                if recorded != *identity {
                    return Err(fail(format!(
                        "记录的身份是{}，而假设表把该命题登记为{}",
                        identity.label_zh(),
                        recorded.label_zh()
                    )));
                }
                Ok(0)
            }
            UnresolvedReason::UnknownWitnesses => {
                // A fact can never leave a conflict unresolved for want of
                // rule witnesses: a strict fact wins, and a claim facing a
                // rule conclusion is recorded as `non_strict_fact`. The same
                // holds for an interpretation witness, which is never a lost
                // rule list.
                if matches!(conflict.left_by, Provenance::Assumption)
                    || matches!(conflict.right_by, Provenance::Assumption)
                {
                    return Err(fail(
                        "一侧是事实时，只能是事实胜出或主张未决，不能记录为见证无法重建".to_owned(),
                    ));
                }
                if matches!(conflict.left_by, Provenance::Interpretation { .. })
                    || matches!(conflict.right_by, Provenance::Interpretation { .. })
                {
                    return Err(fail(
                        "一侧是解释推出的结论时，解释见证就是解释声明，不能记录为见证无法重建"
                            .to_owned(),
                    ));
                }
                if matches!(conflict.left_by, Provenance::Axiom { .. })
                    || matches!(conflict.right_by, Provenance::Axiom { .. })
                {
                    return Err(fail(
                        "一侧是公理实例时，见证就是那条全称公理，不能记录为见证无法重建".to_owned(),
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
                let no_declared_order =
                    matches!(conflict.left_by, Provenance::Interpretation { .. })
                        || matches!(conflict.right_by, Provenance::Interpretation { .. })
                        || matches!(conflict.left_by, Provenance::Axiom { .. })
                        || matches!(conflict.right_by, Provenance::Axiom { .. });
                if no_declared_order {
                    // A priority orders rules only, so no declared edge can
                    // involve an interpretation or a universal instance. A
                    // fact side, however, must be recorded as a defeat or as
                    // `non_strict_fact`.
                    if matches!(conflict.left_by, Provenance::Assumption)
                        || matches!(conflict.right_by, Provenance::Assumption)
                    {
                        return Err(fail(
                            "一侧是事实、另一侧是解释或公理实例时，应记录事实胜出或主张未决，\
                             不能记录为没有优先关系"
                                .to_owned(),
                        ));
                    }
                    return Ok(0);
                }
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

/// The two sides' propositions, winner first.
fn proposition_by_side(conflict: &Conflict, winner: Side) -> (&CertExpr, &CertExpr) {
    match winner {
        Side::Left => (&conflict.left, &conflict.right),
        Side::Right => (&conflict.right, &conflict.left),
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

/// Every environment fact whose declared type is a proposition, keyed by its
/// normalized form.
///
/// A `Fact` asserts a proposition; its identity decides whether it seeds a
/// derivation, exactly as in `Reasoner::assume_ledger_axioms`. A `Disputed`
/// fact asserts only what the other side claims, so it is not a proved
/// proposition and must not block a step here. `Axiom` declarations
/// (`axiom 假 : Prop`) only name a proposition constant and are skipped. The
/// kernel's inference decides the sort; the name is never guessed at.
fn environment_propositions(env: &Env) -> Result<BTreeMap<String, Expr>, CheckError> {
    let mut facts = BTreeMap::new();
    for fact in environment_facts(env)? {
        if !fact.identity.seeds_derivation() {
            continue;
        }
        facts.insert(fact.key, fact.proposition);
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
        Node::InterpretationApplication { conclusion, .. } => Some(conclusion),
        Node::AxiomInstance { conclusion, .. } => Some(conclusion),
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
