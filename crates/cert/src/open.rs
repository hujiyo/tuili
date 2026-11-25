//! Which open concepts a derivation turns into proved propositions.
//!
//! An `open` marker ([`std_deduce_kernel::env::DeclKind::OpenConcept`],
//! [`std_deduce_kernel::Env::open_predicates`]) records that a predicate such as
//! 「重大」 or 「情节严重」 needs a human judgement. The marker asserts nothing
//! and seeds no derivation, but a proof that concludes such a predicate has
//! decided the concept by treating it as an ordinary boolean. This module names
//! the proof steps that do so and turns them into one certificate obligation, so
//! a derivation over an open concept is never reported as an unconditional
//! proof.
//!
//! ## The judgement
//!
//! A *dependency* is a node on the root's proof graph that states an open
//! concept:
//!
//! * a `rule_application` whose conclusion's predicate head is an open concept
//!   (the step that turns premises into the open proposition);
//! * an `interpretation_application` with such a conclusion — it is likewise a
//!   step that licenses the open proposition;
//! * the root node itself when the root proposition is an open concept, even if
//!   the root is an assumed fact or a closed rule conclusion: asking "prove
//!   重大 甲" must not read as an unconditional proof of 「重大」.
//!
//! An assumption node other than the root is never a dependency: a fact the user
//! or the court supplied is evidence, not a booleanization of the concept. That
//! is why a rule that *consumes* an open concept already supplied as a fact
//! leaves the root untouched. The judgement propagates along the proof graph
//! from the root and nowhere else: a rule that derives an open concept on an
//! unrelated branch does not become an obligation of the requested conclusion.
//!
//! The predicate head is read from the kernel term, never from printed text: the
//! node's proposition is normalized in the environment (beta, `def` and zeta stay
//! the only reductions — a predicate is opaque, so a `def` alias of an open
//! predicate is still recognized) and its head constant is compared with
//! [`std_deduce_kernel::Env::open_predicates`].
//!
//! A certificate whose root is a gap proves nothing, so it records no
//! open-concept obligation: the missing-premise obligation already says the
//! conclusion was not established.
//!
//! ## The obligation
//!
//! One [`OpenObligation`] of kind [`ObligationKind::OpenConcept`] is recorded per
//! certificate root derivation. Its id is stable ([`OPEN_CONCEPT_OBLIGATION_ID`]),
//! its description names every concept on the root's proof graph, and its
//! `nodes` list holds exactly the dependency nodes, sorted ascending. Because
//! only direct dependency nodes are listed, the list is bounded by the proof
//! itself and never by the whole environment.

use std::collections::BTreeSet;

use std_deduce_kernel::env::escape_control;
use std_deduce_kernel::norm::normalize;
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{Ctx, Env, Expr, Name};

use crate::expr::CertExpr;
use crate::model::{Certificate, Node, NodeId, ObligationKind, OpenObligation};

/// The stable identifier of the single open-concept obligation a certificate
/// records. It does not depend on node indices or on the order packages loaded
/// in: there is exactly one root derivation per certificate.
pub const OPEN_CONCEPT_OBLIGATION_ID: &str = "open-concept";

/// The open concepts a certificate's root derivation turns into proved
/// propositions, and the proof nodes that state them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenConceptDependency {
    /// The open concept predicate names, sorted, so the obligation text does not
    /// depend on the order the concepts appear in the proof.
    pub concepts: Vec<Name>,
    /// The dependency nodes, sorted ascending. Bounded by the number of proof
    /// nodes: only direct dependency nodes are listed.
    pub nodes: Vec<NodeId>,
}

impl OpenConceptDependency {
    /// The obligation this dependency is recorded as.
    pub fn obligation(&self) -> OpenObligation {
        let names = self
            .concepts
            .iter()
            .map(|concept| format!("`{}`", escape_control(concept)))
            .collect::<Vec<_>>()
            .join("、");
        OpenObligation {
            id: OPEN_CONCEPT_OBLIGATION_ID.to_owned(),
            kind: ObligationKind::OpenConcept,
            description: format!("开放概念 {names} 需要人判断，不得当作已证明"),
            nodes: self.nodes.clone(),
        }
    }
}

/// Recompute the open-concept dependency of a certificate from the environment
/// and the proof graph alone.
///
/// This is the one judgement both the certificate builder and
/// [`crate::check`] use: the builder records the obligation, the checker
/// recomputes it and refuses a certificate that dropped, invented or edited it.
/// A certificate that depends on no open concept yields `None` — including one
/// whose environment has no `open` marker at all.
pub fn dependency(
    env: &Env,
    certificate: &Certificate,
) -> Result<Option<OpenConceptDependency>, String> {
    let open: BTreeSet<Name> = env.open_predicates().into_iter().collect();
    if open.is_empty() {
        return Ok(None);
    }
    let Some(root) = certificate.root else {
        return Ok(None);
    };
    let root_node = certificate.nodes.get(root).ok_or_else(|| {
        format!(
            "根节点索引 {root} 越界：证书只有 {} 个节点",
            certificate.nodes.len()
        )
    })?;
    // A gap proves nothing, so it cannot have decided an open concept.
    if matches!(root_node, Node::Gap { .. }) {
        return Ok(None);
    }

    let mut visited = vec![false; certificate.nodes.len()];
    let mut nodes: Vec<NodeId> = Vec::new();
    let mut concepts: BTreeSet<Name> = BTreeSet::new();
    let mut pending: Vec<NodeId> = vec![root];
    while let Some(id) = pending.pop() {
        if visited[id] {
            continue;
        }
        visited[id] = true;
        let node = certificate.nodes.get(id).ok_or_else(|| {
            format!(
                "节点 {id}：节点索引越界：证书只有 {} 个节点",
                certificate.nodes.len()
            )
        })?;
        match node {
            Node::Assumption { assumption } => {
                // Only the root of a proof graph is a dependency in its own
                // right; a premise fact supplied by the user or the court is
                // evidence, not an open concept the derivation decided.
                if id == root {
                    let entry = certificate.assumptions.get(*assumption).ok_or_else(|| {
                        format!(
                            "节点 {id}：引用了不存在的假设 {assumption}：证书只有 {} 条假设",
                            certificate.assumptions.len()
                        )
                    })?;
                    if let Some(concept) = open_head(env, &entry.proposition, &open)? {
                        concepts.insert(concept);
                        nodes.push(id);
                    }
                }
            }
            Node::RuleApplication {
                conclusion,
                premises,
                ..
            } => {
                if let Some(concept) = open_head(env, conclusion, &open)? {
                    concepts.insert(concept);
                    nodes.push(id);
                }
                for premise in premises {
                    if *premise >= certificate.nodes.len() {
                        return Err(format!(
                            "节点 {id}：前提 {premise} 越界：证书只有 {} 个节点",
                            certificate.nodes.len()
                        ));
                    }
                    pending.push(*premise);
                }
            }
            Node::InterpretationApplication {
                conclusion,
                premise,
                ..
            } => {
                if let Some(concept) = open_head(env, conclusion, &open)? {
                    concepts.insert(concept);
                    nodes.push(id);
                }
                if *premise >= certificate.nodes.len() {
                    return Err(format!(
                        "节点 {id}：前提 {premise} 越界：证书只有 {} 个节点",
                        certificate.nodes.len()
                    ));
                }
                pending.push(*premise);
            }
            // A gap can never be a premise of a proving step; nothing below
            // the root is expanded through it.
            Node::Gap { .. } => {}
        }
    }
    if nodes.is_empty() {
        return Ok(None);
    }
    nodes.sort_unstable();
    nodes.dedup();
    Ok(Some(OpenConceptDependency {
        concepts: concepts.into_iter().collect(),
        nodes,
    }))
}

/// The open concept a proposition states, if its predicate head is one.
///
/// The proposition is normalized first, so a `def` alias that unfolds to an
/// open predicate's application is recognized as the same concept. A head that
/// is not a constant (a bound variable, a quantified form, a sort) is not a
/// declared predicate and is therefore never read as an open concept.
fn open_head(
    env: &Env,
    proposition: &CertExpr,
    open: &BTreeSet<Name>,
) -> Result<Option<Name>, String> {
    let expression = Expr::from(proposition);
    let normalized = normalize(env, &Ctx::new(), &expression).map_err(|error| {
        format!(
            "无法规范化「{}」以判定开放概念：{error}",
            print_expr(&expression)
        )
    })?;
    Ok(normalized.head_const().filter(|head| open.contains(head)))
}
