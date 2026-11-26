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
//! A *statement* is a node on the root's proof graph whose proposition states an
//! open concept. There are two kinds of statements, and only one requires a
//! remaining human judgement:
//!
//! * a `rule_application` or `axiom_instance` whose conclusion's predicate head
//!   is an open concept — the derivation invented the concept from premises, so
//!   it made the judgement itself;
//! * an `interpretation_application` whose conclusion is an open concept —
//!   **exempt**, see below.
//!
//! The root node itself counts when the root proposition is an open concept,
//! even if the root is an assumed fact: asking "prove 重大 甲" must not read as
//! an unconditional proof of 「重大」. An assumption node other than the root is
//! never a statement: a fact the user or the court supplied is evidence, not a
//! booleanization of the concept. That is why a rule that *consumes* an open
//! concept already supplied as a fact leaves the root untouched. The judgement
//! propagates along the proof graph from the root and nowhere else: a rule that
//! derives an open concept on an unrelated branch does not become an obligation
//! of the requested conclusion.
//!
//! ## Interpretation applications release the obligation
//!
//! An `interpret` declaration is the project's explicit representation of a
//! human reading: it has an id, a direction, a `from → to` claim and recorded
//! sources, and it is enabled by the user, never by the loader. Enabling one and
//! deriving the open concept through its application **is** the human
//! judgement, so the obligation is released: the `interpretation_application`
//! node is not a dependency. The release is evidence-bound, not a global
//! switch — the node has to be on the root's proof graph, and a concept the
//! proof states through a rule, a universal instance or the root assumption
//! still produces the obligation. Dropping the interpretation step from a
//! certificate therefore makes the obligation reappear, and the checker
//! recomputes exactly this judgement.
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
//! certificate root derivation, when at least one non-exempt statement remains.
//! Its id is stable ([`OPEN_CONCEPT_OBLIGATION_ID`]), its description names the
//! remaining concepts, and its `nodes` list holds exactly those dependency
//! nodes, sorted ascending. Because only direct dependency nodes are listed, the
//! list is bounded by the proof itself and never by the whole environment.
//!
//! [`statements`] is the unfiltered walk shared by the obligation and the
//! command layer: `:branches` offers the other declared interpretations for
//! every open concept the proof states, including one an enabled
//! interpretation already licensed.

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

/// One node on the root's proof graph whose proposition states an open concept.
///
/// An interpretation application is included here even though it releases the
/// obligation: the concept is still stated by the proof, and the command layer
/// uses this list to offer the other declared interpretations as branches.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenStatement {
    /// The node that states the concept.
    pub node: NodeId,
    /// The open concept predicate the node's proposition has as its head.
    pub concept: Name,
    /// The proposition itself; callers print it or compare it by kernel key.
    pub proposition: CertExpr,
}

/// The open concepts a certificate's root derivation turns into proved
/// propositions, and the proof nodes that state them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenConceptDependency {
    /// The open concept predicate names that still need a human judgement,
    /// sorted, so the obligation text does not depend on the order the concepts
    /// appear in the proof. A concept an interpretation licensed is not here.
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

/// Every open-concept statement on the root's proof graph, deduplicated and
/// sorted by node id.
///
/// This is the raw walk: interpretation applications are included. [`dependency`]
/// filters out the nodes that release the obligation; the command layer uses
/// this list to name every concept the proof states, including one that was
/// already licensed.
///
/// The judgement is the same one `cert::check` recomputes: a certificate whose
/// root is a gap states nothing, and an out-of-range node reference is an
/// error naming the node, never an empty list.
pub fn statements(
    env: &Env,
    certificate: &Certificate,
) -> Result<Option<Vec<OpenStatement>>, String> {
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
    let mut found: Vec<(NodeId, Name)> = Vec::new();
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
                // Only the root of a proof graph states the concept in its own
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
                        found.push((id, concept));
                    }
                }
            }
            Node::RuleApplication {
                conclusion,
                premises,
                ..
            } => {
                if let Some(concept) = open_head(env, conclusion, &open)? {
                    found.push((id, concept));
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
                    found.push((id, concept));
                }
                if *premise >= certificate.nodes.len() {
                    return Err(format!(
                        "节点 {id}：前提 {premise} 越界：证书只有 {} 个节点",
                        certificate.nodes.len()
                    ));
                }
                pending.push(*premise);
            }
            // Universal elimination derives a proposition from a declared
            // universal fact. When that proposition states an open concept, the
            // step turned it into a proved statement, exactly like a rule
            // application; it has no premise node.
            Node::AxiomInstance { conclusion, .. } => {
                if let Some(concept) = open_head(env, conclusion, &open)? {
                    found.push((id, concept));
                }
            }
            // A gap can never be a premise of a proving step; nothing below
            // the root is expanded through it.
            Node::Gap { .. } => {}
        }
    }
    if found.is_empty() {
        return Ok(None);
    }
    found.sort_by_key(|(node, _)| *node);
    found.dedup_by_key(|(node, _)| *node);
    let statements = found
        .into_iter()
        .map(|(node, concept)| {
            let proposition = certificate
                .node_proposition(node)
                .map_err(|error| format!("节点 {node}：{error}"))?
                .clone();
            Ok(OpenStatement {
                node,
                concept,
                proposition,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(Some(statements))
}

/// Recompute the open-concept dependency of a certificate from the environment
/// and the proof graph alone.
///
/// This is the one judgement both the certificate builder and
/// [`crate::check`] use: the builder records the obligation, the checker
/// recomputes it and refuses a certificate that dropped, invented or edited it.
///
/// An interpretation application releases the obligation — enabling a sourced
/// interpretation is the explicit human reading — so its node is not a
/// dependency and its concept is not named. Every other statement (a rule, a
/// universal instance, the root assumption) still needs a human judgement. A
/// certificate with no remaining statement yields `None` — including one whose
/// environment has no `open` marker and one whose open concept an enabled
/// interpretation licensed.
pub fn dependency(
    env: &Env,
    certificate: &Certificate,
) -> Result<Option<OpenConceptDependency>, String> {
    let Some(statements) = statements(env, certificate)? else {
        return Ok(None);
    };
    let mut concepts: BTreeSet<Name> = BTreeSet::new();
    let mut nodes: Vec<NodeId> = Vec::new();
    for statement in statements {
        // Enabling a sourced interpretation and deriving the concept through
        // its application is the human judgement itself; the obligation is
        // released. The release is keyed on the node actually being on the
        // root's proof graph, so dropping that step makes it reappear.
        if matches!(
            certificate.nodes.get(statement.node),
            Some(Node::InterpretationApplication { .. })
        ) {
            continue;
        }
        concepts.insert(statement.concept);
        nodes.push(statement.node);
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
