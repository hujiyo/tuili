//! The certificate data model.
//!
//! Node references are zero-based indices into [`Certificate::nodes`]. The
//! same convention is used by [`Certificate::root`] and
//! [`OpenObligation::nodes`]. The data model does not validate any index;
//! [`crate::check`] validates the proof's node references.

use serde::de::Error as _;
use serde::{Deserialize, Serialize};

use crate::environment::EnvironmentIdentity;
use crate::expr::CertExpr;
use crate::source::Source;
use crate::version::FormatVersion;

/// A zero-based index into [`Certificate::nodes`].
pub type NodeId = usize;

/// A proof certificate.
///
/// The JSON object has exactly the fields below, in this order:
/// `format_version`, `environment`, `assumptions`, `nodes`, `root`,
/// `conflicts`, `open_obligations`, `metadata`. Unknown fields are rejected.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Certificate {
    /// The format version. Only [`FormatVersion::CURRENT`] deserializes.
    pub format_version: FormatVersion,
    /// The environment identity the certificate was produced in. Mandatory:
    /// a certificate cannot be exported without one.
    pub environment: EnvironmentIdentity,
    /// Assumptions used by the derivation, including their provenance and
    /// label. [`Node::Assumption`] refers to entries here by index.
    #[serde(default)]
    pub assumptions: Vec<Assumption>,
    /// The proof graph, in dependency order.
    pub nodes: Vec<Node>,
    /// The node that proves the requested conclusion. `null` means the
    /// certificate has no single root (for example a gap-only certificate).
    pub root: Option<NodeId>,
    /// Conflicts found while deriving, including defeated ones.
    #[serde(default)]
    pub conflicts: Vec<Conflict>,
    /// Items that are unresolved or require human judgement.
    #[serde(default)]
    pub open_obligations: Vec<OpenObligation>,
    /// Generation information. Optional; all of its fields are optional.
    #[serde(default)]
    pub metadata: Metadata,
}

impl Certificate {
    /// Serialize as compact JSON.
    pub fn to_json(&self) -> serde_json::Result<String> {
        serde_json::to_string(self)
    }

    /// Serialize as indented JSON.
    pub fn to_json_pretty(&self) -> serde_json::Result<String> {
        serde_json::to_string_pretty(self)
    }

    /// Stamp the environment identity, replacing whatever the reasoner left.
    ///
    /// The reasoner produces an [`EnvironmentIdentity::Unrecorded`] certificate
    /// because it has no access to the pack registry or corpus; the CLI calls
    /// this before exporting so an unrecorded certificate can never reach disk.
    pub fn with_environment(mut self, environment: EnvironmentIdentity) -> Self {
        self.environment = environment;
        self
    }

    /// Parse JSON, rejecting an unknown or missing `format_version`.
    ///
    /// The version is probed first, using only the `format_version` field, so a
    /// version 2 certificate reports the version error rather than the
    /// `environment` field it could not have written. A fully parsed
    /// certificate's environment record is then validated, so an exporter
    /// cannot hand out duplicate pack names or a malformed corpus hash.
    pub fn from_json(text: &str) -> serde_json::Result<Self> {
        #[derive(Deserialize)]
        struct FormatProbe {
            #[serde(rename = "format_version")]
            _format_version: FormatVersion,
        }

        let _: FormatProbe = serde_json::from_str(text)?;
        let certificate: Self = serde_json::from_str(text)?;
        certificate
            .environment
            .validate()
            .map_err(serde_json::Error::custom)?;
        Ok(certificate)
    }
}

/// An assumption the derivation relies on.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Assumption {
    /// The assumed proposition.
    pub proposition: CertExpr,
    /// Where the assumption comes from. An empty list means the certificate
    /// records no source; it does not mean the assumption is self-evident.
    #[serde(default)]
    pub sources: Vec<Source>,
    /// A human-readable label, for example a fact-ledger identifier.
    #[serde(default)]
    pub label: Option<String>,
}

/// One node of the proof graph.
///
/// The `kind` tag is stable: `assumption`, `rule_application`, `gap`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Node {
    /// A use of [`Assumption`] at the given index.
    Assumption {
        /// Zero-based index into [`Certificate::assumptions`].
        assumption: usize,
    },
    /// One instantiation of a rule.
    RuleApplication {
        /// The rule constant's name in the environment.
        rule: String,
        /// The instantiated conclusion.
        conclusion: CertExpr,
        /// The nodes proving the rule's premises, in the rule's premise order.
        premises: Vec<NodeId>,
        /// The parameter bindings that produced this instance, available to a
        /// checker without parsing the rendering of the instance.
        bindings: Vec<Binding>,
        /// Where the applied rule comes from.
        #[serde(default)]
        sources: Vec<Source>,
    },
    /// An unclosed goal: the explicit replacement for `sorry`.
    Gap {
        /// The proposition that could not be proved.
        proposition: CertExpr,
        /// Rules that could have concluded it, with what they lack.
        #[serde(default)]
        candidates: Vec<GapCandidate>,
        /// A human-readable explanation of the gap.
        #[serde(default)]
        note: Option<String>,
    },
}

/// One parameter binding of a rule instance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Binding {
    /// The rule parameter's name.
    pub parameter: String,
    /// The value the parameter was bound to.
    pub value: CertExpr,
}

/// A rule that could have proved a gap, and why it did not.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GapCandidate {
    /// The candidate rule constant.
    pub rule: String,
    /// Premises that are not known.
    #[serde(default)]
    pub missing: Vec<CertExpr>,
    /// `unless` conditions that already hold, blocking this rule.
    #[serde(default)]
    pub blocked_by: Vec<CertExpr>,
    /// Where the candidate rule comes from.
    #[serde(default)]
    pub sources: Vec<Source>,
}

/// Where a conflicting conclusion came from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Provenance {
    /// The conclusion is an assumption.
    Assumption,
    /// The conclusion was derived by these rules. An empty list means it was
    /// derived but its witnesses can no longer be rebuilt.
    Rules { rules: Vec<String> },
}

/// How a conflict was adjudicated.
///
/// A defeated conflict records its basis: an assumption outranking a
/// defeasible conclusion, or the declared priority edges that decided it. An
/// unresolved conflict records why nobody won.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Resolution {
    /// One side wins.
    Defeated {
        /// The winning side.
        winner: Side,
        /// Why that side wins.
        basis: ResolutionBasis,
    },
    /// No side wins; neither conclusion is asserted.
    Unresolved {
        /// Why the conflict could not be decided.
        reason: UnresolvedReason,
    },
}

/// Why the winning side of a defeated conflict wins.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ResolutionBasis {
    /// A strict fact (assumption) outranks a defeasible conclusion.
    Assumption,
    /// Declared priority edges decide the conflict.
    Priority {
        /// The edges that establish the win, in the reasoner's certificate
        /// order.
        edges: Vec<PriorityEdge>,
    },
}

/// One declared priority edge: `winner` outranks `loser`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PriorityEdge {
    /// The rule that outranks the other.
    pub winner: String,
    /// The rule that is outranked.
    pub loser: String,
    /// Where the declaration comes from.
    pub origin: PriorityOrigin,
}

impl PriorityEdge {
    /// A stable sort key: `(winner, loser, origin_kind,
    /// declared_in_or_rule, clause)`, with a top-level declaration before a
    /// rule-internal clause and `prefer` before `defeated_by`.
    pub fn sort_key(&self) -> (String, String, u8, String, u8) {
        match &self.origin {
            PriorityOrigin::PriorityDeclaration { declared_in, .. } => (
                self.winner.clone(),
                self.loser.clone(),
                0,
                declared_in.clone(),
                0,
            ),
            PriorityOrigin::RuleClause {
                declaring_rule,
                clause,
                ..
            } => (
                self.winner.clone(),
                self.loser.clone(),
                1,
                declaring_rule.clone(),
                match clause {
                    PriorityClause::Prefer => 0,
                    PriorityClause::DefeatedBy => 1,
                },
            ),
        }
    }
}

/// Where a [`PriorityEdge`] comes from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum PriorityOrigin {
    /// A top-level `priority … over …` declaration of a module.
    PriorityDeclaration {
        /// The namespace that asserted the priority.
        declared_in: String,
        /// The declaration's sources, in declaration order.
        sources: Vec<Source>,
    },
    /// A rule-internal `defeated_by` / `prefer` clause.
    RuleClause {
        /// The rule whose declaration carries the clause.
        declaring_rule: String,
        /// Which clause produced the edge.
        clause: PriorityClause,
        /// The declaring rule's sources, in declaration order.
        rule_sources: Vec<Source>,
    },
}

/// Which rule-internal clause produced a [`PriorityEdge`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PriorityClause {
    /// `prefer X`: the declaring rule beats `X`.
    Prefer,
    /// `defeated_by X`: `X` beats the declaring rule.
    DefeatedBy,
}

/// Why a conflict has no winner.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum UnresolvedReason {
    /// Both sides are strict facts; neither outranks the other.
    ConflictingAssumptions,
    /// One side was derived but its witnesses can no longer be rebuilt, so no
    /// priority can be checked for it. Neither side wins.
    UnknownWitnesses,
    /// The rules of the two sides have no declared priority between them.
    NoPriority,
    /// Priorities are declared between the two sides, but they do not decide
    /// the conflict: coverage is incomplete, both directions are covered, or
    /// the edges lie on a priority cycle.
    PriorityUnusable {
        /// Every declared edge between the two sides, in both directions.
        declared: Vec<PriorityEdge>,
    },
}

/// Which side of a conflict a proposition sits on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Side {
    Left,
    Right,
}

/// A recorded conflict between two conclusions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Conflict {
    pub left: CertExpr,
    pub right: CertExpr,
    pub left_by: Provenance,
    pub right_by: Provenance,
    pub resolution: Resolution,
}

/// An item the certificate does not settle.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OpenObligation {
    /// A stable identifier for the obligation.
    pub id: String,
    pub kind: ObligationKind,
    /// What is unresolved or needs a decision.
    pub description: String,
    /// Nodes this obligation relates to, if any.
    #[serde(default)]
    pub nodes: Vec<NodeId>,
}

/// Why an obligation is open.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObligationKind {
    /// A premise could not be proved.
    MissingPremise,
    /// A declaration lacks a citation.
    MissingSource,
    /// An open legal concept needs an interpretation (`合理`, `重大`, ...).
    OpenConcept,
    /// A conflict has no winner.
    UnresolvedConflict,
    /// A human must decide something the logic cannot.
    NeedsHumanDetermination,
    /// Anything else; `description` carries the detail.
    Other,
}

/// Generation information attached to a certificate.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Metadata {
    /// When the certificate was generated, ideally RFC 3339.
    #[serde(default)]
    pub generated_at: Option<String>,
    /// Name of the generating tool.
    #[serde(default)]
    pub tool: Option<String>,
    /// Version of the generating tool.
    #[serde(default)]
    pub tool_version: Option<String>,
}
