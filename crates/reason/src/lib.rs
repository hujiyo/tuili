//! The reasoner: forward chaining over defeasible rules, producing
//! *checkable* derivation trees.
//!
//! ## Semantics: least fixed point, not monotone closure
//!
//! The knowledge set is recomputed from the assumptions on every round until
//! it stops changing. This matters because `unless` makes the operator
//! *anti-monotone*: deriving one more fact can retract an earlier conclusion.
//! A one-pass "insert and never remove" loop gets exactly that wrong — it
//! leaves a blocked conclusion standing because it was derived before the
//! blocking fact appeared. The fixed-point formulation retracts it.
//!
//! If the iteration oscillates (two rules each blocked by the other), we
//! report that instead of picking a side.
//!
//! ## Conflict is declared, then adjudicated — never guessed
//!
//! Two predicates can be declared `contrary`, and a predicate can be declared
//! `unique` at an argument position (one case, one applicable norm). When two
//! derived facts fall foul of either declaration, that is a conflict, and it
//! is adjudicated in exactly these ways:
//!
//! * a strict fact (`verified` or `stipulated`) outranks a defeasible
//!   conclusion and a claim (`user_asserted` or `assumed`);
//! * a declared priority between the rules on the two sides decides the
//!   conflict: `defeated_by` / `prefer` inside one package, or a top-level
//!   `priority … over …` declaration with its sources. A priority edge that
//!   lies on a priority cycle cannot decide anything, and priorities are never
//!   transitive: `A over B` and `B over C` do not make `A over C`. Priorities
//!   order rules only: a claim never automatically beats a rule conclusion,
//!   and a rule conclusion never refutes a claim;
//! * otherwise the conflict is unresolved, and **neither** conclusion enters
//!   the fact base. The recorded reason says whether the sides are two strict
//!   facts, two claims, a claim facing a rule conclusion, lack a declared
//!   priority, have priorities that do not cover the conflict (or lie in a
//!   cycle), or whether one side's witnesses can no longer be rebuilt. It is
//!   not silently dropped: `conflicts()` reports it, and the CLI prints both
//!   derivations and exits non-zero.
//!
//! ## Premises and conflicts are compared up to kernel equality
//!
//! A premise pattern is matched against a fact structurally first; when that
//! fails, both sides are normalized once (beta, `def` delta, zeta) and matched
//! again. The derivation and the gap candidates share this one judgment, so a
//! `def` alias can neither make a rule fire silently nor make a candidate
//! report a satisfied premise the fixed point could not consume. For the same
//! reason a `contrary`/`unique` declaration sees the predicate head after the
//! same normalization: a fact or conclusion written through a `def` alias
//! takes part in the conflict its underlying predicate declares. The conflict
//! judgement itself lives in [`std_deduce_cert::conflict::in_conflict`], which
//! both this producer and the certificate checker call: the two never read a
//! conflict under different rules.
//!
//! ## Guards are instance conditions, judged by evaluation
//!
//! A rule may declare `guard` clauses: comparisons over its parameter values
//! that must hold for an instance to fire. A guard is neither a premise nor an
//! `unless`. It is not a proposition a fact could prove, so it is decided by
//! evaluating the comparison against the values the instance binds
//! ([`std_deduce_kernel::norm::evaluate_comparison`]); all guards of one rule
//! are conjunctive, and a `false` guard leaves the instance unfired while the
//! gap report still names it. The order is: guard (is this binding an instance
//! of the rule's own condition?), then `unless` (does an exception hold?),
//! then the temporal/spatial applicability judgement. An overflowing guard, or
//! one whose operands are not integer literals, aborts the reasoning with an
//! explicit error naming the rule and the guard; it is never read as `false`.
//! Each fired instance records the guard judgements it rested on
//! ([`GuardJudgement`]) and the certificate carries them; the certificate
//! checker re-evaluates each record from the rule declaration and the recorded
//! bindings, so a recorded boolean is evidence that can be rechecked, not a
//! claim to be trusted.
//!
//! ## Three commitments
//!
//! 1. **No negation as failure.** A rule fires only when every premise has
//!    been derived, and an `unless P` blocks only when `P` *itself* has been
//!    derived. "We could not prove it, so it is false" is impossible here.
//! 2. **No silent conflict resolution.** A conflict is either defeated or
//!    reported as unresolved; it is never resolved by an internal preference.
//! 3. **No hidden gaps.** An unreachable goal yields a gap node listing the
//!    candidate rules, which premises are missing, and which blocking
//!    conditions already hold. There is no `sorry` equivalent.
//!
//! ## Interpretations are explicit, one-step permissions
//!
//! An `interpret` declaration is inert until the caller enables it (the CLI's
//! `--interpret` / `:interpret enable`). An enabled interpretation applies at
//! most once per query, after the rule fixed point: when its `from` is already
//! a registered fact or a rule conclusion, its `to` joins the fact base as a
//! separate [`Node::InterpretationApplication`]. It never fires a rule, never
//! consumes another interpretation's conclusion, and is never treated as a
//! rule: there is no interpretation chain and no implicit rewriting. A
//! conclusion licensed by an interpretation that takes part in a conflict is
//! recorded as [`Provenance::Interpretation`] — a declaration witness, not a
//! lost rule list; priorities order rules only, so such a conflict is
//! unresolved unless a strict fact wins.
//!
//! Gap diagnostics keep the two stages apart: a rule's premises are judged
//! against the facts and rule conclusions (never against an interpretation
//! conclusion, which rules cannot consume), while whether the queried goal is
//! proved uses the full settled base. The "only an unenabled interpretation is
//! missing" hint likewise covers only the root goal, and only when the
//! interpretation's `from` holds before any application would run.
//!
//! ## Universal facts are instantiated on demand
//!
//! A `Fact` declaration whose type is a telescope of named `∀` binders ending
//! in a predicate-headed proposition is a universal fact. Its instances are
//! derived, never assumed: a closed goal or a rule premise that is already
//! closed under the bindings collected so far supplies one value per binder,
//! and the conclusion is the declaration's body with those values substituted.
//! The search is never an enumeration over objects: candidates are filtered by
//! the normalized predicate head of the goal against the normalized head of
//! each declaration's body, a structural match is attempted first and a
//! normalization fallback after it, and each (declaration, goal) pair is
//! probed once (misses are cached). Binding values must be closed, every binder
//! must be bound, the kernel checks each value against its instantiated binder
//! domain, and a conclusion that is not the substitution of the body is
//! refused.
//!
//! The bounds are explicit constants: [`MAX_AXIOM_CANDIDATES_PER_GOAL`],
//! [`MAX_AXIOM_INSTANCES_PER_QUERY`] and [`MAX_AXIOM_PROBES_PER_QUERY`].
//! Exceeding one is an error naming the bound, never a truncated derivation.
//! Existential quantifiers, polymorphism and higher-order instantiation of
//! function-typed facts are not implemented; a declaration whose body is an
//! implication or a quantified form is not a candidate. An instance that takes
//! part in a conflict is recorded as [`Provenance::Axiom`]: a universal fact is
//! not a rule, so no priority orders it, and a strict fact defeats it exactly
//! as it defeats a rule conclusion; an unresolved conflict stays unresolved.
//!
//! ## Temporal and spatial applicability
//!
//! A rule's recorded scope (`effective` / `repealed` / `jurisdiction` /
//! `territory`) and the occurrence records of the premise facts an instance
//! consumes (`occurred_at` / `occurred_in`) are judged before that instance
//! may fire. The reference point is the event, not the query date: `:asof` is
//! only a fallback when the instance references no event time. [`Applicability`]
//! keeps four outcomes apart: applicable (with the covered event times/places),
//! inapplicable (with the concrete dates/places that excluded the rule),
//! unchecked (a needed input is missing), and undecidable (the inputs are
//! present but the data cannot decide, including partial coverage). An
//! inapplicable instance never fires and never becomes a conflict witness;
//! an unchecked instance (no evidence at all) keeps firing; an undecidable
//! instance (partial evidence) does not fire. Both excluded forms carry their
//! verdict and evidence wherever a rule is shown, so missing input and partial
//! coverage are visible instead of silently ignored.
//!
//! The judgement itself is [`std_deduce_cert::judge_applicability`]: a pure
//! function over the rule's [`Scope`](std_deduce_kernel::meta::Scope) and
//! the instance's anchor (the premise facts' occurrence records plus the
//! session fallback values). The reasoner only supplies those records; the
//! CLI only renders the recorded verdict. Certificate v13 records the verdict,
//! basis, declared scope and reason on every rule application and gap
//! candidate, and `:verify-cert` recomputes them independently.
//!
//! ## Certificates
//!
//! [`certificate`] converts a derivation into the versioned certificate
//! format owned by the `cert` crate. The conversion is structural: node
//! order, premise order, bindings, sources, conflicts and the root are
//! carried over unchanged. It does not decide anything the derivation did
//! not already decide, and it refuses to drop an expression it cannot
//! encode. One derived fact is added: when the root's proof graph turns an
//! `open` concept (`重大`, `情节严重`) into a proved proposition, the
//! certificate records an `open_concept` obligation naming the concepts and
//! the nodes that state them, so an open concept is never exported as an
//! unconditional conclusion. An `interpretation_application` that licenses the
//! concept is exempt: enabling a sourced interpretation is the explicit human
//! reading, so the obligation is released instead.
//!
//! Every conclusion derived by rules or universal elimination keeps all of its
//! independent witnesses. A witness is one rule instance (rule name plus
//! binding values) or one universal instance (axiom name plus binding values);
//! the same argument reached through different premise nodes is still one
//! witness, and premise-level alternatives are recorded under the premise's
//! own conclusion, never multiplied into the parent's witness list. Each
//! conclusion keeps at most
//! [`std_deduce_cert::MAX_CERT_WITNESSES_PER_CONCLUSION`] witnesses; beyond it
//! the group is marked truncated. Rules are enumerated once into a
//! conclusion-keyed witness index (not once per pending conclusion), so a case
//! with many objects and many rules does not become quadratic. The proof graph
//! is built incrementally: a conclusion gets its first node as soon as one
//! witness is ready, and the remaining witnesses join in later rounds. If some
//! witnesses exist but none can make progress, the construction reports the
//! dependency cycle instead of silently dropping the extra arguments.
//! Witnesses sort by rule name and binding
//! structure (universal instances after rules); the first in that order is the
//! main path shown by `root`, which is deterministic but carries no claim of
//! being the most credible argument. Repeated generation of the same case is
//! byte-identical. Keeping them changes neither the fixed point nor conflict
//! adjudication: the same rules win and lose, but both paths stay visible.
//!
//! ## Open concepts are not silently booleanised
//!
//! `open <pred>` is kernel metadata: it seeds no derivation and blocks no `unless`.
//! It is not inert for output, though. A rule step whose conclusion head is an
//! open predicate, or a queried root that is one, depends on a human judgement;
//! the dependency propagates from the root's proof graph and becomes the
//! certificate obligation. A fact the user or the court supplied is evidence,
//! not a decision of the concept, so an open concept that merely appears as an
//! assumption premise is not counted. [`Reasoner::branch_candidates`] names
//! the declared interpretations that could license the blocked concept and
//! says which of them can actually run; the command layer runs each one alone
//! as its own derivation, never as a combination.

mod applicability;
mod branches;

pub use branches::{
    BranchCandidate, BranchCandidateScan, CandidateRelation, EnabledLicense, UnavailableBranch,
    MAX_BRANCH_CANDIDATES,
};

pub use applicability::{
    Applicability, Basis, CodeDimension, DateField, DatedEvidence, InapplicableReason,
    InstanceAnchor, MissingInput, PlaceEvidence, UndecidableReason,
};

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use std_deduce_cert::conflict::{
    in_conflict, view as conflict_view, within_term_limit, ConflictView, Declarations,
};
use std_deduce_cert::CertExpr;
use std_deduce_kernel::conv::convertible;
use std_deduce_kernel::env::{
    named_binders, substitute_pattern_constants, Decl, DeclKind, Env, FactIdentity, OpenPremise,
    PremiseKind, RuleDecl, RulePleading, SourceRef,
};
use std_deduce_kernel::norm::{evaluate_arithmetic, evaluate_comparison, normalize};
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::term::{instantiate_telescope, is_closed};
use std_deduce_kernel::{check, Ctx, Expr, Name, RevisionGroup};

// ---------------------------------------------------------------- nodes

#[derive(Debug, Clone)]
pub enum Node {
    Assumption {
        prop: Expr,
        /// Who asserts the proposition. A strict fact outranks a defeasible
        /// conclusion; a claim does not.
        identity: FactIdentity,
        sources: Vec<SourceRef>,
        label: Option<String>,
        /// The environment fact's recorded `occurred_at`, if any. It is
        /// evidence about the case and travels with the assumption so a
        /// certificate can record it; it is never defaulted.
        occurred_at: Option<String>,
        /// The environment fact's recorded `occurred_in`, if any.
        occurred_in: Option<String>,
    },
    RuleApplication {
        rule: Name,
        conclusion: Expr,
        /// The instance's conclusion exactly as the rule wrote it with the
        /// parameter values substituted, recorded only when the kernel's
        /// arithmetic evaluation changed it. It is the record of the
        /// computation: the certificate checker requires it to be the rule's
        /// own conclusion under the recorded bindings, and the recorded
        /// `conclusion` to be that expression's value. Boxed because a term is
        /// much larger than the other node payloads.
        computed: Option<Box<Expr>>,
        premises: Vec<usize>,
        /// Which branch or witness each compound premise used, one entry per
        /// premise (plain premises carry [`PremiseSelection::Plain`]).
        selections: Vec<PremiseSelection>,
        /// The guard judgements this instance fired under, in the rule's
        /// declaration order. Every one of them holds; the certificate records
        /// each guard's expression, substituted form and truth value, and its
        /// checker re-evaluates them from the declaration and the bindings.
        guard_judgements: Vec<GuardJudgement>,
        /// The rule's parameters and the values this step bound them to.
        bindings: Vec<(Name, Expr)>,
        sources: Vec<SourceRef>,
        /// The temporal/spatial judgement under which this instance fired,
        /// with the event times/places it relied on. The certificate records it
        /// together with the rule's declared scope. Boxed because the node
        /// enum is dominated by this record; the payload is unchanged.
        applicability: Box<Applicability>,
    },
    /// One application of an enabled interpretation. It is a separate step,
    /// never a rule: the declaration licenses the move from `from` to `to`,
    /// and the premise is a registered fact or a rule conclusion (never
    /// another interpretation's conclusion).
    InterpretationApplication {
        interpretation: Name,
        conclusion: Expr,
        premise: usize,
    },
    /// One universal elimination: the declared universal fact `axiom` is
    /// instantiated with the recorded values of its binders. The step has no
    /// premise because the universal statement itself is a declaration, not a
    /// fact of the case; the certificate records the declaration's identity
    /// separately, so the proof never hides whose assertion it rests on.
    AxiomInstance {
        axiom: Name,
        /// The identity of the universal fact the instance rests on.
        identity: FactIdentity,
        /// The binder names and the closed values substituted for them,
        /// outermost binder first.
        bindings: Vec<(Name, Expr)>,
        conclusion: Expr,
        sources: Vec<SourceRef>,
    },
    /// An unclosed goal. The honest replacement for `sorry`.
    Gap {
        prop: Expr,
        candidates: Vec<GapCandidate>,
        /// Universal facts whose body unifies with the goal, with the values
        /// the instance would need and, when no instance was produced, why.
        /// They are diagnostics: an instantiation that succeeded closes the
        /// goal and never leaves a gap.
        axiom_candidates: Vec<AxiomCandidate>,
        note: Option<String>,
    },
}

/// One universal fact that could instantiate a gap goal.
#[derive(Debug, Clone)]
pub struct AxiomCandidate {
    /// The universal fact's declaration name.
    pub axiom: Name,
    /// The binder values the unified instance would use, outermost first.
    pub bindings: Vec<(Name, Expr)>,
    /// Why the instance was not produced, or `None` when it was legal but this
    /// path did not trigger it.
    pub problem: Option<String>,
}

/// One universal elimination step, as the derivation records it.
#[derive(Debug, Clone, PartialEq)]
pub struct AxiomInstance {
    /// The universal fact's declaration name.
    pub axiom: Name,
    /// The identity the universal fact is registered under. It is evidence,
    /// not an assumption: the instantiated conclusion is derived.
    pub identity: FactIdentity,
    /// The binder names and the closed values substituted for them, outermost
    /// binder first.
    pub bindings: Vec<(Name, Expr)>,
    /// The conclusion, which is the declaration's body with the bindings
    /// substituted.
    pub conclusion: Expr,
    pub sources: Vec<SourceRef>,
}

impl AxiomInstance {
    /// A stable order for the steps of one derivation: axiom name, then the
    /// structural keys of the binding values in binder order.
    fn sort_key(&self, env: &Env) -> (String, String) {
        let values = self
            .bindings
            .iter()
            .map(|(parameter, value)| format!("{parameter}={}", key(env, value)))
            .collect::<Vec<_>>()
            .join("，");
        (self.axiom.to_string(), values)
    }
}

#[derive(Debug, Clone)]
pub struct GapCandidate {
    pub rule: Name,
    /// The parameter bindings that produced this candidate instance. A
    /// certificate records them so a checker can re-instantiate the rule's
    /// premises instead of trusting the printed gap tree.
    pub bindings: Vec<(Name, Expr)>,
    /// The rule premises that already hold, in the rule's premise order. Their
    /// propositions are how the certificate checker rebuilds the
    /// applicability anchor from the environment's occurrence records.
    pub held: Vec<Expr>,
    /// Premises that are not known.
    pub missing: Vec<Expr>,
    /// Branch labels parallel to `missing`: `Some(k)` for the k-th written
    /// branch of a failing disjunction, `None` for a plain/existential gap.
    pub missing_branches: Vec<Option<usize>>,
    /// Branch/witness selections of the compound premises that already hold.
    pub choices: Vec<PremiseSelection>,
    /// `unless` conditions that *are* known, i.e. why this rule is blocked.
    pub blocked_by: Vec<Expr>,
    /// The guard judgements of this candidate instance, in declaration order.
    /// A guard that does not hold (or cannot be decided) is recorded here
    /// instead of letting the candidate disappear: `:gap` / `:issues` print the
    /// substituted guard and why it did not let the rule fire.
    pub guards: Vec<GuardJudgement>,
    /// One entry per rule premise, in premise order, with the branch/witness
    /// structure the gap tree and the certificate use. `held`, `missing` and
    /// `choices` are the flattened views of this list.
    pub premises: Vec<PremiseStatus>,
    pub sources: Vec<SourceRef>,
    /// The rule's temporal/spatial judgement for this case. An excluded
    /// candidate is still listed: `:gap` says why it cannot be used instead of
    /// hiding it. Unchecked candidates keep their missing premises and are
    /// expanded; inapplicable/undecidable ones are listed but not expanded,
    /// because adding a premise cannot make an excluded rule fire.
    pub applicability: Applicability,
}

/// One premise's status for a gap candidate or the issue scan.
///
/// A plain premise either holds (its instantiated proposition is in `held`) or
/// is missing (the same proposition is in `missing`). A disjunction that holds
/// records the selected branch; a disjunction that fails fills `missing` with
/// one entry per written branch and `branches` with their indices. An existence
/// that fails fills `missing` with the open body pattern and `exists_candidates`
/// with the declared individuals of its domain (bounded, with an explicit
/// truncation flag); one that holds records the witness.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct PremiseStatus {
    /// The proposition this premise holds, when it holds.
    pub held: Option<Expr>,
    /// The propositions this premise still lacks. For a failing disjunction this
    /// is one entry per branch; for a plain/existential premise it is one entry.
    pub missing: Vec<Expr>,
    /// Which branch or witness the premise used, when it holds.
    pub selection: PremiseSelection,
    /// The written branches, in order, when a disjunction fails. Each carries
    /// its own gap subtree in the rendered tree.
    pub branches: Vec<(usize, Expr)>,
    /// The declared individuals the witness search tried, when an existence
    /// premise has no witness.
    pub exists_candidates: Vec<Expr>,
    /// Whether more declared individuals exist than the display bound.
    pub exists_truncated: bool,
    /// Whether this premise is an existential premise at all (needed even when
    /// its domain has no declared individual: the gap must still say that some
    /// individual has to satisfy the body).
    pub exists: bool,
}

/// The declared individuals of one existential domain, bounded for display.
struct WitnessCandidates {
    items: Vec<Expr>,
    truncated: bool,
}

/// The display bound for candidate individuals in a gap tree.
pub const MAX_GAP_WITNESS_CANDIDATES: usize = 8;

/// Enumerate the declared individuals of a domain for a gap display, keeping at
/// most [`MAX_GAP_WITNESS_CANDIDATES`] and marking truncation explicitly.
fn display_witness_candidates(env: &Env, domain: &Expr) -> Result<WitnessCandidates, String> {
    let mut individuals = declared_individuals(env, domain)?;
    let truncated = individuals.len() > MAX_GAP_WITNESS_CANDIDATES;
    individuals.truncate(MAX_GAP_WITNESS_CANDIDATES);
    Ok(WitnessCandidates {
        items: individuals,
        truncated,
    })
}

#[derive(Debug, Clone, Default)]
pub struct Derivation {
    pub nodes: Vec<Node>,
    pub root: Option<usize>,
    pub conflicts: Vec<Conflict>,
    /// Every derived conclusion with all of its independent witness nodes, in
    /// proposition-key order. The main proof tree follows `root`; this table
    /// records the other arguments that establish the same conclusions.
    pub alternatives: Vec<WitnessGroup>,
    /// The interpretations enabled for this derivation, sorted by id. A
    /// certificate lists only the entries its nodes or conflicts cite.
    pub interpretations: Vec<InterpretationRecord>,
}

/// One derived conclusion and the nodes that each independently derive it.
///
/// The witness nodes are a subset of [`Derivation::nodes`]. A node that is
/// already a premise of the main tree still counts as a witness; the table is
/// what makes a second, third or later argument visible instead of silently
/// dropped by the first one.
#[derive(Debug, Clone, PartialEq)]
pub struct WitnessGroup {
    pub proposition: Expr,
    /// Witness node ids, ordered by the deriving rule's name and the binding
    /// structure of the instance, with universal instances after the rules.
    pub witnesses: Vec<usize>,
    /// More distinct witnesses exist than the per-conclusion bound allows.
    pub truncated: bool,
}

/// One enabled interpretation declaration, as the derivation records it.
///
/// It is declaration data, not a proof step: [`Node::InterpretationApplication`]
/// records where it was applied. The record keeps everything a certificate
/// needs to re-find the declaration in the environment and compare it field by
/// field.
#[derive(Debug, Clone, PartialEq)]
pub struct InterpretationRecord {
    pub id: Name,
    pub from: Expr,
    pub to: Expr,
    pub direction: std_deduce_kernel::InterpretationDirection,
    pub sources: Vec<SourceRef>,
}

/// Which side of a recorded conflict a fact sits on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
    Left,
    Right,
}

/// Where a conflicting conclusion came from. An empty `Rules` list means the
/// conclusion was derived but its witnesses can no longer be rebuilt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Provenance {
    /// The conclusion is a registered assumption; the identity it was
    /// registered under decides whether it wins.
    Assumption,
    Rules(Vec<Name>),
    /// The conclusion was derived by instantiating the named universal fact.
    /// It is a derived conclusion: no identity of the instance itself, and no
    /// priority orders it (a universal fact is not a rule).
    Axiom(Name),
    /// The conclusion was licensed by the named interpretation. It is a
    /// defeasible conclusion, not a fact: no priority orders it, and it never
    /// counts as a lost rule witness.
    Interpretation(Name),
}

/// How a conflict was adjudicated.
///
/// A conflict is never decided by an internal preference: it is either
/// defeated by a declared priority or by the strictness of a fact, or it is
/// reported as unresolved with the reason.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolution {
    /// One side wins.
    Defeated {
        /// The winning side.
        winner: Side,
        /// Why that side wins.
        basis: ResolutionBasis,
    },
    /// No side wins; neither conclusion enters the fact base.
    Unresolved {
        /// Why the conflict could not be decided.
        reason: UnresolvedReason,
    },
}

/// Why the winning side of a defeated conflict wins.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolutionBasis {
    /// A strict fact (an assumption recorded as `verified` or `stipulated`)
    /// outranks a defeasible conclusion or a claim.
    Assumption,
    /// Declared priority edges decide the conflict.
    Priority {
        /// The declared edges that establish the win, sorted by
        /// [`PriorityEdge::sort_key`].
        edges: Vec<PriorityEdge>,
    },
}

/// One declared priority edge: `winner` outranks `loser`.
///
/// An edge records a declaration someone made, not an inference: its origin
/// names who declared it and the sources they cited.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PriorityEdge {
    /// The rule that outranks the other.
    pub winner: Name,
    /// The rule that is outranked.
    pub loser: Name,
    /// Where the declaration comes from.
    pub origin: PriorityOrigin,
}

impl PriorityEdge {
    /// A stable sort key for certificate output.
    ///
    /// The key is `(winner, loser, origin_kind, declared_in_or_rule,
    /// clause)`: a top-level declaration sorts before a rule-internal clause,
    /// and `prefer` before `defeated_by`. Sorting by it makes the order of
    /// recorded edges independent of the order in which packages were loaded.
    pub fn sort_key(&self) -> (String, String, u8, String, u8) {
        let (origin_kind, declared_or_rule, clause) = match &self.origin {
            PriorityOrigin::Declaration { declared_in, .. } => (0, declared_in.to_string(), 0),
            PriorityOrigin::RuleClause {
                rule, clause: c, ..
            } => (
                1,
                rule.to_string(),
                match c {
                    PriorityClause::Prefer => 0,
                    PriorityClause::DefeatedBy => 1,
                },
            ),
        };
        (
            self.winner.to_string(),
            self.loser.to_string(),
            origin_kind,
            declared_or_rule,
            clause,
        )
    }
}

/// Where a [`PriorityEdge`] comes from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PriorityOrigin {
    /// A top-level `priority … over …` declaration of a module.
    Declaration {
        /// The namespace that asserted the priority.
        declared_in: Name,
        /// The declaration's sources, in declaration order.
        sources: Vec<SourceRef>,
    },
    /// A rule-internal `defeated_by` / `prefer` clause. Such an edge can only
    /// order rules of the declaring rule's own package.
    RuleClause {
        /// The rule whose declaration carries the clause.
        rule: Name,
        /// Which clause produced the edge.
        clause: PriorityClause,
        /// The declaring rule's sources, in declaration order.
        sources: Vec<SourceRef>,
    },
}

/// Which rule-internal clause produced a [`PriorityEdge`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PriorityClause {
    /// `prefer X`: the declaring rule beats `X`.
    Prefer,
    /// `defeated_by X`: `X` beats the declaring rule.
    DefeatedBy,
}

/// Why a conflict has no winner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnresolvedReason {
    /// Both sides are facts; neither outranks the other. Two strict facts have
    /// no order between them, and two claims are both unproved.
    ConflictingAssumptions,
    /// A claim met a rule conclusion. The claim is not proof, so it cannot
    /// automatically beat the rule conclusion; the rule conclusion does not
    /// refute the claim either. Neither side wins.
    NonStrictFact {
        /// The identity the claim is recorded under: `user_asserted` or
        /// `assumed`.
        identity: FactIdentity,
    },
    /// One side was derived but its witnesses can no longer be rebuilt
    /// ([`Provenance::Rules`] with an empty list), so no priority can be
    /// checked for it. Neither side wins.
    UnknownWitnesses,
    /// The rules of the two sides have no declared priority between them.
    NoPriority,
    /// Priorities are declared between the two sides, but they do not decide
    /// the conflict: coverage is incomplete, both directions are covered, or
    /// the edges lie on a priority cycle.
    PriorityUnusable {
        /// Every declared edge between the two sides, in both directions,
        /// sorted by [`PriorityEdge::sort_key`].
        declared: Vec<PriorityEdge>,
    },
}

/// The declared priority order of one environment, as computed by a
/// [`Reasoner`].
///
/// It records which rules share a priority cycle. Certificate generation uses
/// it only to describe an unusable priority in human terms: an edge whose two
/// rules sit in the same cycle cannot decide anything.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PriorityOrder {
    components: BTreeMap<Name, u32>,
}

impl PriorityOrder {
    /// Whether `winner` and `loser` sit in the same priority cycle. Two rules
    /// share a component when they are strongly connected, so an edge between
    /// them can never decide a conflict; a name the order does not know is
    /// never in a recorded component.
    pub fn same_cycle(&self, winner: &Name, loser: &Name) -> bool {
        match (self.components.get(winner), self.components.get(loser)) {
            (Some(w), Some(l)) => w == l,
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Conflict {
    pub left: Expr,
    pub right: Expr,
    pub left_by: Provenance,
    pub right_by: Provenance,
    pub resolution: Resolution,
}

/// The revision group containing at least one witness rule of each side of a
/// conflict.
///
/// A `revision` group declares that its rules are versions of one provision
/// (the 1997 and the 2021 version of an article). When two rules of one group
/// conflict, the conflict is between an old and a new version, and the reason
/// text must say so: "no priority was declared" alone leaves a reader unable to
/// tell an ordinary cross-rule conflict from an unresolved choice between two
/// versions. The groups are read from the declarations only; the function never
/// picks a version, and it returns the first shared group in
/// `(namespace, identifier)` order so the text is deterministic.
///
/// `None` means the sides share no group, or at least one side is not a rule
/// side (a fact, a universal instance or an interpretation conclusion).
pub fn shared_revision_group(
    env: &Env,
    left: &Provenance,
    right: &Provenance,
) -> Option<RevisionGroup> {
    let (Provenance::Rules(left), Provenance::Rules(right)) = (left, right) else {
        return None;
    };
    let left_groups: BTreeSet<RevisionGroup> = left
        .iter()
        .filter_map(|rule| env.revision_group_of(rule))
        .collect();
    let right_groups: BTreeSet<RevisionGroup> = right
        .iter()
        .filter_map(|rule| env.revision_group_of(rule))
        .collect();
    left_groups.intersection(&right_groups).next().cloned()
}

/// One unenabled interpretation that would have applied to a queried
/// proposition. The command layer prints these as suggestions; the reasoner
/// never applies them on its own.
#[derive(Debug, Clone, PartialEq)]
pub struct InterpretationHint {
    pub id: Name,
    pub from: Expr,
    pub to: Expr,
}

// ---------------------------------------------------------------- internals

/// One registered fact's occurrence record: `occurred_at`, `occurred_in`.
type OccurrenceRecord = (Option<String>, Option<String>);
/// Registered facts' occurrence records keyed by structural proposition key.
type OccurrenceIndex = BTreeMap<String, Vec<OccurrenceRecord>>;

struct Assumption {
    prop: Expr,
    identity: FactIdentity,
    sources: Vec<SourceRef>,
    label: Option<String>,
    /// First day the fact occurred, copied from the ledger declaration. A
    /// reasoner assumption registered by hand has none, so a missing
    /// occurrence is not invented from the query date.
    occurred_at: Option<String>,
    /// Place the fact occurred in, copied from the ledger declaration.
    occurred_in: Option<String>,
}

/// One guard of a rule instance, as the reasoner judged it.
///
/// A guard is an *instance condition*: a comparison over the values the
/// instance binds. It is not a premise — nothing proves it — and it is not an
/// `unless`: a guard that holds lets the rule fire, while an `unless` that
/// holds blocks it. All guards of one rule are conjunctive.
#[derive(Debug, Clone, PartialEq)]
pub struct GuardJudgement {
    /// Zero-based index in the rule's `guard` clauses, in declaration order.
    pub index: usize,
    /// The guard closed by the instance's bindings, before evaluation, e.g.
    /// `(le 5000 3000)`. A parameter the bindings leave open stays `?name`.
    pub instance: Expr,
    /// The evaluated truth value. `Some` for every fired instance; `None` only
    /// for a gap candidate whose guard could not be decided (an open parameter
    /// or a non-literal operand). `None` is never read as `false`.
    pub holds: Option<bool>,
}

impl GuardJudgement {
    /// Whether this guard is recorded as holding.
    fn is_true(&self) -> bool {
        self.holds == Some(true)
    }
}

/// Whether every guard of one instance holds.
///
/// An undecided guard is not `true`, so the instance does not fire: the
/// reasoner reports the undecided state where it can (gap candidates) and
/// errors where it cannot (a fired step must decide every guard).
fn guards_hold(guards: &[GuardJudgement]) -> bool {
    guards.iter().all(GuardJudgement::is_true)
}

/// Which branch or witness one premise of a rule instance used.
///
/// The reasoner records one entry per premise. A disjunction records which
/// written branch's proof was actually found; an existence records the concrete
/// declared individual whose body was found. The selection is derived from the
/// found proof, never guessed, and travels into the certificate's `choices`.
#[derive(Debug, Clone, PartialEq, Default)]
pub enum PremiseSelection {
    #[default]
    Plain,
    Branch {
        premise: usize,
        branch: usize,
    },
    Witness {
        premise: usize,
        witness: Expr,
    },
}

impl PremiseSelection {
    /// The branch/witness choice this selection records, or `None` for a plain
    /// premise. A witness that cannot be represented is an error, never a
    /// silently dropped record.
    pub(crate) fn certificate_choice(
        &self,
    ) -> Result<Option<std_deduce_cert::PremiseChoice>, String> {
        match self {
            PremiseSelection::Plain => Ok(None),
            PremiseSelection::Branch { premise, branch } => {
                Ok(Some(std_deduce_cert::PremiseChoice::Branch {
                    premise: *premise,
                    branch: *branch,
                }))
            }
            PremiseSelection::Witness { premise, witness } => {
                Ok(Some(std_deduce_cert::PremiseChoice::Witness {
                    premise: *premise,
                    witness: cert_expr(witness, None, "存在见证")?,
                }))
            }
        }
    }
}

/// The largest number of witness candidates one existential premise may try in
/// one rule enumeration.
///
/// Witnesses are enumerated from the rule-visible facts and from the declared
/// individuals of the domain type. Exceeding the bound is an explicit error: a
/// premise that silently stopped at an arbitrary witness would be a hidden
/// incompleteness.
pub const MAX_WITNESS_CANDIDATES_PER_PREMISE: usize = 64;

/// The largest number of branch/witness selection attempts one rule may make in
/// one enumeration (one fixed-point round or one witness index).
///
/// Disjunction and existence are alternatives, not a product: the reasoner
/// tries the branches of one premise in written order and uses the first branch
/// that yields a complete instance, and enumerates one witness per matching
/// body. This bound is the explicit ceiling on that search, so a rule set that
/// would multiply choices cannot silently turn into an explosive search.
pub const MAX_SELECTION_ATTEMPTS_PER_RULE: usize = 512;

/// One instantiation of a rule against a set of known facts.
struct Instance {
    /// The proposition this instance derives: the rule's conclusion with the
    /// parameter values substituted and the built-in arithmetic evaluated, so
    /// `合计 甲 (add 3000 2000)` is recorded as `合计 甲 5000`.
    conclusion: Expr,
    /// The pre-evaluation form, kept only when the evaluation changed it. It
    /// is what makes the arithmetic step auditable: the certificate records
    /// both, and the checker recomputes the second from the first.
    computed: Option<Box<Expr>>,
    premise_keys: Vec<String>,
    /// One selection per premise: plain, a chosen branch, or a chosen witness.
    selections: Vec<PremiseSelection>,
    /// Open `unless` expressions, already closed by this instantiation.
    unlesses: Vec<Expr>,
    /// The guard judgements of this instantiation, in declaration order.
    guard_judgements: Vec<GuardJudgement>,
    /// The rule's parameters and the values this instantiation bound them to.
    bindings: Vec<(Name, Expr)>,
}

/// How one side of a conflict is supported.
///
/// The identity travels with a fact because it decides the conflict: a strict
/// fact outranks a rule conclusion and a claim, while a claim stands against a
/// rule conclusion unresolved. A rule side carries its witnesses; an empty list
/// means they can no longer be rebuilt.
enum Support {
    Fact(FactIdentity),
    Rules(Vec<Name>),
    /// Derived by instantiating the named universal fact.
    Axiom(Name),
    Interpretation(Name),
}

impl Support {
    /// The provenance the certificate records for this side.
    fn provenance(&self) -> Provenance {
        match self {
            Support::Fact(_) => Provenance::Assumption,
            Support::Rules(rules) => Provenance::Rules(rules.clone()),
            Support::Axiom(axiom) => Provenance::Axiom(axiom.clone()),
            Support::Interpretation(interpretation) => {
                Provenance::Interpretation(interpretation.clone())
            }
        }
    }
}

/// The witnesses recorded for one conclusion while its proof graph is being
/// built. A conclusion may get its first node before every witness is ready:
/// witnesses whose premises depend on another pending conclusion are appended
/// in a later round. Entries keep their structural identity so the final order
/// is the stable witness order, not the round that happened to construct them.
struct WitnessBuild {
    proposition: Expr,
    main_identity: (u8, String, String),
    entries: Vec<((u8, String, String), usize)>,
    /// Distinct witnesses the index found for this conclusion, before the
    /// per-conclusion bound. Truncation is `total > entries.len()`.
    total: usize,
}

/// The capacity error for a proof graph that would exceed the certificate's
/// node bound. It is raised before the node vector is built past the bound, so
/// a large multi-witness case fails early instead of after minutes of work.
fn node_capacity_error(estimate: usize) -> String {
    format!(
        "证书节点数量将超过上限 {}：按当前事实与规则预估约 {estimate} 个节点\
         （同一结论的多条见证使节点数约等于已推导结论数 × 见证数，每个结论最多 {} 条）。\
         请减少可推导的对象或规则，或收紧查询目标。",
        std_deduce_cert::MAX_CERT_NODES,
        std_deduce_cert::MAX_CERT_WITNESSES_PER_CONCLUSION
    )
}

/// Whether two witnesses are the same argument: same derivation kind and name,
/// and the same binding values under kernel conversion.
///
/// Bindings are compared by parameter name, not by the order they happen to be
/// listed in: a checker accepts any binding order, so the same instance must
/// not become a second independent witness merely by reordering its bindings.
/// Kernel conversion also folds η-equivalent function values.
type WitnessParts<'a> = (
    u8,
    &'a Name,
    &'a Vec<(Name, Expr)>,
    Option<&'a [PremiseSelection]>,
);

fn same_witness(
    env: &Env,
    left: &WitnessCandidate,
    right: &WitnessCandidate,
) -> Result<bool, String> {
    let (left_kind, left_name, left_bindings, left_selections): WitnessParts<'_> = match left {
        WitnessCandidate::Rule { rule, instance, .. } => {
            (0u8, rule, &instance.bindings, Some(&instance.selections))
        }
        WitnessCandidate::Axiom { instance } => (1u8, &instance.axiom, &instance.bindings, None),
    };
    let (right_kind, right_name, right_bindings, right_selections): WitnessParts<'_> = match right {
        WitnessCandidate::Rule { rule, instance, .. } => {
            (0u8, rule, &instance.bindings, Some(&instance.selections))
        }
        WitnessCandidate::Axiom { instance } => (1u8, &instance.axiom, &instance.bindings, None),
    };
    if left_kind != right_kind
        || left_name != right_name
        || left_bindings.len() != right_bindings.len()
    {
        return Ok(false);
    }
    let mut left_sorted: Vec<(&Name, &Expr)> = left_bindings
        .iter()
        .map(|(name, value)| (name, value))
        .collect();
    let mut right_sorted: Vec<(&Name, &Expr)> = right_bindings
        .iter()
        .map(|(name, value)| (name, value))
        .collect();
    left_sorted.sort_by_key(|(name, _)| name.to_string());
    right_sorted.sort_by_key(|(name, _)| name.to_string());
    for ((left_name, left_value), (right_name, right_value)) in
        left_sorted.iter().zip(right_sorted.iter())
    {
        if left_name != right_name {
            return Ok(false);
        }
        let same = convertible(env, &Ctx::new(), left_value, right_value)
            .map_err(|error| format!("无法判定两个见证的绑定值是否等价：{error}"))?;
        if !same {
            return Ok(false);
        }
    }
    match (left_selections, right_selections) {
        (None, None) => Ok(true),
        (Some(left), Some(right)) => same_selections(env, left, right),
        _ => Ok(false),
    }
}

/// Whether two instances chose the same branch or witness for every premise.
///
/// A different witness is a different argument even when the parameters and the
/// conclusion are identical: the certificate records the choice, so two
/// arguments that rest on different witnesses must not be merged into one.
fn same_selections(
    env: &Env,
    left: &[PremiseSelection],
    right: &[PremiseSelection],
) -> Result<bool, String> {
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right.iter()) {
        match (left, right) {
            (PremiseSelection::Plain, PremiseSelection::Plain) => {}
            (
                PremiseSelection::Branch {
                    premise: left_premise,
                    branch: left_branch,
                },
                PremiseSelection::Branch {
                    premise: right_premise,
                    branch: right_branch,
                },
            ) => {
                if left_premise != right_premise || left_branch != right_branch {
                    return Ok(false);
                }
            }
            (
                PremiseSelection::Witness {
                    premise: left_premise,
                    witness: left_witness,
                },
                PremiseSelection::Witness {
                    premise: right_premise,
                    witness: right_witness,
                },
            ) => {
                if left_premise != right_premise {
                    return Ok(false);
                }
                if !convertible(env, &Ctx::new(), left_witness, right_witness)
                    .map_err(|error| format!("无法判定两个存在见证是否等价：{error}"))?
                {
                    return Ok(false);
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

/// One node that independently derives a conclusion.
enum WitnessCandidate {
    Rule {
        rule: Name,
        instance: Instance,
        sources: Vec<SourceRef>,
        applicability: Box<Applicability>,
    },
    Axiom {
        instance: AxiomInstance,
    },
}

impl WitnessCandidate {
    /// The propositions a witness consumes; a universal instance consumes
    /// none because its evidence is the declaration itself.
    fn premise_keys(&self) -> &[String] {
        match self {
            WitnessCandidate::Rule { instance, .. } => &instance.premise_keys,
            WitnessCandidate::Axiom { .. } => &[],
        }
    }

    /// The stable structural identity of a witness: derivation kind, rule or
    /// axiom name, and the binding values by structural key. Two records with
    /// the same key are the same argument, not two independent ones.
    fn identity_key(&self, env: &Env) -> (u8, String, String) {
        match self {
            WitnessCandidate::Rule { rule, instance, .. } => (
                0,
                rule.to_string(),
                format!(
                    "{}|{}",
                    instance_binding_key(env, &instance.bindings),
                    instance_selection_key(env, &instance.selections)
                ),
            ),
            WitnessCandidate::Axiom { instance } => (
                1,
                instance.axiom.to_string(),
                instance_binding_key(env, &instance.bindings),
            ),
        }
    }
}

/// The branch/witness structure of one rule instance.
///
/// A witness choice is part of the instance's identity: two instances of the
/// same rule with the same parameters but different witnesses are different
/// arguments and must not be merged into one node.
fn instance_selection_key(env: &Env, selections: &[PremiseSelection]) -> String {
    selections
        .iter()
        .map(|selection| match selection {
            PremiseSelection::Plain => "plain".to_string(),
            PremiseSelection::Branch { premise, branch } => {
                format!("branch:{premise}:{branch}")
            }
            PremiseSelection::Witness { premise, witness } => {
                format!("witness:{premise}:{}", structural_key(env, witness))
            }
        })
        .collect::<Vec<_>>()
        .join(";")
}

/// The binding structure of a rule or universal instance.
///
/// Values are compared by the collision-free structural encoding of their
/// normal forms, so a `def` alias and its underlying term describe the same
/// binding, and printed text is never the identity.
fn instance_binding_key(env: &Env, bindings: &[(Name, Expr)]) -> String {
    bindings
        .iter()
        .map(|(parameter, value)| format!("{parameter}={}", structural_key(env, value)))
        .collect::<Vec<_>>()
        .join(";")
}

// ------------------------------------------------------- universal facts

/// Collect the environment's instantiable universal facts, grouped by the
/// normalized predicate head of their body.
///
/// A universal fact is a `Fact` declaration whose proposition is a telescope of
/// named `∀` binders ending in a predicate-headed proposition. Its identity must
/// seed a derivation: a `disputed` declaration asserts only what the other side
/// claims, so instantiating it would smuggle an unasserted claim into the fact
/// base. Declarations without a named universal binder (a bare proposition, an
/// anonymous arrow), with a repeated binder name, or with a body whose head is
/// not a predicate (an implication, a quantified form, a proposition variable)
/// are not instantiable and are left out: no goal can name the values they
/// would need.
///
/// The grouping is the candidate filter: a goal's normalized head selects one
/// group, so instantiation is never a scan over every declaration.
fn axiom_declarations(env: &Env) -> Result<BTreeMap<Name, Vec<AxiomDecl>>, String> {
    let mut by_head: BTreeMap<Name, Vec<AxiomDecl>> = BTreeMap::new();
    for decl in env.iter() {
        let DeclKind::Fact { identity } = &decl.kind else {
            continue;
        };
        if !identity.seeds_derivation() {
            continue;
        }
        // The declaration's type must itself be a universal proposition. The
        // environment checks this on insertion, but a directly built ledger is
        // part of the reasoner's input too, so it is checked here.
        check::check(env, &Ctx::new(), &decl.ty, &Expr::Sort(0)).map_err(|error| {
            format!(
                "无法把 `{}` 当作全称公理：它的类型不是命题：{error}",
                decl.name
            )
        })?;
        let binders_and_body = named_binders(env, &decl.ty)
            .map_err(|error| format!("无法解析全称公理 `{}` 的类型：{error}", decl.name))?;
        let Some((binders, body)) = binders_and_body else {
            continue;
        };
        let normalized_body = normalize(env, &Ctx::new(), &body)
            .map_err(|error| format!("无法规范化全称公理 `{}` 的命题体：{error}", decl.name))?;
        let Some(head) = normalized_body.head_const() else {
            continue;
        };
        by_head.entry(head).or_default().push(AxiomDecl {
            name: decl.name.clone(),
            identity: *identity,
            binders,
            body,
            normalized_body,
            sources: decl.sources.clone(),
        });
    }
    for group in by_head.values_mut() {
        group.sort_by(|a, b| a.name.cmp(&b.name));
    }
    Ok(by_head)
}

/// First-order match of a universal body against a closed goal.
///
/// The only variables of `pattern` are the universal's own binders, which are
/// free de Bruijn indices (`index >= depth`). A free index is bound once to the
/// corresponding goal subterm; a repeated binder must meet an identical term.
/// A value that mentions one of the goal's own binders is rejected: every
/// recorded binding must be closed, so a bound-variable value would be a
/// capture rather than an instance. Binders of the body itself (`index <
/// depth`) must agree structurally; the goal's constants are never generalized
/// into variables, so matching only instantiates the declaration's binders.
fn match_axiom_body(
    pattern: &Expr,
    goal: &Expr,
    depth: usize,
    binders: usize,
    binding: &mut Vec<(usize, Expr)>,
) -> bool {
    match (pattern, goal) {
        (Expr::Sort(left), Expr::Sort(right)) => left == right,
        (Expr::Const(left), Expr::Const(right)) => left == right,
        (Expr::Num(left), Expr::Num(right)) => left == right,
        (Expr::Date(left), Expr::Date(right)) => left == right,
        (Expr::Var(left), Expr::Var(right)) if left < &depth || right < &depth => *left == *right,
        (Expr::Var(left), other) if *left >= depth => {
            // `position` counts from the outermost binder; `0` is de Bruijn
            // index `binders - 1`.
            let position = binders - 1 - (*left - depth);
            if !is_closed(other) {
                return false;
            }
            match binding.iter().find(|(bound, _)| *bound == position) {
                Some((_, previous)) => previous == other,
                None => {
                    binding.push((position, other.clone()));
                    true
                }
            }
        }
        (Expr::Var(_), _) => false,
        (
            Expr::App {
                func: pattern_func,
                arg: pattern_arg,
            },
            Expr::App {
                func: goal_func,
                arg: goal_arg,
            },
        ) => {
            match_axiom_body(pattern_func, goal_func, depth, binders, binding)
                && match_axiom_body(pattern_arg, goal_arg, depth, binders, binding)
        }
        (
            Expr::Pi {
                domain: pattern_domain,
                codomain: pattern_codomain,
                ..
            },
            Expr::Pi {
                domain: goal_domain,
                codomain: goal_codomain,
                ..
            },
        ) => {
            match_axiom_body(pattern_domain, goal_domain, depth, binders, binding)
                && match_axiom_body(pattern_codomain, goal_codomain, depth + 1, binders, binding)
        }
        (
            Expr::Lam {
                domain: pattern_domain,
                body: pattern_body,
                ..
            },
            Expr::Lam {
                domain: goal_domain,
                body: goal_body,
                ..
            },
        ) => {
            match_axiom_body(pattern_domain, goal_domain, depth, binders, binding)
                && match_axiom_body(pattern_body, goal_body, depth + 1, binders, binding)
        }
        (
            Expr::Let {
                value: pattern_value,
                body: pattern_body,
                ..
            },
            Expr::Let {
                value: goal_value,
                body: goal_body,
                ..
            },
        ) => {
            match_axiom_body(pattern_value, goal_value, depth, binders, binding)
                && match_axiom_body(pattern_body, goal_body, depth + 1, binders, binding)
        }
        _ => false,
    }
}

/// How many closed candidate values one evaluation-aware axiom match may draw
/// from a goal.
///
/// The fallback is only used when a structural match failed and the
/// declaration's body contains a built-in operation: its instance can become
/// the goal after the operation evaluates (`x + 0` with `x = 5000` becomes
/// `5000`). Exceeding the bound is an error that names it, never a silently
/// skipped candidate.
pub const MAX_AXIOM_MATCH_VALUES: usize = 64;

/// How many complete binder assignments one evaluation-aware axiom match may
/// try. An assignment is one value per still-unbound binder variable; the
/// product of the candidate sets above is checked before anything is tried.
pub const MAX_AXIOM_MATCH_ASSIGNMENTS: usize = 4096;

/// Does `expression` mention a built-in operation?
///
/// The evaluation-aware match fallback is meaningful only here: without such
/// an operation, evaluating the instantiated body cannot change it, so the
/// ordinary structural and normalized matches already cover the goal.
fn contains_builtin_arithmetic(expression: &Expr) -> bool {
    match expression {
        Expr::Const(name) => std_deduce_kernel::builtin::Op::from_name(name).is_some(),
        Expr::Sort(_) | Expr::Var(_) | Expr::Num(_) | Expr::Date(_) => false,
        Expr::Pi {
            domain, codomain, ..
        } => contains_builtin_arithmetic(domain) || contains_builtin_arithmetic(codomain),
        Expr::Lam { domain, body, .. } => {
            contains_builtin_arithmetic(domain) || contains_builtin_arithmetic(body)
        }
        Expr::App { func, arg } => {
            contains_builtin_arithmetic(func) || contains_builtin_arithmetic(arg)
        }
        Expr::Let { value, body, .. } => {
            contains_builtin_arithmetic(value) || contains_builtin_arithmetic(body)
        }
    }
}

/// Every closed subterm of `expression`, in pre-order.
fn closed_subterms(expression: &Expr, out: &mut Vec<Expr>) {
    if !is_closed(expression) {
        return;
    }
    out.push(expression.clone());
    match expression {
        Expr::App { func, arg } => {
            closed_subterms(func, out);
            closed_subterms(arg, out);
        }
        Expr::Pi {
            domain, codomain, ..
        } => {
            closed_subterms(domain, out);
            closed_subterms(codomain, out);
        }
        Expr::Lam { domain, body, .. } => {
            closed_subterms(domain, out);
            closed_subterms(body, out);
        }
        Expr::Let { value, body, .. } => {
            closed_subterms(value, out);
            closed_subterms(body, out);
        }
        _ => {}
    }
}

/// The binder positions a universal body still mentions, as the positions
/// [`match_axiom_body`] records.
fn free_binder_positions(
    expression: &Expr,
    depth: usize,
    binders: usize,
    out: &mut BTreeSet<usize>,
    axiom: &str,
) -> Result<(), String> {
    match expression {
        Expr::Var(index) if *index >= depth => {
            let offset = *index - depth;
            let position = binders
                .checked_sub(offset + 1)
                .ok_or_else(|| format!("公理 `{axiom}` 的命题体含有超出绑定范围的自由变量"))?;
            out.insert(position);
        }
        Expr::Sort(_) | Expr::Const(_) | Expr::Num(_) | Expr::Date(_) | Expr::Var(_) => {}
        Expr::Pi {
            domain, codomain, ..
        } => {
            free_binder_positions(domain, depth, binders, out, axiom)?;
            free_binder_positions(codomain, depth + 1, binders, out, axiom)?;
        }
        Expr::Lam { domain, body, .. } => {
            free_binder_positions(domain, depth, binders, out, axiom)?;
            free_binder_positions(body, depth + 1, binders, out, axiom)?;
        }
        Expr::App { func, arg } => {
            free_binder_positions(func, depth, binders, out, axiom)?;
            free_binder_positions(arg, depth, binders, out, axiom)?;
        }
        Expr::Let { value, body, .. } => {
            free_binder_positions(value, depth, binders, out, axiom)?;
            free_binder_positions(body, depth + 1, binders, out, axiom)?;
        }
    }
    Ok(())
}

/// Every complete binder assignment the evaluation-aware match may try.
///
/// Values are closed subterms of the goal's normal form: an operation inside
/// the axiom body only evaluates once its operands are literals
/// (`x + 0`), so the value that makes the instance equal the goal is one of
/// those subterms. Literal values are tried first, which keeps the ordinary
/// case (a goal that is already a number) cheap and deterministic. The whole
/// search space is bounded before it is enumerated; exceeding a bound is an
/// error naming it.
fn value_bindings(axiom: &AxiomDecl, goal: &Expr) -> Result<Vec<Vec<(usize, Expr)>>, String> {
    let mut positions = BTreeSet::new();
    free_binder_positions(
        &axiom.body,
        0,
        axiom.binders.len(),
        &mut positions,
        &axiom.name,
    )?;
    let mut candidates = Vec::new();
    closed_subterms(goal, &mut candidates);
    if candidates.len() > MAX_AXIOM_MATCH_VALUES {
        return Err(format!(
            "目标「{}」有 {} 个闭合子项，超过公理 `{}` 的算术匹配候选上限 {} 个",
            print_expr(goal),
            candidates.len(),
            axiom.name,
            MAX_AXIOM_MATCH_VALUES
        ));
    }
    candidates.sort_by_key(|value| u8::from(!matches!(value, Expr::Num(_))));
    let positions: Vec<usize> = positions.into_iter().collect();
    if positions.is_empty() || candidates.is_empty() {
        // Nothing to assign. A body with no free binder variable is already
        // closed and the structural matches would have covered it; this path
        // produces no assignment rather than an empty one.
        return Ok(Vec::new());
    }
    let space = candidates
        .len()
        .checked_pow(positions.len() as u32)
        .filter(|space| *space <= MAX_AXIOM_MATCH_ASSIGNMENTS);
    let Some(space) = space else {
        return Err(format!(
            "公理 `{}` 的算术匹配需要 {} 个候选值的 {} 重组合，超过 {} 个赋值上限",
            axiom.name,
            candidates.len(),
            positions.len(),
            MAX_AXIOM_MATCH_ASSIGNMENTS
        ));
    };
    let mut out = Vec::with_capacity(space);
    let mut current = vec![0usize; positions.len()];
    loop {
        out.push(
            positions
                .iter()
                .zip(current.iter())
                .map(|(position, index)| (*position, candidates[*index].clone()))
                .collect(),
        );
        // Odometer increment. The last digit is advanced first, so the first
        // candidate is tried in every position before any position moves on.
        let mut digit = current.len();
        loop {
            if digit == 0 {
                return Ok(out);
            }
            digit -= 1;
            current[digit] += 1;
            if current[digit] < candidates.len() {
                break;
            }
            current[digit] = 0;
        }
    }
}

/// The settled result: the set of facts and a derivation for each.
struct Fixed {
    /// The settled fact base, including the conclusions an interpretation
    /// licensed. A queried goal is proved against this set.
    facts: BTreeMap<String, Expr>,
    /// The facts the rule stage could see: registered facts and rule
    /// conclusions, without any interpretation application. Rules never
    /// consume an interpretation's conclusion, so gap candidates must judge a
    /// rule's premises against this set, not against [`Fixed::facts`].
    rule_facts: BTreeMap<String, Expr>,
    nodes: Vec<Node>,
    ids: BTreeMap<String, usize>,
    conflicts: Vec<Conflict>,
    /// Conclusions that were derived but kept out of `facts` because of a
    /// conflict, keyed by the same normalised key as `facts`.
    contested: BTreeMap<String, Conflict>,
    /// Interpretation conclusion key -> interpretation id, for the applications
    /// that produced the settled fact base.
    applications: BTreeMap<String, Name>,
    /// Every derived conclusion's independent witness node ids, keyed by the
    /// same structural key as `facts`.
    alternatives: BTreeMap<String, WitnessGroup>,
}

/// How many universal facts one goal may be tried against.
///
/// The candidates are first filtered by the normalized predicate head of the
/// declaration's body, so this bounds a pathological environment that declares
/// many universal facts about the same predicate. Exceeding it is an error that
/// names the bound; no candidate is silently skipped.
pub const MAX_AXIOM_CANDIDATES_PER_GOAL: usize = 64;

/// The largest number of universal-elimination instances one query may derive.
///
/// Every instance is keyed by its conclusion, so this is also the bound on the
/// conclusions universal elimination can add to one fact base. Exceeding it is
/// an error naming the bound, never a truncated derivation.
pub const MAX_AXIOM_INSTANCES_PER_QUERY: usize = 1024;

/// The largest number of distinct goals one query may try to instantiate.
///
/// A probe that finds no instance is remembered as well as one that finds an
/// instance, so repeated premises do not recompute the match. The bound keeps a
/// runaway premise demand finite; exceeding it is an error, never a silent
/// stop.
pub const MAX_AXIOM_PROBES_PER_QUERY: usize = 4096;

/// One universal fact declaration, prepared for demand-driven instantiation.
///
/// Only a `Fact` declaration whose declared type is a telescope of *named*
/// universal binders ending in a predicate-headed proposition is instantiable.
/// The proposition is the fact's whole declaration (`Decl::ty`), so the
/// declaration's identity is the evidence the instance rests on.
#[derive(Debug, Clone)]
struct AxiomDecl {
    name: Name,
    identity: FactIdentity,
    /// Binder names, outermost first.
    binders: Vec<Name>,
    /// The declaration's proposition body, written in the context of `binders`.
    body: Expr,
    /// `body` normalized once (beta, `def` delta, zeta). It is what the
    /// matching fallback compares.
    normalized_body: Expr,
    sources: Vec<SourceRef>,
}

/// The per-query state of universal elimination.
#[derive(Debug, Default)]
struct AxiomState {
    /// Instances keyed by the conclusion's structural key, so a conclusion
    /// demanded twice is derived once. When two universal facts can produce
    /// the same conclusion, the first in axiom-name order wins.
    instances: BTreeMap<String, AxiomInstance>,
    /// Goals already probed, successful or not. Probing is a pure function of
    /// the environment and the goal, so a miss is remembered as well.
    probed: BTreeSet<String>,
}

/// A universal fact tried against one goal.
#[derive(Debug, Clone)]
enum AxiomTrial {
    /// The body unified and the instance is legal.
    Instantiated(AxiomInstance),
    /// The body unified, but no instance was produced. The unified bindings
    /// are kept so a gap report can say which value the instance would need.
    Refused {
        axiom: Name,
        bindings: Vec<(Name, Expr)>,
        problem: String,
    },
}

// ---------------------------------------------------------------- reasoner

pub struct Reasoner<'a> {
    env: &'a Env,
    assumptions: Vec<Assumption>,
    /// Every declared priority edge, keyed by `(winner, loser)`. One pair may
    /// carry several edges: the same order can be claimed by several packages.
    declared: BTreeMap<(Name, Name), Vec<PriorityEdge>>,
    /// Rule name -> strongly connected component of the declared priority
    /// graph.
    scc: BTreeMap<Name, u32>,
    /// Priority edges between different components, i.e. the ones that can
    /// decide a conflict. An edge inside a cycle can never decide anything.
    effective: BTreeMap<Name, BTreeSet<Name>>,
    /// Every priority cycle: the components that declare one (more than one
    /// rule, or a single rule that outranks itself), members sorted by name,
    /// components sorted by their first member.
    cycles: Vec<Vec<Name>>,
    /// The environment's declared `contrary` and `unique` relation. The
    /// judgement over it is [`std_deduce_cert::conflict::in_conflict`], shared
    /// with the certificate checker so both read a conflict the same way.
    declarations: Declarations,
    /// Interpretations this query enabled, sorted by id. Empty means the
    /// default: every interpretation stays inert, and output is unchanged.
    enabled: BTreeSet<Name>,
    /// The session's legal as-of date, if one was set. It is a reference date
    /// of the applicability judgement, never copied onto a fact.
    as_of: Option<String>,
    /// The session's jurisdiction code, if one was set. It is compared with a
    /// rule's recorded `jurisdiction`; it never filters a rule by itself.
    jurisdiction: Option<String>,
    /// Assumption occurrence records indexed by the proposition's structural
    /// key. Built lazily and invalidated when an assumption is registered, so
    /// an instance judgement does not scan the whole assumption table for
    /// every premise. The `Rc` is cloned per lookup, not the strings.
    occurrence_index: RefCell<Option<Rc<OccurrenceIndex>>>,
    /// Universal facts grouped by the normalized predicate head of their body.
    /// This is the candidate filter: instantiation never scans the whole
    /// ledger, only the declarations that can conclude the goal's predicate.
    axioms: BTreeMap<Name, Vec<AxiomDecl>>,
    /// A failure while preparing the universal facts. It is reported by the
    /// first query that needs them, instead of being swallowed into an empty
    /// candidate set.
    axiom_error: Option<String>,
    axiom_state: RefCell<AxiomState>,
    fixed: Option<Fixed>,
    max_rounds: usize,
}

impl<'a> Reasoner<'a> {
    pub fn new(env: &'a Env) -> Self {
        let declared = declared_priorities(env);
        let graph = priority_graph(env, &declared);
        let declarations = Declarations::from_env(env);
        let (axioms, axiom_error) = match axiom_declarations(env) {
            Ok(axioms) => (axioms, None),
            Err(error) => (BTreeMap::new(), Some(error)),
        };
        Reasoner {
            env,
            assumptions: Vec::new(),
            declared,
            scc: graph.scc,
            effective: graph.effective,
            cycles: graph.cycles,
            declarations,
            enabled: BTreeSet::new(),
            as_of: None,
            jurisdiction: None,
            occurrence_index: RefCell::new(None),
            axioms,
            axiom_error,
            axiom_state: RefCell::new(AxiomState::default()),
            fixed: None,
            max_rounds: 256,
        }
    }

    /// Anchor the reasoner's applicability judgement to the session's legal
    /// as-of date and jurisdiction code.
    ///
    /// Call this before [`Reasoner::saturate`]. `:asof` is only a fallback for
    /// an instance whose premise facts record no occurrence date; an event
    /// time, when present, is never replaced by it. `None` means "not set" and
    /// is reported as missing input when a rule declares that dimension; it is
    /// never filled in from a default. The values are validated by the command
    /// layer, and a malformed stored value only ever makes a comparison
    /// undecidable — it is not silently dropped.
    pub fn set_session_scope(&mut self, as_of: Option<&str>, jurisdiction: Option<&str>) {
        self.as_of = as_of.map(ToOwned::to_owned);
        self.jurisdiction = jurisdiction.map(ToOwned::to_owned);
    }

    /// The assumption occurrence records, indexed by structural key.
    ///
    /// A proposition may be asserted by more than one fact declaration; both
    /// records stay under the same key, so an instance that consumes the
    /// proposition references every recorded event. The cache is invalidated
    /// when a new assumption is registered.
    fn occurrence_index(&self) -> Rc<OccurrenceIndex> {
        if let Some(index) = self.occurrence_index.borrow().as_ref() {
            return Rc::clone(index);
        }
        let mut built = OccurrenceIndex::new();
        for assumption in &self.assumptions {
            built
                .entry(self.key_of(&assumption.prop))
                .or_default()
                .push((
                    assumption.occurred_at.clone(),
                    assumption.occurred_in.clone(),
                ));
        }
        let built = Rc::new(built);
        *self.occurrence_index.borrow_mut() = Some(Rc::clone(&built));
        built
    }

    /// The occurrence records of the premise facts a rule instance references.
    ///
    /// A premise key that names a registered fact is looked up in the
    /// occurrence index; one that names only a derived conclusion carries no
    /// occurrence record, so it is flagged as missing rather than inherited
    /// from its own premises. The session's as-of date and jurisdiction are
    /// copied in as the fallback/legal-system values.
    fn instance_anchor(&self, premise_keys: &[String]) -> InstanceAnchor {
        let index = self.occurrence_index();
        let mut event_dates: Vec<String> = Vec::new();
        let mut event_places: Vec<String> = Vec::new();
        let mut missing_event_date = false;
        let mut missing_event_place = false;
        for key in premise_keys {
            match index.get(key) {
                Some(records) => {
                    for (date, place) in records {
                        match date {
                            Some(date) => {
                                if !event_dates.contains(date) {
                                    event_dates.push(date.clone());
                                }
                            }
                            None => missing_event_date = true,
                        }
                        match place {
                            Some(place) => {
                                if !event_places.contains(place) {
                                    event_places.push(place.clone());
                                }
                            }
                            None => missing_event_place = true,
                        }
                    }
                }
                // A rule conclusion is a fact but not a registered occurrence:
                // it does not inherit the event time/place of its premises.
                None => {
                    missing_event_date = true;
                    missing_event_place = true;
                }
            }
        }
        InstanceAnchor {
            as_of: self.as_of.clone(),
            jurisdiction: self.jurisdiction.clone(),
            event_dates,
            missing_event_date,
            event_places,
            missing_event_place,
        }
    }

    /// Judge one rule instance against the facts it consumes.
    fn judge_instance(
        &self,
        scope: &std_deduce_kernel::meta::Scope,
        premise_keys: &[String],
    ) -> Applicability {
        applicability::judge(scope, &self.instance_anchor(premise_keys))
    }

    /// Split one instantiated premise list into the facts it already holds and
    /// the premises still missing.
    ///
    /// The keys of the held premises are how the ledger indexes a fact's
    /// occurrence record, so they are the whole input of the applicability
    /// judgement. One judgment ([`premise_satisfied`], shared with the
    /// derivation) decides both lists: a premise the fixed point can consume
    /// must contribute its event record, and a premise it cannot consume must
    /// stay missing here as well. Computing the two lists from different
    /// conditions would let a rule be judged inapplicable on the event record
    /// of a fact it never used, or applicable while the gap tree reports the
    /// same premise missing.
    /// Classify every premise of one candidate instance against the fact set.
    ///
    /// The classification is the single judgment used by the gap tree, the
    /// issue scan and the certificate's gap record: a plain premise is held or
    /// missing; a disjunctive premise holds at the first written branch that a
    /// fact satisfies (otherwise all branches are missing, one entry each); an
    /// existential premise holds at the first concrete witness whose body a
    /// fact satisfies, or is missing with the body pattern and the candidate
    /// individuals the search tried. A disjunction never reports a lump-sum
    /// "P or Q" gap, and an existence never reports "some individual satisfies
    /// P" without naming the candidates it could enumerate.
    fn premise_statuses(
        &self,
        rule_name: &str,
        rule: &RuleDecl,
        binding: &[(Name, Expr)],
        facts: &BTreeMap<String, Expr>,
    ) -> Result<Vec<PremiseStatus>, String> {
        let mut statuses = Vec::with_capacity(rule.premises.len());
        for index in 0..rule.premises.len() {
            let status = match rule.open_premise(index) {
                OpenPremise::Plain(pattern) => {
                    let proposition = close_pattern(&pattern, binding);
                    if premise_satisfied(self.env, facts, &proposition) {
                        PremiseStatus {
                            held: Some(proposition),
                            selection: PremiseSelection::Plain,
                            ..PremiseStatus::default()
                        }
                    } else {
                        PremiseStatus {
                            missing: vec![proposition],
                            selection: PremiseSelection::Plain,
                            ..PremiseStatus::default()
                        }
                    }
                }
                OpenPremise::Or(branches) => {
                    let closed: Vec<Expr> = branches
                        .iter()
                        .map(|branch| close_pattern(branch, binding))
                        .collect();
                    let first = closed
                        .iter()
                        .position(|branch| premise_satisfied(self.env, facts, branch));
                    match first {
                        Some(branch) => PremiseStatus {
                            held: Some(closed[branch].clone()),
                            selection: PremiseSelection::Branch {
                                premise: index,
                                branch,
                            },
                            ..PremiseStatus::default()
                        },
                        None => PremiseStatus {
                            missing: closed.clone(),
                            branches: closed.into_iter().enumerate().collect(),
                            selection: PremiseSelection::Plain,
                            ..PremiseStatus::default()
                        },
                    }
                }
                OpenPremise::Exists {
                    binder,
                    domain,
                    body,
                } => {
                    let pattern = close_pattern(&body, binding);
                    let witness_candidates =
                        display_witness_candidates(self.env, &close_pattern(&domain, binding))?;
                    let holds = if open_names(&body).contains(&binder) {
                        // Match the body against facts to find a concrete
                        // witness; the first declared individual in fact order
                        // is the deterministic choice.
                        let mut found = None;
                        for fact in facts.values() {
                            let mut trial = binding.to_vec();
                            if !match_premise(self.env, &pattern, fact, &mut trial) {
                                continue;
                            }
                            let Some(witness) = trial
                                .iter()
                                .rev()
                                .find(|(name, _)| *name == binder)
                                .map(|(_, value)| value.clone())
                            else {
                                continue;
                            };
                            if !is_concrete_witness(self.env, &witness) {
                                return Err(format!(
                                    "规则 `{}` 的第 {} 个存在前提的见证 `{}` 不是已声明个体：\
                                     不能用它作为缺口候选的具体见证",
                                    rule_name,
                                    index + 1,
                                    print_expr(&witness)
                                ));
                            }
                            let instance = substitute_pattern_constants(
                                &pattern,
                                &[(binder.clone(), witness.clone())],
                            );
                            found = Some(PremiseStatus {
                                held: Some(instance),
                                selection: PremiseSelection::Witness {
                                    premise: index,
                                    witness,
                                },
                                exists: true,
                                ..PremiseStatus::default()
                            });
                            break;
                        }
                        found
                    } else {
                        let mut found = None;
                        for witness in &witness_candidates.items {
                            let instance = substitute_pattern_constants(
                                &pattern,
                                &[(binder.clone(), witness.clone())],
                            );
                            if premise_satisfied(self.env, facts, &instance) {
                                found = Some(PremiseStatus {
                                    held: Some(instance),
                                    selection: PremiseSelection::Witness {
                                        premise: index,
                                        witness: witness.clone(),
                                    },
                                    exists: true,
                                    ..PremiseStatus::default()
                                });
                                break;
                            }
                        }
                        found
                    };
                    match holds {
                        Some(status) => status,
                        None => PremiseStatus {
                            missing: vec![pattern],
                            selection: PremiseSelection::Plain,
                            exists_candidates: witness_candidates.items,
                            exists_truncated: witness_candidates.truncated,
                            exists: true,
                            ..PremiseStatus::default()
                        },
                    }
                }
            };
            statuses.push(status);
        }
        Ok(statuses)
    }

    /// The priority cycles of the environment: every strongly connected
    /// component that declares a cycle, either with at least two rules or with
    /// one rule whose priority edge points at itself. Members are sorted by
    /// name, components by their first member. Edges inside a cycle cannot
    /// decide a conflict.
    pub fn priority_cycles(&self) -> Vec<Vec<Name>> {
        self.cycles.clone()
    }

    /// The declared priority order this reasoner computed. Certificate
    /// generation uses it to describe why a declared priority could not decide
    /// a conflict.
    pub fn priority_order(&self) -> PriorityOrder {
        PriorityOrder {
            components: self.scc.clone(),
        }
    }

    /// Enable one interpretation for this query.
    ///
    /// An interpretation is an explicit permission, never an implicit rewrite:
    /// it must name a declared `interpret`, may not be enabled twice, and two
    /// enabled interpretations may not license kernel-equivalent conclusions —
    /// otherwise a single step would have two indistinguishable justifications.
    /// The error tells the reader to query them separately or disable one.
    pub fn enable_interpretation(&mut self, id: &str) -> Result<(), String> {
        let name = std_deduce_kernel::name(id);
        let Some(decl) = self.env.get(&name) else {
            return Err(format!("解释 `{id}` 不存在：当前环境没有这个声明"));
        };
        let DeclKind::Interpretation(interpretation) = &decl.kind else {
            return Err(format!("`{id}` 不是解释声明，不能启用"));
        };
        if self.enabled.contains(&name) {
            return Err(format!("解释 `{id}` 已经启用，不能重复启用"));
        }
        for existing in &self.enabled {
            let Some(decl) = self.env.get(existing) else {
                continue;
            };
            let DeclKind::Interpretation(other) = &decl.kind else {
                continue;
            };
            let same = self.key_of(&other.to) == self.key_of(&interpretation.to)
                || convertible(self.env, &Ctx::new(), &other.to, &interpretation.to).map_err(
                    |error| {
                        format!(
                            "无法判定解释 `{id}` 与已启用的解释 `{existing}` 的 to 是否等价：{error}"
                        )
                    },
                )?;
            if same {
                return Err(format!(
                    "解释 `{id}` 的 to 与已启用的解释 `{existing}` 在内核下等价，\
                     两个结论无法区分；请分别查询，或先 :interpret disable {existing}"
                ));
            }
        }
        self.enabled.insert(name);
        Ok(())
    }

    /// The interpretations this query enabled, sorted by id.
    pub fn enabled_interpretations(&self) -> Vec<Name> {
        self.enabled.iter().cloned().collect()
    }

    /// Every interpretation the environment declares, sorted by id.
    pub fn interpretation_records(&self) -> Vec<InterpretationRecord> {
        let mut records: Vec<InterpretationRecord> = self
            .env
            .iter()
            .filter_map(|decl| match &decl.kind {
                DeclKind::Interpretation(interpretation) => Some(InterpretationRecord {
                    id: decl.name.clone(),
                    from: interpretation.from.clone(),
                    to: interpretation.to.clone(),
                    direction: interpretation.direction,
                    sources: interpretation.sources.clone(),
                }),
                _ => None,
            })
            .collect();
        records.sort_by(|a, b| a.id.cmp(&b.id));
        records
    }

    /// The enabled interpretation declarations, sorted by id.
    fn enabled_records(&self) -> Vec<InterpretationRecord> {
        self.interpretation_records()
            .into_iter()
            .filter(|record| self.enabled.contains(&record.id))
            .collect()
    }

    /// Is `expression` already in `facts`, up to kernel definitional equality?
    ///
    /// The normalized key is an exact fast path; a miss compares every fact
    /// with [`convertible`]. A failed comparison is an error, never "not
    /// present": treating it as absent would silently skip a step whose
    /// premise may hold.
    fn holds(&self, facts: &BTreeMap<String, Expr>, expression: &Expr) -> Result<bool, String> {
        if facts.contains_key(&self.key_of(expression)) {
            return Ok(true);
        }
        for fact in facts.values() {
            if convertible(self.env, &Ctx::new(), fact, expression).map_err(|error| {
                format!("无法判定「{}」是否已成立：{error}", print_expr(expression))
            })? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Unenabled interpretations that could prove the queried `goal` in one
    /// more step: the interpretation's `to` is kernel-equivalent to the goal,
    /// and its `from` already holds in the fact set *before* any interpretation
    /// application.
    ///
    /// Only the root goal is considered. An unenabled interpretation is never
    /// offered for a rule's missing premise: rules do not consume
    /// interpretation conclusions, so enabling it could not close that gap.
    /// The `from` check reads the rule-visible set for the same reason — an
    /// already enabled interpretation's conclusion is not available to another
    /// interpretation, so a hint built on it would be a dead end.
    ///
    /// These are hints, not derivations: nothing is applied, and the result is
    /// sorted by id so the printed suggestion does not depend on declaration
    /// order.
    pub fn unused_interpretation_hints(
        &self,
        goal: &Expr,
    ) -> Result<Vec<InterpretationHint>, String> {
        let Some(fixed) = &self.fixed else {
            return Ok(Vec::new());
        };
        let mut out = Vec::new();
        for record in self.interpretation_records() {
            if self.enabled.contains(&record.id) {
                continue;
            }
            let same_to = self.key_of(goal) == self.key_of(&record.to)
                || convertible(self.env, &Ctx::new(), &record.to, goal).map_err(|error| {
                    format!(
                        "无法判定目标「{}」是否与解释 `{}` 的 to 等价：{error}",
                        print_expr(goal),
                        record.id
                    )
                })?;
            if !same_to {
                continue;
            }
            if !self.holds(&fixed.rule_facts, &record.from)? {
                continue;
            }
            out.push(InterpretationHint {
                id: record.id,
                from: record.from,
                to: record.to,
            });
        }
        Ok(out)
    }

    /// Demand a universal-elimination instance for `goal`.
    ///
    /// This is the query-level trigger: the goal itself is a closed
    /// proposition, so an environment universal fact whose body unifies with it
    /// yields one instance that proves the goal without any rule. The
    /// instance is derived, not assumed: it is not registered as a fact and it
    /// carries the universal declaration's identity, not a case fact's.
    ///
    /// The call must happen before [`Reasoner::saturate`], which includes the
    /// demanded instances in the fact base and records them as derivation
    /// nodes. Repeated demands are idempotent. `Ok(None)` means no universal
    /// fact produced a legal instance; the goal stays unproved and the gap
    /// report says why.
    pub fn demand(&self, goal: &Expr) -> Result<Option<AxiomInstance>, String> {
        self.demand_axiom(goal)
    }

    /// The universal-elimination instance already demanded for `goal`, if any.
    ///
    /// It answers without deriving anything: `None` means no instance was
    /// demanded, not that no instance is possible.
    pub fn axiom_instance_for(&self, goal: &Expr) -> Option<AxiomInstance> {
        self.axiom_state
            .borrow()
            .instances
            .get(&self.key_of(goal))
            .cloned()
    }

    /// Derive at most one instance of the universal facts that can conclude
    /// `goal`, caching both hits and misses.
    ///
    /// Candidates are filtered by the normalized head of the goal against the
    /// normalized head of each declaration's body, then tried in axiom-name
    /// order. Matching is deterministic and single-valued: the goal is closed,
    /// so each binder has exactly one possible value, and a repeated binder
    /// must meet an identical term. There is therefore at most one attempt per
    /// declaration per goal; the per-goal candidate and per-query probe and
    /// instance bounds are the explicit limits.
    fn demand_axiom(&self, goal: &Expr) -> Result<Option<AxiomInstance>, String> {
        if let Some(error) = &self.axiom_error {
            return Err(error.clone());
        }
        if self.axioms.is_empty() || has_open_pattern(goal) || !is_closed(goal) {
            return Ok(None);
        }
        if check::check(self.env, &Ctx::new(), goal, &Expr::Sort(0)).is_err() {
            return Ok(None);
        }
        let key = self.key_of(goal);
        {
            let state = self.axiom_state.borrow();
            if let Some(instance) = state.instances.get(&key) {
                return Ok(Some(instance.clone()));
            }
            if state.probed.contains(&key) {
                return Ok(None);
            }
            if state.probed.len() >= MAX_AXIOM_PROBES_PER_QUERY {
                return Err(format!(
                    "公理实例化在本次查询中探测的目标超过 {MAX_AXIOM_PROBES_PER_QUERY} 个上限"
                ));
            }
        }
        let trials = self.axiom_trials(goal)?;
        let mut state = self.axiom_state.borrow_mut();
        state.probed.insert(key);
        for trial in trials {
            let AxiomTrial::Instantiated(instance) = trial else {
                continue;
            };
            let conclusion_key = self.key_of(&instance.conclusion);
            if !state.instances.contains_key(&conclusion_key)
                && state.instances.len() >= MAX_AXIOM_INSTANCES_PER_QUERY
            {
                return Err(format!(
                    "公理实例化的结论超过本次查询 {MAX_AXIOM_INSTANCES_PER_QUERY} 个上限"
                ));
            }
            let stored = state
                .instances
                .entry(conclusion_key)
                .or_insert_with(|| instance.clone());
            // The instance stored under this conclusion may have been derived
            // from an earlier axiom; the cached one is the stable answer.
            return Ok(Some(stored.clone()));
        }
        Ok(None)
    }

    /// Every universal fact whose body unifies with `goal`, with the unified
    /// bindings and either the instance or the reason it was refused.
    ///
    /// This never changes the derivation: the gap report uses it to explain
    /// that a goal is only obtainable by instantiating a universal fact and
    /// which values that would need.
    fn axiom_trials(&self, goal: &Expr) -> Result<Vec<AxiomTrial>, String> {
        if let Some(error) = &self.axiom_error {
            return Err(error.clone());
        }
        if self.axioms.is_empty() || has_open_pattern(goal) || !is_closed(goal) {
            return Ok(Vec::new());
        }
        let normalized_goal = normalize(self.env, &Ctx::new(), goal).map_err(|error| {
            format!(
                "无法规范化目标「{}」以尝试公理实例化：{error}",
                print_expr(goal)
            )
        })?;
        let Some(head) = normalized_goal.head_const() else {
            return Ok(Vec::new());
        };
        let Some(candidates) = self.axioms.get(&head) else {
            return Ok(Vec::new());
        };
        if candidates.len() > MAX_AXIOM_CANDIDATES_PER_GOAL {
            return Err(format!(
                "目标「{}」的谓词 `{head}` 有 {} 条全称公理候选，超过每个目标 {MAX_AXIOM_CANDIDATES_PER_GOAL} 条的上限",
                print_expr(goal),
                candidates.len()
            ));
        }
        let mut trials = Vec::new();
        for axiom in candidates {
            // Structural match first, against the goal as written and then
            // against both normal forms. Each attempt starts from an empty
            // binding: a failed match may have recorded values for the prefix
            // it got through, and those must not leak into the next attempt.
            let mut binding = Vec::new();
            if match_axiom_body(&axiom.body, goal, 0, axiom.binders.len(), &mut binding) {
                trials.push(self.instantiate_trial(axiom, binding, goal)?);
                continue;
            }
            let mut normalized_binding = Vec::new();
            if match_axiom_body(
                &axiom.normalized_body,
                &normalized_goal,
                0,
                axiom.binders.len(),
                &mut normalized_binding,
            ) {
                trials.push(self.instantiate_trial(axiom, normalized_binding, goal)?);
                continue;
            }
            // The axiom writes an operation (`合计 甲 (x + 0)`); the goal is
            // already its value (`合计 甲 5000`). Every equivalent spelling of
            // the same proposition has the same normal form, so a value the
            // operation can consume is drawn from that normal form and the
            // whole instance is evaluated before it is compared with the goal.
            // The two paths share one judgement: this is the same
            // `instantiate_trial` the structural match uses, so a proof and a
            // gap candidate can never disagree about whether the axiom applies.
            if !contains_builtin_arithmetic(&axiom.normalized_body) {
                continue;
            }
            let assignments = value_bindings(axiom, &normalized_goal)?;
            for assignment in assignments {
                let trial = self.instantiate_trial(axiom, assignment, goal)?;
                if let AxiomTrial::Instantiated(_) = trial {
                    trials.push(trial);
                    break;
                }
            }
        }
        Ok(trials)
    }

    /// Turn one successful structural match into an instance, or explain why
    /// the match cannot be a legal elimination step.
    fn instantiate_trial(
        &self,
        axiom: &AxiomDecl,
        binding: Vec<(usize, Expr)>,
        goal: &Expr,
    ) -> Result<AxiomTrial, String> {
        let mut values: Vec<Option<Expr>> = vec![None; axiom.binders.len()];
        for (position, value) in binding {
            values[position] = Some(value);
        }
        let complete: Option<Vec<Expr>> = values.into_iter().collect();
        let Some(values) = complete else {
            return Ok(AxiomTrial::Refused {
                axiom: axiom.name.clone(),
                bindings: Vec::new(),
                problem: "公理体的绑定没有覆盖每个绑定变量，无法形成完整实例".to_owned(),
            });
        };
        let ordered: Vec<(Name, Expr)> = axiom
            .binders
            .iter()
            .cloned()
            .zip(values.iter().cloned())
            .collect();
        for (name, value) in &ordered {
            if !is_closed(value) {
                return Ok(AxiomTrial::Refused {
                    axiom: axiom.name.clone(),
                    bindings: ordered.clone(),
                    problem: format!(
                        "绑定变量 `{name}` 的值 `{}` 不是闭合项（会捕获变量）",
                        print_expr(value)
                    ),
                });
            }
        }
        let raw = instantiate_telescope(&axiom.body, &values);
        // Applying the declaration to the values makes the kernel check every
        // value against its binder domain and confirms the substituted body is
        // the instance's type. Checking the application against the computed
        // body ties both sides together.
        let applied = Expr::apps(Expr::constant(&axiom.name), values.iter().cloned());
        if let Err(error) = check::check(self.env, &Ctx::new(), &applied, &raw) {
            return Ok(AxiomTrial::Refused {
                axiom: axiom.name.clone(),
                bindings: ordered,
                problem: format!("绑定值不满足公理的参数类型：{error}"),
            });
        }
        if !is_closed(&raw) {
            return Ok(AxiomTrial::Refused {
                axiom: axiom.name.clone(),
                bindings: ordered,
                problem: "实例化后的结论不是闭合命题（绑定不足或发生变量捕获）".to_owned(),
            });
        }
        // The instance's conclusion is the value of the substituted body; an
        // `i64` overflow here is an error, never a term that survives because
        // the binding path happened to be `x + 0` instead of `5000`. The
        // certificate records this evaluated form, and `cert::check` recomputes
        // the body from the same bindings and compares by kernel conversion,
        // so the two sides agree.
        let conclusion = evaluate_arithmetic(self.env, &raw).map_err(|error| {
            format!(
                "公理 `{}` 的实例结论无法计算：{error}（结论写的是「{}」）",
                axiom.name,
                print_expr(&raw)
            )
        })?;
        let same = convertible(self.env, &Ctx::new(), &conclusion, goal).map_err(|error| {
            format!(
                "无法判定公理 `{}` 的实例结论「{}」与目标「{}」是否等价：{error}",
                axiom.name,
                print_expr(&conclusion),
                print_expr(goal)
            )
        })?;
        if !same {
            return Ok(AxiomTrial::Refused {
                axiom: axiom.name.clone(),
                bindings: ordered,
                problem: format!(
                    "实例化后的结论「{}」与目标「{}」在内核下不等价",
                    print_expr(&conclusion),
                    print_expr(goal)
                ),
            });
        }
        Ok(AxiomTrial::Instantiated(AxiomInstance {
            axiom: axiom.name.clone(),
            identity: axiom.identity,
            bindings: ordered,
            conclusion,
            sources: axiom.sources.clone(),
        }))
    }

    /// The universal facts that could instantiate `goal`, as gap diagnostics.
    ///
    /// Only declarations whose body unifies with the goal are listed; an
    /// instantiated one has no problem, a refused one carries the reason. An
    /// instance that succeeds closes the goal and never appears in a real gap,
    /// so the `None` case is what a gap normally shows for a nested premise the
    /// current derivation did not demand.
    fn axiom_candidates(&self, goal: &Expr) -> Result<Vec<AxiomCandidate>, String> {
        let mut out = Vec::new();
        for trial in self.axiom_trials(goal)? {
            match trial {
                AxiomTrial::Instantiated(instance) => out.push(AxiomCandidate {
                    axiom: instance.axiom,
                    bindings: instance.bindings,
                    problem: None,
                }),
                AxiomTrial::Refused {
                    axiom,
                    bindings,
                    problem,
                } => out.push(AxiomCandidate {
                    axiom,
                    bindings,
                    problem: Some(problem),
                }),
            }
        }
        Ok(out)
    }

    /// Register an assumption together with the identity of the fact it
    /// records. Its type must be a proposition.
    ///
    /// A `disputed` proposition records what the other side claims, not what is
    /// proved, so it cannot be an assumption. One proposition has exactly one
    /// identity: conflict resolution reads that identity as evidence, so the
    /// same proposition cannot be registered once as a strict fact and once as
    /// a mere claim. Registering the same proposition again under the same
    /// identity is allowed.
    pub fn assume(
        &mut self,
        prop: &Expr,
        identity: FactIdentity,
        sources: Vec<SourceRef>,
        label: Option<String>,
    ) -> Result<(), String> {
        // A hand-registered assumption records no occurrence: only a ledger
        // fact carries `occurred_at` / `occurred_in`, and a query date is not
        // the fact's date.
        self.assume_with_occurrence(prop, identity, sources, label, None, None)
    }

    /// Register an assumption together with the occurrence the ledger fact
    /// records. The public [`Reasoner::assume`] delegates here with `None`; the
    /// occurrence is evidence about the case, so it travels with the
    /// assumption instead of being looked up from a printed name later.
    fn assume_with_occurrence(
        &mut self,
        prop: &Expr,
        identity: FactIdentity,
        sources: Vec<SourceRef>,
        label: Option<String>,
        occurred_at: Option<String>,
        occurred_in: Option<String>,
    ) -> Result<(), String> {
        if identity == FactIdentity::Disputed {
            return Err("争议事实不能作为假设：它断言的是对方的主张，不是已证明的命题".into());
        }
        // A fact with no provenance is not an assumption that can be audited;
        // accepting it would present an unsourced assertion as proved. A
        // whitespace-only source names nothing and is refused for the same
        // reason. There is deliberately no fallback source here.
        if !sources
            .iter()
            .any(|s| !s.text.trim().is_empty() && !s.locator.trim().is_empty())
        {
            return Err("假设必须有来源：来源不能是空白，没有出处的“事实”不能被当作已证明".into());
        }
        check::check(self.env, &Ctx::new(), prop, &Expr::Sort(0))
            .map_err(|e| format!("假设不是命题：{e}"))?;
        // Exact integer arithmetic in an asserted proposition is evaluated
        // here, so an overflowing literal is reported when the fact is
        // registered instead of silently surviving as an unevaluated term.
        evaluate_arithmetic(self.env, prop)
            .map_err(|error| format!("假设「{}」的整数运算失败：{error}", print_expr(prop)))?;
        // One proposition has one identity. Comparisons use kernel
        // conversion, not the printed or normalized form: alpha- and
        // eta-variants are the same proposition, and a string key would let a
        // second registration smuggle in a different identity.
        let prop_key = self.key_of(prop);
        for recorded in &self.assumptions {
            let same = if self.key_of(&recorded.prop) == prop_key {
                true
            } else {
                convertible(self.env, &Ctx::new(), &recorded.prop, prop)
                    .map_err(|error| format!("无法判定假设命题是否等价：{error}"))?
            };
            if same && recorded.identity != identity {
                return Err(format!(
                    "同一命题只能有一种事实身份：`{}` 已登记为{}，不能同时是{}",
                    print_expr(prop),
                    recorded.identity.label_zh(),
                    identity.label_zh()
                ));
            }
        }
        self.assumptions.push(Assumption {
            prop: prop.clone(),
            identity,
            sources,
            label,
            occurred_at,
            occurred_in,
        });
        // The occurrence index must not keep serving a stale table after a new
        // fact (with its own event records) was registered.
        *self.occurrence_index.borrow_mut() = None;
        Ok(())
    }

    /// The identity recorded for the assumption of `prop`, if this reasoner
    /// holds one.
    ///
    /// The identity is evidence: conflict resolution reads it from the same
    /// assumption table, so a display layer must read it here rather than infer
    /// it from the printed proposition. A proposition the reasoner only derived
    /// has no identity.
    pub fn identity_of(&self, prop: &Expr) -> Option<FactIdentity> {
        self.assumption_identity(&self.key_of(prop))
    }

    /// The identity recorded for the assumption whose normalized key is
    /// `key`, if the reasoner holds such an assumption.
    fn assumption_identity(&self, key: &str) -> Option<FactIdentity> {
        self.assumptions
            .iter()
            .find(|assumption| self.key_of(&assumption.prop) == key)
            .map(|assumption| assumption.identity)
    }

    /// Register every fact in the ledger as an assumption, carrying its
    /// identity.
    ///
    /// A `Fact` records who asserts it. `verified` and `stipulated` facts are
    /// strict and outrank a defeasible conclusion; `user_asserted` and
    /// `assumed` facts are claims that may seed a derivation and block an
    /// `unless`, but never automatically beat a rule conclusion. A `Disputed`
    /// fact is not seeded at all — it asserts what the other side claims, not
    /// what is the case.
    ///
    /// `Axiom` declarations (`axiom 假 : Prop`) only name a constant and
    /// assert nothing. Such declarations contribute nothing to reasoning and
    /// are skipped.
    ///
    /// Rules are declarations too, but they drive the reasoner rather than
    /// seed it, so they are not assumptions.
    pub fn assume_ledger_axioms(&mut self) -> Result<(), String> {
        // Sorted by declaration name: the assumption list feeds the node
        // order, so it must not depend on the order independent packages were
        // loaded in.
        let env = self.env;
        let mut facts: Vec<&Decl> = env
            .iter()
            .filter(|decl| {
                matches!(
                    &decl.kind,
                    DeclKind::Fact { identity } if identity.seeds_derivation()
                )
            })
            .collect();
        facts.sort_by(|a, b| a.name.cmp(&b.name));
        for decl in facts {
            // The language gives every proposition-typed `axiom` a `Fact`
            // entry, but the reasoner also accepts environments built
            // directly, so it still refuses to assume a declaration whose
            // type is not a proposition.
            if !declared_type_is_prop(self.env, &decl.ty) {
                continue;
            }
            let DeclKind::Fact { identity } = &decl.kind else {
                continue;
            };
            self.assume_with_occurrence(
                &decl.ty,
                *identity,
                decl.sources.clone(),
                Some(decl.name.to_string()),
                decl.occurred_at.clone(),
                decl.occurred_in.clone(),
            )?;
        }
        Ok(())
    }

    fn key_of(&self, e: &Expr) -> String {
        key(self.env, e)
    }

    /// Compute the least fixed point, then build the derivation.
    ///
    /// Conflict resolution is layered on top: a conclusion that loses, or an
    /// unresolved pair, is removed from the fact base, and the fixed point is
    /// recomputed without it. Removals only accumulate, so the loop
    /// terminates; each round is still a full recomputation, so `unless`
    /// retractions remain correct.
    pub fn saturate(&mut self) -> Result<(), String> {
        let mut removed: BTreeSet<String> = BTreeSet::new();
        let mut seen: BTreeMap<(String, String), Conflict> = BTreeMap::new();

        for _ in 0..self.max_rounds {
            let mut facts = self.fixed_point(&removed)?;
            // Snapshot the rule-visible set before any interpretation runs:
            // rules never consume an interpretation conclusion, so a gap
            // candidate must not treat one as a satisfied premise.
            let rule_facts = facts.clone();
            // Interpretations are one explicit step after the rule fixed
            // point. They read only the registered facts and rule conclusions;
            // no rule runs afterwards, and no interpretation reads another
            // interpretation's conclusion, so there is no interpretation
            // chain.
            let applications = self.apply_interpretations(&mut facts, &removed)?;
            let conflicts = self.detect_conflicts(&facts, &rule_facts, &applications)?;
            let mut next_removed = removed.clone();
            for c in &conflicts {
                let lk = self.key_of(&c.left);
                let rk = self.key_of(&c.right);
                seen.insert((lk, rk), c.clone());
                match &c.resolution {
                    Resolution::Unresolved { .. } => {
                        next_removed.insert(self.key_of(&c.left));
                        next_removed.insert(self.key_of(&c.right));
                    }
                    Resolution::Defeated { winner, .. } => {
                        let loser = match winner {
                            Side::Left => &c.right,
                            Side::Right => &c.left,
                        };
                        next_removed.insert(self.key_of(loser));
                    }
                }
            }

            if next_removed == removed {
                let mut conflicts: Vec<Conflict> = seen
                    .values()
                    .filter(|c| {
                        removed.contains(&self.key_of(&c.left))
                            || removed.contains(&self.key_of(&c.right))
                    })
                    .cloned()
                    .collect();
                conflicts.sort_by_key(|c| (self.key_of(&c.left), self.key_of(&c.right)));
                let mut contested = BTreeMap::new();
                for c in &conflicts {
                    contested.insert(self.key_of(&c.left), c.clone());
                    contested.insert(self.key_of(&c.right), c.clone());
                }
                let fixed = self.build_nodes(
                    facts,
                    rule_facts,
                    conflicts,
                    contested,
                    applications,
                    self.axiom_state.borrow().instances.clone(),
                )?;
                self.fixed = Some(fixed);
                return Ok(());
            }
            removed = next_removed;
        }
        Err("冲突裁决在 256 轮内未收敛".into())
    }

    /// Apply every enabled interpretation whose `from` already holds.
    ///
    /// The base fact set is snapshotted first, so two interpretations enabled
    /// in the same query cannot chain: each one reads only the registered
    /// facts and the rule conclusions, never a conclusion another enabled
    /// interpretation just licensed. The result maps a conclusion key to the
    /// interpretation that licensed it; an interpretation whose `to` is
    /// already established by a fact or a rule is not applied again.
    ///
    /// "Already established" is kernel conversion, not the structural key: an
    /// alpha variant of a quantified fact is the same proposition, and adding
    /// a second step for it would be a redundant interpretation application.
    fn apply_interpretations(
        &self,
        facts: &mut BTreeMap<String, Expr>,
        removed: &BTreeSet<String>,
    ) -> Result<BTreeMap<String, Name>, String> {
        let mut applications = BTreeMap::new();
        if self.enabled.is_empty() {
            return Ok(applications);
        }
        let base = facts.clone();
        for record in self.enabled_records() {
            let key = self.key_of(&record.to);
            if removed.contains(&key) {
                continue;
            }
            if self.holds(&base, &record.to)? {
                continue;
            }
            if !self.holds(&base, &record.from)? {
                continue;
            }
            facts.insert(key.clone(), record.to.clone());
            applications.insert(key, record.id);
        }
        Ok(applications)
    }

    fn fixed_point(&self, removed: &BTreeSet<String>) -> Result<BTreeMap<String, Expr>, String> {
        let seeds: BTreeMap<String, Expr> = self
            .assumptions
            .iter()
            .map(|a| (self.key_of(&a.prop), a.prop.clone()))
            .filter(|(k, _)| !removed.contains(k))
            .collect();
        let mut k = seeds.clone();
        self.add_demanded_instances(&mut k, removed);
        let mut previous: Option<BTreeMap<String, Expr>> = None;

        for _round in 0..self.max_rounds {
            let mut next = seeds.clone();
            self.add_demanded_instances(&mut next, removed);
            for decl in self.ordered_rules() {
                let DeclKind::Rule(rule) = &decl.kind else {
                    continue;
                };
                // A rule instance the case excludes contributes no conclusion
                // at all. It is not merely hidden later: it must never seed a
                // premise, an `unless` blocker or a conflict side. The verdict
                // is per instance because it depends on the facts it consumes.
                for inst in self.enumerate_demanding(&decl.name, rule, &k, removed)? {
                    // Guards are instance conditions: a false one keeps the
                    // rule from firing exactly as an unmet premise would, but
                    // the instance is still reported by the gap scan. The
                    // order is: guard first (does this binding meet the rule's
                    // own condition?), then `unless` (is there an exception?),
                    // then the applicability judgement.
                    if !guards_hold(&inst.guard_judgements) {
                        continue;
                    }
                    if blocked(&inst.unlesses, &k, self.env)? {
                        continue;
                    }
                    if !self
                        .judge_instance(&decl.scope, &inst.premise_keys)
                        .allows_firing()
                    {
                        continue;
                    }
                    next.entry(self.key_of(&inst.conclusion))
                        .or_insert_with(|| inst.conclusion.clone());
                }
            }
            // Premises probed while enumerating may have demanded new
            // universal instances; they join the next set in the same round,
            // so the rule that needed them fires on the next one.
            self.add_demanded_instances(&mut next, removed);
            next.retain(|key, _| !removed.contains(key));
            if same_keys(&k, &next) {
                return Ok(next);
            }
            if let Some(p) = &previous {
                if same_keys(p, &next) {
                    return Err(
                        "推理在两组结论之间来回振荡：存在互相以 unless 阻断的规则环。\
                         这需要人工裁决，系统不替你选。"
                            .into(),
                    );
                }
            }
            previous = Some(k);
            k = next;
        }
        Err("推理在 256 轮内未收敛：可能存在规则环".into())
    }

    /// Add every demanded universal-elimination instance to `facts`.
    ///
    /// Instances are keyed by their conclusion and are added only when no
    /// assumption already holds the same conclusion: an asserted proposition is
    /// supported by the fact, not by an instantiation. A conclusion removed by
    /// a conflict is not re-added.
    fn add_demanded_instances(
        &self,
        facts: &mut BTreeMap<String, Expr>,
        removed: &BTreeSet<String>,
    ) {
        let instances = self.axiom_state.borrow();
        for (key, instance) in &instances.instances {
            if removed.contains(key) {
                continue;
            }
            facts
                .entry(key.clone())
                .or_insert_with(|| instance.conclusion.clone());
        }
    }

    /// Enumerate instances of `rule` against `facts`, demanding a universal
    /// instance for a premise that no fact satisfies but which is closed and
    /// has a matching universal fact.
    ///
    /// Instantiation is premise-driven: the premise's own argument terms
    /// determine every binder value, so nothing is enumerated object by object.
    /// Only a premise that is already closed under the bindings collected so
    /// far can drive it; a premise that still mentions an undetermined rule
    /// parameter is reported as a gap instead of guessed.
    fn enumerate_demanding(
        &self,
        rule_name: &str,
        rule: &RuleDecl,
        facts: &BTreeMap<String, Expr>,
        removed: &BTreeSet<String>,
    ) -> Result<Vec<Instance>, String> {
        let mut out = Vec::new();
        let mut binding: Vec<(Name, Expr)> = Vec::new();
        let mut keys: Vec<String> = Vec::new();
        let mut selections: Vec<PremiseSelection> = (0..rule.premises.len())
            .map(|_| PremiseSelection::Plain)
            .collect();
        let mut budget = SelectionBudget::new();
        let matching = Matching {
            env: self.env,
            rule_name,
            rule,
            facts,
        };
        premise_walk(
            &matching,
            Some((self, removed)),
            0,
            &mut binding,
            &mut keys,
            &mut selections,
            &mut budget,
            &mut out,
        )?;
        Ok(out)
    }

    /// Every rule declaration of the environment, ordered by name, so that
    /// iteration never depends on the order independent packages were loaded
    /// in.
    fn ordered_rules(&self) -> Vec<&'a Decl> {
        let mut rules = self.env.rules();
        rules.sort_by(|a, b| a.name.cmp(&b.name));
        rules
    }

    fn detect_conflicts(
        &self,
        facts: &BTreeMap<String, Expr>,
        rule_facts: &BTreeMap<String, Expr>,
        applications: &BTreeMap<String, Name>,
    ) -> Result<Vec<Conflict>, String> {
        let items: Vec<(&String, &Expr)> = facts.iter().collect();
        // Normalize each proposition once, not once per pair: the conflict
        // relation is about the kernel's view of both sides, and rebuilding
        // that view for every pair would make the quadratic scan quadratic in
        // normalization work as well.
        let mut views: Vec<Option<ConflictView>> = Vec::with_capacity(items.len());
        for (_, expression) in &items {
            views.push(conflict_view(self.env, expression)?);
        }
        let mut out = Vec::new();
        for i in 0..items.len() {
            for j in (i + 1)..items.len() {
                let (Some(left_view), Some(right_view)) = (&views[i], &views[j]) else {
                    continue;
                };
                if !in_conflict(&self.declarations, left_view, right_view) {
                    continue;
                }
                let (ka, a) = items[i];
                let (kb, b) = items[j];
                let left = self.support(ka, rule_facts, applications)?;
                let right = self.support(kb, rule_facts, applications)?;
                let resolution = self.resolve(&left, &right);
                out.push(Conflict {
                    left: a.clone(),
                    right: b.clone(),
                    left_by: left.provenance(),
                    right_by: right.provenance(),
                    resolution,
                });
            }
        }
        Ok(out)
    }

    /// How one side of a conflict is supported: a fact recorded in the
    /// assumption table, with its identity, an interpretation application, a
    /// rule conclusion with the rules that can still be rebuilt as its
    /// witnesses, or a universal-elimination instance.
    ///
    /// A rule witness is preferred over a universal instance when both can
    /// conclude the proposition: the certificate records one step per
    /// conclusion, and the rule chain is the fuller argument.
    fn support(
        &self,
        target: &str,
        rule_facts: &BTreeMap<String, Expr>,
        applications: &BTreeMap<String, Name>,
    ) -> Result<Support, String> {
        if let Some(identity) = self.assumption_identity(target) {
            return Ok(Support::Fact(identity));
        }
        if let Some(interpretation) = applications.get(target) {
            return Ok(Support::Interpretation(interpretation.clone()));
        }
        let derivers = self.derivers(target, rule_facts)?;
        if !derivers.is_empty() {
            return Ok(Support::Rules(derivers));
        }
        if let Some(instance) = self.axiom_state.borrow().instances.get(target) {
            return Ok(Support::Axiom(instance.axiom.clone()));
        }
        Ok(Support::Rules(Vec::new()))
    }

    /// Every rule that has an unblocked instance concluding `target`, with all
    /// premises already in `facts`.
    fn derivers(&self, target: &str, facts: &BTreeMap<String, Expr>) -> Result<Vec<Name>, String> {
        let mut out = BTreeSet::new();
        for decl in self.ordered_rules() {
            let DeclKind::Rule(rule) = &decl.kind else {
                continue;
            };
            for inst in self.enumerate(&decl.name, rule, facts)? {
                if self.key_of(&inst.conclusion) != target {
                    continue;
                }
                // A guard that does not hold is an instance condition that is
                // false, so this instance is not a witness: `enumerate` keeps
                // the instance (gap reports need it) and the firing rules are
                // checked here.
                if !guards_hold(&inst.guard_judgements) {
                    continue;
                }
                if blocked(&inst.unlesses, facts, self.env)? {
                    continue;
                }
                // A rule that does not apply to this instance is no witness.
                // Counting it here would let a priority resolve a conflict
                // through an inapplicable rule, and would make a rebuilt
                // derivation cite a step that never fired.
                if !self
                    .judge_instance(&decl.scope, &inst.premise_keys)
                    .allows_firing()
                {
                    continue;
                }
                if inst.premise_keys.iter().all(|pk| facts.contains_key(pk)) {
                    out.insert(decl.name.clone());
                }
            }
        }
        Ok(out.into_iter().collect())
    }

    /// Decide a conflict from the support on each side.
    ///
    /// A strict fact (`verified` / `stipulated`) wins over a rule conclusion
    /// and over a claim: being merely asserted is not evidence against a
    /// proved fact. Two strict facts have no order between them, and two
    /// claims are both unproved, so those conflicts are unresolved. A claim
    /// against a rule conclusion is unresolved as well: the claim cannot
    /// automatically beat the rule conclusion, and the rule conclusion cannot
    /// prove the claim false. Between rules, a side wins only when every rule
    /// on it beats every rule on the other side through a declared priority
    /// that is not part of a cycle, and the other side is not covered in
    /// return. Priorities are not transitive and are never guessed: anything
    /// else is unresolved, with the reason.
    fn resolve(&self, left: &Support, right: &Support) -> Resolution {
        match (left, right) {
            (Support::Fact(left), Support::Fact(right)) => {
                match (left.is_strict(), right.is_strict()) {
                    (true, false) => Resolution::Defeated {
                        winner: Side::Left,
                        basis: ResolutionBasis::Assumption,
                    },
                    (false, true) => Resolution::Defeated {
                        winner: Side::Right,
                        basis: ResolutionBasis::Assumption,
                    },
                    _ => Resolution::Unresolved {
                        reason: UnresolvedReason::ConflictingAssumptions,
                    },
                }
            }
            (Support::Fact(identity), Support::Rules(_))
            | (Support::Fact(identity), Support::Axiom(_))
            | (Support::Fact(identity), Support::Interpretation(_)) => {
                if identity.is_strict() {
                    Resolution::Defeated {
                        winner: Side::Left,
                        basis: ResolutionBasis::Assumption,
                    }
                } else {
                    Resolution::Unresolved {
                        reason: UnresolvedReason::NonStrictFact {
                            identity: *identity,
                        },
                    }
                }
            }
            (Support::Rules(_), Support::Fact(identity))
            | (Support::Axiom(_), Support::Fact(identity))
            | (Support::Interpretation(_), Support::Fact(identity)) => {
                if identity.is_strict() {
                    Resolution::Defeated {
                        winner: Side::Right,
                        basis: ResolutionBasis::Assumption,
                    }
                } else {
                    Resolution::Unresolved {
                        reason: UnresolvedReason::NonStrictFact {
                            identity: *identity,
                        },
                    }
                }
            }
            // A priority orders rules only. A universal fact is not a rule,
            // so it cannot carry a declared priority either; a conflict
            // between a universal instance and a rule or another instance
            // stays unresolved for want of an order.
            (Support::Axiom(_), Support::Axiom(_))
            | (Support::Axiom(_), Support::Rules(_))
            | (Support::Rules(_), Support::Axiom(_))
            | (Support::Interpretation(_), Support::Interpretation(_))
            | (Support::Interpretation(_), Support::Rules(_))
            | (Support::Rules(_), Support::Interpretation(_))
            | (Support::Interpretation(_), Support::Axiom(_))
            | (Support::Axiom(_), Support::Interpretation(_)) => Resolution::Unresolved {
                reason: UnresolvedReason::NoPriority,
            },
            (Support::Rules(l), Support::Rules(r)) => {
                // An empty witness list means the conclusion was derived but
                // its witnesses can no longer be rebuilt. It must never let
                // the other side win: the earlier "every rule on the other
                // side" test was vacuously true for an empty side.
                if l.is_empty() || r.is_empty() {
                    return Resolution::Unresolved {
                        reason: UnresolvedReason::UnknownWitnesses,
                    };
                }
                let win_left = self.beats(l, r);
                let win_right = self.beats(r, l);
                match (win_left, win_right) {
                    (true, false) => Resolution::Defeated {
                        winner: Side::Left,
                        basis: ResolutionBasis::Priority {
                            edges: self.cover(l, r),
                        },
                    },
                    (false, true) => Resolution::Defeated {
                        winner: Side::Right,
                        basis: ResolutionBasis::Priority {
                            edges: self.cover(r, l),
                        },
                    },
                    _ => {
                        let declared = self.declared_between(l, r);
                        if declared.is_empty() {
                            Resolution::Unresolved {
                                reason: UnresolvedReason::NoPriority,
                            }
                        } else {
                            Resolution::Unresolved {
                                reason: UnresolvedReason::PriorityUnusable { declared },
                            }
                        }
                    }
                }
            }
        }
    }

    /// Does every rule of `winners` beat every rule of `losers` through an
    /// effective (non-cyclic) declared priority edge?
    fn beats(&self, winners: &[Name], losers: &[Name]) -> bool {
        !winners.is_empty()
            && !losers.is_empty()
            && winners.iter().all(|winner| {
                losers.iter().all(|loser| {
                    self.effective
                        .get(winner)
                        .is_some_and(|beaten| beaten.contains(loser))
                })
            })
    }

    /// Every declared edge from the winning side to the losing side, sorted by
    /// [`PriorityEdge::sort_key`]. The winner was established by
    /// [`Reasoner::beats`], so each pair is covered; several packages may have
    /// declared the same order.
    fn cover(&self, winners: &[Name], losers: &[Name]) -> Vec<PriorityEdge> {
        let mut edges = Vec::new();
        for winner in winners {
            for loser in losers {
                if let Some(declarations) = self.declared.get(&(winner.clone(), loser.clone())) {
                    edges.extend(declarations.iter().cloned());
                }
            }
        }
        edges.sort_by_key(PriorityEdge::sort_key);
        // A rule may stand on both sides of a conflict, so enumerating by
        // pair can visit the same declared edge more than once.
        edges.dedup();
        edges
    }

    /// Every declared edge between the two sides in either direction, sorted
    /// by [`PriorityEdge::sort_key`]. These are the declarations that a
    /// defeated win would have to cite, and the ones an unusable priority
    /// records.
    fn declared_between(&self, left: &[Name], right: &[Name]) -> Vec<PriorityEdge> {
        let mut edges = Vec::new();
        for (winners, losers) in [(left, right), (right, left)] {
            for winner in winners {
                for loser in losers {
                    if let Some(declarations) = self.declared.get(&(winner.clone(), loser.clone()))
                    {
                        edges.extend(declarations.iter().cloned());
                    }
                }
            }
        }
        edges.sort_by_key(PriorityEdge::sort_key);
        // A rule may stand on both sides of a conflict, so enumerating both
        // directions can visit the same declared edge more than once.
        edges.dedup();
        edges
    }

    /// Construct whatever is already ready for one conclusion, and keep its
    /// remaining witnesses for a later round.
    ///
    /// A conclusion is allowed to get its first node as soon as **one** of its
    /// witnesses has all premises id'd. Waiting for every witness would
    /// deadlock two conclusions that cite each other while a third,
    /// premise-free witness (an assumption or a legal universal instance)
    /// could have broken the cycle. The remaining witnesses are appended in
    /// later rounds; the group's order is restored from their structural
    /// identities, not from creation order. A witness that never becomes ready
    /// eventually leaves the target in `waiting`; when no target makes
    /// progress, the caller reports the dependency cycle instead of silently
    /// dropping the extra witnesses.
    fn advance_witness_build(
        &self,
        target: &str,
        candidates_by_target: &mut BTreeMap<String, Vec<WitnessCandidate>>,
        ids: &mut BTreeMap<String, usize>,
        nodes: &mut Vec<Node>,
        builds: &mut BTreeMap<String, WitnessBuild>,
        waiting: &mut BTreeSet<String>,
    ) -> Result<bool, String> {
        let Some(candidates) = candidates_by_target.remove(target) else {
            return Ok(false);
        };
        if candidates.is_empty() {
            return Ok(false);
        }
        let known_total =
            builds.get(target).map_or(0, |build| build.entries.len()) + candidates.len();
        let mut ready: Vec<WitnessCandidate> = Vec::new();
        let mut not_ready: Vec<WitnessCandidate> = Vec::new();
        for candidate in candidates {
            if candidate
                .premise_keys()
                .iter()
                .all(|pk| ids.contains_key(pk))
            {
                ready.push(candidate);
            } else {
                not_ready.push(candidate);
            }
        }
        if ready.is_empty() {
            if !not_ready.is_empty() {
                candidates_by_target.insert(target.to_string(), not_ready);
            }
            return Ok(false);
        }
        let existing_entries = builds.get(target).map_or(0, |build| build.entries.len());
        let room = std_deduce_cert::MAX_CERT_WITNESSES_PER_CONCLUSION - existing_entries;
        if room == 0 {
            if let Some(build) = builds.get_mut(target) {
                build.total = build.total.max(known_total);
            }
            waiting.remove(target);
            return Ok(true);
        }
        let mut remaining: Vec<WitnessCandidate> = Vec::new();
        let mut created = false;
        for (index, candidate) in ready.into_iter().enumerate() {
            if index >= room {
                remaining.push(candidate);
                continue;
            }
            let (id, conclusion) = self.create_witness_node(nodes, &candidate, ids)?;
            let identity = candidate.identity_key(self.env);
            created = true;
            match builds.get_mut(target) {
                Some(build) => {
                    build.entries.push((identity.clone(), id));
                    build.total = build.total.max(known_total);
                    if identity < build.main_identity {
                        build.main_identity = identity;
                        build.proposition = conclusion;
                        ids.insert(target.to_string(), id);
                    }
                }
                None => {
                    builds.insert(
                        target.to_string(),
                        WitnessBuild {
                            proposition: conclusion,
                            main_identity: identity.clone(),
                            entries: vec![(identity, id)],
                            total: known_total,
                        },
                    );
                    ids.insert(target.to_string(), id);
                }
            }
        }
        remaining.extend(not_ready);
        remaining.sort_by_key(|candidate| candidate.identity_key(self.env));
        let filled = builds.get(target).map_or(0, |build| build.entries.len());
        if filled >= std_deduce_cert::MAX_CERT_WITNESSES_PER_CONCLUSION || remaining.is_empty() {
            waiting.remove(target);
        } else {
            candidates_by_target.insert(target.to_string(), remaining);
            waiting.insert(target.to_string());
        }
        Ok(created)
    }

    /// Create one witness node, refusing to exceed the certificate's node
    /// bound. The bound is shared with the certificate format, so the
    /// reasoner fails with the same limit and an actionable explanation.
    fn create_witness_node(
        &self,
        nodes: &mut Vec<Node>,
        candidate: &WitnessCandidate,
        ids: &BTreeMap<String, usize>,
    ) -> Result<(usize, Expr), String> {
        if nodes.len() >= std_deduce_cert::MAX_CERT_NODES {
            return Err(node_capacity_error(nodes.len() + 1));
        }
        let id = nodes.len();
        let conclusion = match candidate {
            WitnessCandidate::Rule {
                rule,
                instance,
                sources,
                applicability,
            } => {
                let premises: Vec<usize> = instance.premise_keys.iter().map(|pk| ids[pk]).collect();
                let conclusion = instance.conclusion.clone();
                nodes.push(Node::RuleApplication {
                    rule: rule.clone(),
                    conclusion: conclusion.clone(),
                    computed: instance.computed.clone(),
                    premises,
                    selections: instance.selections.clone(),
                    guard_judgements: instance.guard_judgements.clone(),
                    bindings: instance.bindings.clone(),
                    sources: sources.clone(),
                    applicability: Box::new((**applicability).clone()),
                });
                conclusion
            }
            WitnessCandidate::Axiom { instance } => {
                let conclusion = instance.conclusion.clone();
                nodes.push(Node::AxiomInstance {
                    axiom: instance.axiom.clone(),
                    identity: instance.identity,
                    bindings: instance.bindings.clone(),
                    conclusion: conclusion.clone(),
                    sources: instance.sources.clone(),
                });
                conclusion
            }
        };
        Ok((id, conclusion))
    }

    /// Build nodes in dependency order: an assumption first, then any rule
    /// application whose premises all already have ids.
    fn build_nodes(
        &self,
        facts: BTreeMap<String, Expr>,
        rule_facts: BTreeMap<String, Expr>,
        conflicts: Vec<Conflict>,
        contested: BTreeMap<String, Conflict>,
        applications: BTreeMap<String, Name>,
        axiom_instances: BTreeMap<String, AxiomInstance>,
    ) -> Result<Fixed, String> {
        let mut nodes: Vec<Node> = Vec::new();
        let mut ids: BTreeMap<String, usize> = BTreeMap::new();

        for a in &self.assumptions {
            let k = self.key_of(&a.prop);
            // An unresolved conflict removes both sides from the fact base, but
            // their provenance still belongs in the certificate: the conflict
            // names the side as `Provenance::Assumption`, and the certificate
            // must record what was assumed and where it came from.
            if !facts.contains_key(&k) && !contested.contains_key(&k) {
                continue;
            }
            if nodes.len() >= std_deduce_cert::MAX_CERT_NODES {
                return Err(node_capacity_error(nodes.len() + 1));
            }
            let id = nodes.len();
            nodes.push(Node::Assumption {
                prop: a.prop.clone(),
                identity: a.identity,
                sources: a.sources.clone(),
                label: a.label.clone(),
                occurred_at: a.occurred_at.clone(),
                occurred_in: a.occurred_in.clone(),
            });
            ids.insert(k, id);
        }

        // One pass over the rules builds every witness, keyed by conclusion.
        // This keeps the construction independent of how many conclusions the
        // case has; the previous per-conclusion enumeration made a big case
        // quadratic (and eight witnesses made it eight times worse).
        let mut candidates_by_target = self.witness_index(&rule_facts, &axiom_instances)?;

        // Fail before allocating a proof graph the certificate format cannot
        // carry. The estimate is exact for the witnesses the index found: each
        // pending conclusion contributes at most its witness count, capped at
        // the per-conclusion bound.
        let assumption_nodes = self
            .assumptions
            .iter()
            .filter(|a| {
                let key = self.key_of(&a.prop);
                facts.contains_key(&key) || contested.contains_key(&key)
            })
            .count();
        let witness_nodes: usize = facts
            .keys()
            .filter(|key| {
                !ids.contains_key(key.as_str()) && !applications.contains_key(key.as_str())
            })
            .map(|key| {
                candidates_by_target.get(key).map_or(0, |candidates| {
                    candidates
                        .len()
                        .min(std_deduce_cert::MAX_CERT_WITNESSES_PER_CONCLUSION)
                })
            })
            .sum();
        let contested_axiom_nodes = axiom_instances
            .iter()
            .filter(|(key, _)| {
                contested.contains_key((*key).as_str()) && !facts.contains_key((*key).as_str())
            })
            .count();
        let estimated_nodes =
            assumption_nodes + applications.len() + witness_nodes + contested_axiom_nodes;
        if estimated_nodes > std_deduce_cert::MAX_CERT_NODES {
            return Err(node_capacity_error(estimated_nodes));
        }

        let mut pending: Vec<String> = facts
            .keys()
            .filter(|k| !ids.contains_key(k.as_str()) && !applications.contains_key(k.as_str()))
            .cloned()
            .collect();
        pending.sort();
        let mut builds: BTreeMap<String, WitnessBuild> = BTreeMap::new();
        let mut waiting: BTreeSet<String> = BTreeSet::new();

        loop {
            let mut progressed = false;
            let mut i = 0;
            while i < pending.len() {
                let target = pending[i].clone();
                if self.advance_witness_build(
                    &target,
                    &mut candidates_by_target,
                    &mut ids,
                    &mut nodes,
                    &mut builds,
                    &mut waiting,
                )? {
                    pending.remove(i);
                    progressed = true;
                } else {
                    i += 1;
                }
            }
            let waiting_targets: Vec<String> = waiting.iter().cloned().collect();
            for target in waiting_targets {
                if self.advance_witness_build(
                    &target,
                    &mut candidates_by_target,
                    &mut ids,
                    &mut nodes,
                    &mut builds,
                    &mut waiting,
                )? {
                    progressed = true;
                }
            }
            if pending.is_empty() && waiting.is_empty() {
                break;
            }
            if !progressed {
                let mut stuck: Vec<String> = pending.clone();
                stuck.extend(waiting.iter().cloned());
                stuck.sort();
                stuck.dedup();
                return Err(format!(
                    "无法为以下结论构造推导（可能存在依赖环）：{}。\
                     存在见证，但没有一条见证的前提已经全部就绪；\
                     系统不会为了绕过环而退回单见证。",
                    stuck.join("，")
                ));
            }
        }

        let mut alternatives: BTreeMap<String, WitnessGroup> = BTreeMap::new();
        for (target, build) in builds {
            let mut entries = build.entries;
            entries.sort_by_key(|(identity, _)| identity.clone());
            let witnesses: Vec<usize> = entries.into_iter().map(|(_, id)| id).collect();
            let truncated = build.total > witnesses.len();
            alternatives.insert(
                target,
                WitnessGroup {
                    proposition: build.proposition,
                    witnesses,
                    truncated,
                },
            );
        }

        // A conclusion that lost an unresolved conflict is not in `facts`, but
        // the conflict records it as a universal instance; the certificate
        // needs that node so both sides of the conflict can be inspected.
        let mut contested_instances: Vec<&AxiomInstance> = axiom_instances
            .iter()
            .filter(|(key, _)| {
                contested.contains_key((*key).as_str()) && !ids.contains_key((*key).as_str())
            })
            .map(|(_, instance)| instance)
            .collect();
        contested_instances.sort_by_key(|instance| instance.sort_key(self.env));
        for instance in contested_instances {
            if nodes.len() >= std_deduce_cert::MAX_CERT_NODES {
                return Err(node_capacity_error(nodes.len() + 1));
            }
            let key = self.key_of(&instance.conclusion);
            let id = nodes.len();
            nodes.push(Node::AxiomInstance {
                axiom: instance.axiom.clone(),
                identity: instance.identity,
                bindings: instance.bindings.clone(),
                conclusion: instance.conclusion.clone(),
                sources: instance.sources.clone(),
            });
            ids.insert(key, id);
        }

        // Interpretation steps come after the facts and rule conclusions they
        // consume: their premise is, by construction, a registered fact or a
        // rule conclusion, never another interpretation's conclusion.
        let records = self.enabled_records();
        for (target, interpretation) in &applications {
            let Some(conclusion) = facts.get(target) else {
                return Err(format!(
                    "解释 `{interpretation}` 的结论不在事实库中，无法构造解释应用步"
                ));
            };
            let Some(record) = records.iter().find(|record| record.id == *interpretation) else {
                return Err(format!("解释 `{interpretation}` 不在本次启用的解释记录中"));
            };
            let premise = self.premise_node(&facts, &ids, &record.from, interpretation)?;
            if nodes.len() >= std_deduce_cert::MAX_CERT_NODES {
                return Err(node_capacity_error(nodes.len() + 1));
            }
            let id = nodes.len();
            nodes.push(Node::InterpretationApplication {
                interpretation: interpretation.clone(),
                conclusion: conclusion.clone(),
                premise,
            });
            ids.insert(target.clone(), id);
        }

        Ok(Fixed {
            facts,
            rule_facts,
            nodes,
            ids,
            alternatives,
            conflicts,
            contested,
            applications,
        })
    }

    /// The node id that proves `expression`, compared by kernel conversion.
    fn premise_node(
        &self,
        facts: &BTreeMap<String, Expr>,
        ids: &BTreeMap<String, usize>,
        expression: &Expr,
        interpretation: &Name,
    ) -> Result<usize, String> {
        if let Some(id) = ids.get(&self.key_of(expression)) {
            return Ok(*id);
        }
        for (key, fact) in facts {
            let same = convertible(self.env, &Ctx::new(), fact, expression).map_err(|error| {
                format!(
                    "无法判定解释 `{interpretation}` 的前提「{}」是否已成立：{error}",
                    print_expr(expression)
                )
            })?;
            if same {
                if let Some(id) = ids.get(key) {
                    return Ok(*id);
                }
            }
        }
        Err(format!(
            "解释 `{interpretation}` 的前提「{}」没有可引用的证明节点",
            print_expr(expression)
        ))
    }

    /// Every independent witness of every derivable conclusion, grouped by
    /// the conclusion's structural key.
    ///
    /// The rules are enumerated **once** over `rule_facts`, not once per
    /// pending conclusion: a proof graph with many derived conclusions must
    /// not make the witness index quadratic in the number of facts. Rules read
    /// only `rule_facts`, the rule-visible fact set: an interpretation
    /// conclusion is not there, so a rule that consumes one is never recorded
    /// as a witness (a certificate could never make that step pass the
    /// checker).
    ///
    /// A witness is a rule instance whose premises all hold in `rule_facts`,
    /// is not blocked by an `unless`, fires under the case applicability
    /// judgement, plus the demanded universal instance for the same
    /// conclusion. Instances of the same rule with the same binding values are
    /// one witness (their premises are the same propositions); a different
    /// rule, or the same rule with different bindings, is another. The lists
    /// are sorted by [`WitnessCandidate::identity_key`] so the construction
    /// order never depends on enumeration order.
    fn witness_index(
        &self,
        rule_facts: &BTreeMap<String, Expr>,
        axiom_instances: &BTreeMap<String, AxiomInstance>,
    ) -> Result<BTreeMap<String, Vec<WitnessCandidate>>, String> {
        let mut index: BTreeMap<String, Vec<WitnessCandidate>> = BTreeMap::new();
        for decl in self.ordered_rules() {
            let DeclKind::Rule(rule) = &decl.kind else {
                continue;
            };
            // The witness is an argument the reader may be shown, so it must
            // be an instance that could actually fire under the case
            // judgement.
            for inst in self.enumerate(&decl.name, rule, rule_facts)? {
                if blocked(&inst.unlesses, rule_facts, self.env)? {
                    continue;
                }
                // An instance whose guard did not hold never fired, so it is
                // not a witness the certificate could cite.
                if !guards_hold(&inst.guard_judgements) {
                    continue;
                }
                if !inst
                    .premise_keys
                    .iter()
                    .all(|pk| rule_facts.contains_key(pk))
                {
                    continue;
                }
                let verdict = self.judge_instance(&decl.scope, &inst.premise_keys);
                if !verdict.allows_firing() {
                    continue;
                }
                let key = self.key_of(&inst.conclusion);
                let candidate = WitnessCandidate::Rule {
                    rule: decl.name.clone(),
                    instance: inst,
                    sources: decl.sources.clone(),
                    applicability: Box::new(verdict),
                };
                let entry = index.entry(key).or_default();
                let mut duplicate = false;
                for existing in entry.iter() {
                    if same_witness(self.env, existing, &candidate)? {
                        duplicate = true;
                        break;
                    }
                }
                if !duplicate {
                    entry.push(candidate);
                }
            }
        }
        for (key, instance) in axiom_instances {
            let candidate = WitnessCandidate::Axiom {
                instance: instance.clone(),
            };
            let entry = index.entry(key.clone()).or_default();
            let mut duplicate = false;
            for existing in entry.iter() {
                if same_witness(self.env, existing, &candidate)? {
                    duplicate = true;
                    break;
                }
            }
            if !duplicate {
                entry.push(candidate);
            }
        }
        for candidates in index.values_mut() {
            candidates.sort_by_key(|candidate| candidate.identity_key(self.env));
        }
        Ok(index)
    }

    /// Enumerate instances of `rule` against `facts`.
    ///
    /// Ordered backtracking over the premise list: premise `i` is a pattern
    /// open over the rule's binders; try each known fact, match, extend the
    /// binding, recurse. Facts are ground, so this is first-order matching.
    /// A conclusion whose built-in arithmetic overflows is an error, never a
    /// skipped instance.
    fn enumerate(
        &self,
        rule_name: &str,
        rule: &RuleDecl,
        facts: &BTreeMap<String, Expr>,
    ) -> Result<Vec<Instance>, String> {
        let mut out = Vec::new();
        let mut binding: Vec<(Name, Expr)> = Vec::new();
        let mut keys: Vec<String> = Vec::new();
        let mut selections: Vec<PremiseSelection> = (0..rule.premises.len())
            .map(|_| PremiseSelection::Plain)
            .collect();
        let mut budget = SelectionBudget::new();
        let matching = Matching {
            env: self.env,
            rule_name,
            rule,
            facts,
        };
        premise_walk(
            &matching,
            None,
            0,
            &mut binding,
            &mut keys,
            &mut selections,
            &mut budget,
            &mut out,
        )?;
        Ok(out)
    }

    // ------------------------------------------------------------ queries

    /// The environment this reasoner reads. Exposed so callers can check a
    /// certificate against the same declarations the derivation used.
    pub fn env(&self) -> &Env {
        self.env
    }

    /// The burden/standard declarations of one rule, for the gap report.
    ///
    /// The gap candidate records only the rule name, so the report looks the
    /// declaration up by that name. `None` means no rule of that name is
    /// declared here; the renderer says so rather than inventing a burden.
    pub fn pleading(&self, rule: &str) -> Option<RulePleading> {
        match &self.env.get(rule)?.kind {
            DeclKind::Rule(decl) => Some(RulePleading::of_rule(decl)),
            _ => None,
        }
    }

    /// Every declared rule's burden/standard, keyed by rule name.
    ///
    /// Certificate v13 does not record these declarations (adding them would
    /// change the format), so `:explain` supplies this map when it narrates a
    /// certificate gap. The values come from the environment declaration, the
    /// same one the derivation used.
    pub fn pleadings(&self) -> BTreeMap<String, RulePleading> {
        self.env
            .rules()
            .into_iter()
            .filter_map(|decl| {
                let DeclKind::Rule(rule) = &decl.kind else {
                    return None;
                };
                Some((decl.name.to_string(), RulePleading::of_rule(rule)))
            })
            .collect()
    }

    pub fn knows(&self, prop: &Expr) -> bool {
        self.fixed
            .as_ref()
            .map(|f| f.facts.contains_key(&self.key_of(prop)))
            .unwrap_or(false)
    }

    pub fn root_for(&self, prop: &Expr) -> Option<usize> {
        self.fixed
            .as_ref()
            .and_then(|f| f.ids.get(&self.key_of(prop)).copied())
    }

    /// Conflicts recorded in the settled state. A defeated conflict is still
    /// recorded: it explains why a conclusion is absent.
    pub fn conflicts(&self) -> Vec<Conflict> {
        self.fixed
            .as_ref()
            .map(|f| f.conflicts.clone())
            .unwrap_or_default()
    }

    /// The conflict a conclusion took part in, if any.
    pub fn conflict_for(&self, prop: &Expr) -> Option<Conflict> {
        self.fixed
            .as_ref()
            .and_then(|f| f.contested.get(&self.key_of(prop)).cloned())
    }

    /// Which side of `c` the proposition sits on.
    pub fn conflict_side(&self, c: &Conflict, prop: &Expr) -> Option<Side> {
        let k = self.key_of(prop);
        if self.key_of(&c.left) == k {
            Some(Side::Left)
        } else if self.key_of(&c.right) == k {
            Some(Side::Right)
        } else {
            None
        }
    }

    pub fn derivation(&self) -> Derivation {
        match &self.fixed {
            Some(f) => Derivation {
                nodes: f.nodes.clone(),
                root: None,
                alternatives: f.alternatives.values().cloned().collect(),
                conflicts: f.conflicts.clone(),
                interpretations: self.enabled_records(),
            },
            None => Derivation::default(),
        }
    }

    /// A derivation that reaches `prop` even when it is not in the fact base.
    ///
    /// Used to show both sides of an unresolved conflict: the conclusion is
    /// not asserted, but the argument for it must still be inspectable. When
    /// the side was licensed by an enabled interpretation, the rebuilt
    /// derivation carries that application step too. The interpretation is
    /// matched against the rule-visible facts, never against the settled base
    /// with interpretation conclusions, so the reconstruction cannot invent a
    /// chain by reading another interpretation's output.
    pub fn derivation_for(&self, prop: &Expr) -> Option<Derivation> {
        let k = self.key_of(prop);
        let base = self.fixed.as_ref()?;
        let mut facts = base.facts.clone();
        facts.insert(k.clone(), prop.clone());
        let mut applications = base.applications.clone();
        if !applications.contains_key(&k) {
            // The proposition is not in the settled base: it was removed by a
            // conflict. Reconstruct its interpretation witness only when no
            // rule can still conclude it; otherwise the rule is the witness
            // the conflict recorded.
            if self.derivers(&k, &facts).ok()?.is_empty() {
                if let Ok(Some(interpretation)) =
                    self.interpretation_for(&k, prop, &base.rule_facts)
                {
                    applications.insert(k.clone(), interpretation);
                }
            }
        }
        let rule_facts: BTreeMap<String, Expr> = facts
            .iter()
            .filter(|(key, _)| !applications.contains_key(*key))
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect();
        let fixed = self
            .build_nodes(
                facts,
                rule_facts,
                Vec::new(),
                BTreeMap::new(),
                applications,
                self.axiom_state.borrow().instances.clone(),
            )
            .ok()?;
        Some(Derivation {
            root: fixed.ids.get(&k).copied(),
            nodes: fixed.nodes,
            alternatives: fixed.alternatives.values().cloned().collect(),
            conflicts: Vec::new(),
            interpretations: self.enabled_records(),
        })
    }

    /// The enabled interpretation whose `to` is kernel-equivalent to `target`
    /// and whose `from` already holds in `base`.
    ///
    /// The structural key is only a fast path: a converted-but-differently-keyed
    /// `to` (an alpha variant of a quantified proposition, an eta variant) must
    /// still be recognised as the same conclusion, so a rebuilt derivation never
    /// invents a second interpretation step for it.
    fn interpretation_for(
        &self,
        target: &str,
        target_expr: &Expr,
        base: &BTreeMap<String, Expr>,
    ) -> Result<Option<Name>, String> {
        for record in self.enabled_records() {
            let same = self.key_of(&record.to) == target
                || convertible(self.env, &Ctx::new(), &record.to, target_expr).map_err(
                    |error| format!("无法判定解释 `{}` 的 to 是否与结论等价：{error}", record.id),
                )?;
            if !same {
                continue;
            }
            if self.holds(base, &record.from)? {
                return Ok(Some(record.id));
            }
        }
        Ok(None)
    }

    /// Why is `goal` unreachable? List candidate rules with what each is
    /// missing, what is blocking it, and every universal fact whose body
    /// unifies with it.
    ///
    /// A goal that took part in a conflict gets a note that follows the
    /// recorded resolution: an unresolved conflict needs a human decision, a
    /// defeated loser is already rejected, and a winner is not described as
    /// pending. Only a goal with no conflict falls through to candidate rules.
    ///
    /// This is the one-level explanation used where a recursive tree would not
    /// fit (the gap node of a certificate). `:gap` uses
    /// [`Reasoner::gap_tree`], which expands the same candidates recursively.
    pub fn explain(&self, goal: &Expr) -> Result<GapExplanation, String> {
        let note = match self.gap_status(goal) {
            GapStatus::Proved => Some(match self.conflict_for(goal) {
                Some(conflict) => match &conflict.resolution {
                    Resolution::Defeated { winner, .. } => {
                        match self.conflict_side(&conflict, goal) {
                            Some(side) if side == *winner => {
                                "目标在该冲突中胜出：依据见冲突记录".to_string()
                            }
                            _ => "目标已可推出".to_string(),
                        }
                    }
                    // A proved goal cannot be an unresolved side.
                    Resolution::Unresolved { .. } => "目标已可推出".to_string(),
                },
                None => "目标已可推出".to_string(),
            }),
            GapStatus::InterpretedOnly => {
                Some("目标由解释推出，但规则阶段不消费解释结论".to_string())
            }
            GapStatus::Conflicted => {
                Some("目标处于冲突中：未决的结论不进入事实库，需要人工裁决".to_string())
            }
            GapStatus::Defeated => Some("目标已被否决：冲突已裁决，依据见冲突记录".to_string()),
            GapStatus::NotAProposition => Some("目标不是命题".to_string()),
            GapStatus::Unreachable | GapStatus::OpenPattern | GapStatus::Cycle => None,
        };
        let (candidates, axiom_candidates) = if note.is_some() {
            (Vec::new(), Vec::new())
        } else {
            (self.gap_candidates(goal)?, self.axiom_candidates(goal)?)
        };
        Ok(GapExplanation {
            goal: goal.clone(),
            candidates,
            axiom_candidates,
            note,
        })
    }

    /// Why is `goal` unreachable, expanded into a recursive gap tree?
    ///
    /// Each candidate rule names what it is missing, which blocking conditions
    /// already hold and where the rule comes from. Every missing premise
    /// becomes its own gap node, expanded until it reaches a fact leaf (no
    /// rule concludes it), a proposition in an unresolved conflict, a decided
    /// losing side, an open pattern or a non-proposition, or a proposition
    /// that is already being expanded on this path (a rule cycle).
    ///
    /// The expansion is bounded by [`GapLimits`]. A limit that stops a branch
    /// is recorded on the node or candidate that stopped it; nothing is
    /// silently cut off, and the recursion cannot run away: the depth cap is
    /// checked before a child is built and the node cap before it is created.
    pub fn gap_tree(&self, goal: &Expr) -> Result<GapTree, String> {
        self.gap_tree_with(goal, &GapLimits::default())
    }

    /// [`Reasoner::gap_tree`] with explicit limits.
    ///
    /// The root counts as a node. When the budget does not even allow the root
    /// (`max_nodes == 0`), a stub that carries the node limit and lists no
    /// candidate is returned: a `GapTree` is always a tree, so the limit is
    /// reported instead of silently expanding a root the budget refuses.
    pub fn gap_tree_with(&self, goal: &Expr, limits: &GapLimits) -> Result<GapTree, String> {
        let mut budget = GapBudget::new(limits);
        let mut path = Vec::new();
        if budget.nodes >= limits.max_nodes {
            return Ok(GapTree {
                goal: goal.clone(),
                status: self.gap_status(goal),
                candidates: Vec::new(),
                axiom_candidates: Vec::new(),
                limit: Some(GapLimit::Nodes {
                    limit: limits.max_nodes,
                }),
            });
        }
        self.expand_gap(goal, 0, &mut path, &mut budget)
    }

    /// Every conclusion the current fact set can still contest, each with its
    /// recursive gap tree.
    ///
    /// A conclusion is contestable when a rule can be instantiated to it for
    /// the declared constants (one object per parameter, in parameter order)
    /// and it is not already in the fact base, or when it is a side of an
    /// *unresolved* conflict. A conflict the theory already decided is not an
    /// open issue: its winner is in the fact base, and its loser is reported by
    /// [`Reasoner::gap_tree`] as `Defeated` rather than `Conflicted`.
    ///
    /// The scan reports what it could not enumerate — rules whose parameter
    /// types have no declared constant — instead of pretending the list is
    /// complete. The list and every tree are bounded by [`GapLimits`].
    pub fn issues(&self) -> Result<IssueScan, String> {
        self.issues_with(&GapLimits::default())
    }

    /// [`Reasoner::issues`] with explicit limits.
    pub fn issues_with(&self, limits: &GapLimits) -> Result<IssueScan, String> {
        let mut scan = IssueScan {
            issues: Vec::new(),
            limits: Vec::new(),
            uninstantiable: Vec::new(),
            excluded: Vec::new(),
        };
        let values = constant_values(self.env);
        // Keyed by structural identity: two rules that conclude the same
        // proposition are one issue with two candidate rules, and an alpha
        // variant does not create a second entry.
        let mut goals: BTreeMap<String, (Option<Name>, Expr)> = BTreeMap::new();
        let facts: BTreeMap<String, Expr> = self
            .fixed
            .as_ref()
            .map(|fixed| fixed.rule_facts.clone())
            .unwrap_or_default();

        for decl in self.ordered_rules() {
            let DeclKind::Rule(rule) = &decl.kind else {
                continue;
            };
            let mut instances = Vec::new();
            let mut truncated = false;
            collect_param_bindings(
                self.env,
                rule,
                &values,
                limits.max_rule_attempts,
                &mut instances,
                &mut truncated,
            );
            if truncated {
                scan.limits.push(GapLimit::RuleAttempts {
                    rule: decl.name.clone(),
                    limit: limits.max_rule_attempts,
                });
            }
            let mut stated = false;
            let mut fired_any = false;
            let mut excluded_verdicts: Vec<Applicability> = Vec::new();
            for binding in instances {
                let conclusion = close_pattern(&rule.open_conclusion(), &binding);
                // A conclusion that still mentions a premise binder is not a
                // proposition that can be stated from facts: it depends on a
                // particular proof term. Such a rule cannot produce an issue.
                if has_open_pattern(&conclusion) {
                    continue;
                }
                if check::check(self.env, &Ctx::new(), &conclusion, &Expr::Sort(0)).is_err() {
                    continue;
                }
                stated = true;
                // Judge this instance on the premise facts it actually holds.
                // A missing premise is not a fact and contributes no event
                // record; the query date must never stand in for an event time
                // that the held facts record. "Holds" is the derivation's own
                // judgment, so an instance the fixed point can fire is not
                // reported as excluded here just because its premise was
                // written through a `def` alias.
                let statuses = self.premise_statuses(&decl.name, rule, &binding, &facts)?;
                let held_keys: Vec<String> = statuses
                    .iter()
                    .filter_map(|status| status.held.as_ref().map(|held| self.key_of(held)))
                    .collect();
                let verdict = self.judge_instance(&decl.scope, &held_keys);
                // The conclusion is an issue even when this instance is
                // excluded: the gap tree must show why the rule did not fire.
                let key = structural_key(self.env, &conclusion);
                goals
                    .entry(key)
                    .or_insert_with(|| (Some(decl.name.clone()), conclusion));
                if verdict.allows_firing() {
                    fired_any = true;
                } else if !excluded_verdicts.contains(&verdict) {
                    excluded_verdicts.push(verdict);
                }
            }
            if !stated {
                scan.uninstantiable.push(decl.name.clone());
            } else if !fired_any && !excluded_verdicts.is_empty() {
                // The rule is reported as excluded only when every enumerable
                // instance is excluded; one applicable instance keeps it out of
                // this list.
                if scan.excluded.len() < limits.max_excluded {
                    scan.excluded.push(ExcludedRule {
                        rule: decl.name.clone(),
                        verdicts: excluded_verdicts,
                    });
                } else {
                    scan.limits.push(GapLimit::Excluded {
                        limit: limits.max_excluded,
                    });
                }
            }
        }

        // Only an unresolved conflict is contestable. A decided conflict is
        // settled by its recorded resolution: the winning side is already in
        // the fact base, and the losing side must not be reported as something
        // a human still has to decide.
        let mut decided: BTreeSet<String> = BTreeSet::new();
        for conflict in self.conflicts() {
            match &conflict.resolution {
                Resolution::Unresolved { .. } => {
                    for side in [&conflict.left, &conflict.right] {
                        if self.knows(side) {
                            continue;
                        }
                        let key = structural_key(self.env, side);
                        goals.entry(key).or_insert_with(|| (None, side.clone()));
                    }
                }
                Resolution::Defeated { .. } => {
                    decided.insert(structural_key(self.env, &conflict.left));
                    decided.insert(structural_key(self.env, &conflict.right));
                }
            }
        }

        let mut entries: Vec<(Option<Name>, String, Expr)> = goals
            .into_iter()
            .map(|(key, (rule, goal))| (rule, key, goal))
            .collect();
        // A proved conclusion is not contestable, and neither is a side of a
        // conflict that was already decided. This removes defeated conclusions
        // that the rule enumeration produced as ordinary gaps: their status is
        // `Defeated`, not an open issue.
        entries.retain(|(_, key, goal)| !self.knows(goal) && !decided.contains(key));
        entries.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
        if entries.len() > limits.max_issues {
            scan.limits.push(GapLimit::Issues {
                limit: limits.max_issues,
            });
            entries.truncate(limits.max_issues);
        }
        for (_, _, goal) in entries {
            let tree = self.gap_tree_with(&goal, limits)?;
            scan.issues.push(tree);
        }
        scan.limits.sort();
        scan.limits.dedup();
        scan.uninstantiable.sort();
        scan.uninstantiable.dedup();
        scan.excluded.sort_by(|a, b| a.rule.cmp(&b.rule));
        scan.excluded.dedup();
        Ok(scan)
    }

    /// Expand one gap node.
    ///
    /// The caller guarantees this node may be created. `depth` is the number of
    /// candidate links above this node, so the depth cap is a hard bound on the
    /// call stack as well as on the output.
    fn expand_gap(
        &self,
        goal: &Expr,
        depth: usize,
        path: &mut Vec<GapPathEntry>,
        budget: &mut GapBudget,
    ) -> Result<GapTree, String> {
        budget.nodes += 1;
        let status = self.gap_status(goal);
        let mut tree = GapTree {
            goal: goal.clone(),
            status,
            candidates: Vec::new(),
            axiom_candidates: Vec::new(),
            limit: None,
        };
        if status != GapStatus::Unreachable {
            return Ok(tree);
        }
        // A universal fact can prove this goal outright; if it does, the goal
        // is not a gap. The candidates listed here are the ones the current
        // derivation did not demand, or the ones refused (a binding value of
        // the wrong type, an incomplete match). They are diagnostics, bounded
        // by the same per-goal candidate cap as instantiation.
        tree.axiom_candidates = self.axiom_candidates(goal)?;
        let candidates = self.gap_candidates(goal)?;
        if candidates.is_empty() {
            return Ok(tree);
        }
        if depth >= budget.limits.max_depth {
            for candidate in candidates {
                tree.candidates.push(GapRule::unexpanded(candidate, None));
            }
            tree.limit = Some(GapLimit::Depth {
                limit: budget.limits.max_depth,
            });
            return Ok(tree);
        }

        path.push(GapPathEntry {
            key: structural_key(self.env, goal),
            goal: goal.clone(),
        });
        for candidate in candidates {
            // The node cap was reached by an earlier branch: the remaining
            // candidates and their premises are still listed (what and which
            // rule), but nothing below them is expanded.
            if tree.limit.is_some() {
                tree.candidates.push(GapRule::unexpanded(candidate, None));
                continue;
            }
            let attempts = budget.attempts.entry(candidate.rule.clone()).or_default();
            if !candidate.applicability.allows_firing() || !guards_hold(&candidate.guards) {
                // The rule cannot fire in this case — either the case does not
                // apply to this instance or one of its guards does not hold —
                // so its missing premises are not a place to dig deeper: the
                // candidate, what it lacks and the recorded reason are listed
                // together. It consumes no attempt and sets no limit, because
                // nothing was cut off.
                tree.candidates.push(GapRule::unexpanded(candidate, None));
                continue;
            }
            if *attempts >= budget.limits.max_rule_attempts {
                let rule = candidate.rule.clone();
                tree.candidates.push(GapRule::unexpanded(
                    candidate,
                    Some(GapLimit::RuleAttempts {
                        rule,
                        limit: budget.limits.max_rule_attempts,
                    }),
                ));
                continue;
            }
            *attempts += 1;
            let fallback = Expr::Sort(0);
            let mut rule = GapRule {
                rule: candidate.rule,
                applicability: candidate.applicability,
                held: candidate.held,
                missing: Vec::new(),
                blocked_by: candidate.blocked_by,
                guards: candidate.guards,
                sources: candidate.sources,
                limit: None,
            };
            for status in candidate.premises {
                if status.held.is_some() {
                    continue;
                }
                if !status.branches.is_empty() {
                    // A failing disjunction lists every written branch with its
                    // own gap: "P or Q is missing" is not a lump-sum answer.
                    let mut group = GapPremise {
                        premise: status
                            .missing
                            .first()
                            .cloned()
                            .unwrap_or_else(|| fallback.clone()),
                        gap: None,
                        branches: Vec::new(),
                        exists: None,
                    };
                    for (index, proposition) in status.branches {
                        let Some(child) = self.expand_premise(&proposition, depth, path, budget)?
                        else {
                            tree.limit = Some(GapLimit::Nodes {
                                limit: budget.limits.max_nodes,
                            });
                            group.branches.push(GapBranch {
                                index,
                                proposition,
                                gap: None,
                            });
                            continue;
                        };
                        group.branches.push(GapBranch {
                            index,
                            proposition,
                            gap: Some(Box::new(child)),
                        });
                    }
                    rule.missing.push(group);
                    continue;
                }
                let premise = status
                    .missing
                    .first()
                    .cloned()
                    .unwrap_or_else(|| fallback.clone());
                let exists = status.exists.then(|| GapExists {
                    body: premise.clone(),
                    candidates: status.exists_candidates,
                    truncated: status.exists_truncated,
                });
                let Some(child) = self.expand_premise(&premise, depth, path, budget)? else {
                    tree.limit = Some(GapLimit::Nodes {
                        limit: budget.limits.max_nodes,
                    });
                    rule.missing.push(GapPremise {
                        premise,
                        gap: None,
                        branches: Vec::new(),
                        exists,
                    });
                    continue;
                };
                rule.missing.push(GapPremise {
                    premise,
                    gap: Some(Box::new(child)),
                    branches: Vec::new(),
                    exists,
                });
            }
            tree.candidates.push(rule);
        }
        path.pop();
        Ok(tree)
    }

    /// Build the gap node for one missing premise, or `None` when the node
    /// budget is spent or the premise is already on the expansion path.
    fn expand_premise(
        &self,
        premise: &Expr,
        depth: usize,
        path: &mut Vec<GapPathEntry>,
        budget: &mut GapBudget,
    ) -> Result<Option<GapTree>, String> {
        if budget.nodes >= budget.limits.max_nodes {
            return Ok(None);
        }
        if self.gap_on_path(premise, path) {
            // A cycle marker is a node of the output too, so it counts.
            budget.nodes += 1;
            return Ok(Some(GapTree {
                goal: premise.clone(),
                status: GapStatus::Cycle,
                candidates: Vec::new(),
                axiom_candidates: Vec::new(),
                limit: None,
            }));
        }
        Ok(Some(self.expand_gap(premise, depth + 1, path, budget)?))
    }

    /// The status of a proposition as a gap node.
    fn gap_status(&self, goal: &Expr) -> GapStatus {
        if has_open_pattern(goal) {
            // The goal does not determine every parameter of the candidate
            // that produced it; there is no closed proposition to explain.
            GapStatus::OpenPattern
        } else if check::check(self.env, &Ctx::new(), goal, &Expr::Sort(0)).is_err() {
            GapStatus::NotAProposition
        } else if self.knows(goal) {
            // A defeated winner is in the fact base; `Proved` is the honest
            // status even though the proposition took part in a conflict. A
            // conclusion only an enabled interpretation licensed is marked
            // separately: as a rule premise it is still missing, because rules
            // never consume interpretation conclusions.
            let key = self.key_of(goal);
            let rule_visible = self
                .fixed
                .as_ref()
                .is_some_and(|fixed| fixed.rule_facts.contains_key(&key));
            if rule_visible {
                GapStatus::Proved
            } else {
                GapStatus::InterpretedOnly
            }
        } else if let Some(conflict) = self.conflict_for(goal) {
            match &conflict.resolution {
                Resolution::Unresolved { .. } => GapStatus::Conflicted,
                Resolution::Defeated { .. } => GapStatus::Defeated,
            }
        } else {
            GapStatus::Unreachable
        }
    }

    /// Every rule whose head matches `goal`, in rule-name order, with the
    /// premises still missing and the blocking conditions that already hold.
    ///
    /// The single-level candidate search is shared by `explain` and the
    /// recursive gap tree; the tree wraps each entry in a child node instead of
    /// reimplementing the match. Premises and `unless` blockers are judged
    /// against the rule-visible fact set, never against the interpretation
    /// conclusions: rules do not consume those, so counting one as satisfied
    /// would hide the very premise that keeps the rule from firing.
    ///
    /// Both sides of a premise match use the same judgment as the derivation
    /// ([`match_premise`]): a structural match first, then a normalization of
    /// both sides. A premise is missing only when no rule-visible fact
    /// satisfies that judgment, so a candidate with no missing premises means
    /// the rule really can fire, and one with a missing premise really cannot.
    fn gap_candidates(&self, goal: &Expr) -> Result<Vec<GapCandidate>, String> {
        let facts: BTreeMap<String, Expr> = self
            .fixed
            .as_ref()
            .map(|f| f.rule_facts.clone())
            .unwrap_or_default();
        let mut candidates = Vec::new();
        for decl in self.ordered_rules() {
            let DeclKind::Rule(rule) = &decl.kind else {
                continue;
            };
            // Match the rule head against the goal to get a candidate
            // instantiation, then instantiate premises and blockers with it.
            let mut binding = Vec::new();
            if !match_premise(self.env, &rule.open_conclusion(), goal, &mut binding) {
                continue;
            }
            // One judgment decides both sides of this candidate: a premise the
            // fixed point can consume contributes the fact's occurrence record
            // to the applicability anchor, and everything else is what the tree
            // reports as missing. The candidate's instance references only the
            // premise facts that already hold; a still-missing premise is not
            // a fact yet, so it does not contribute an event record.
            let premises = self.premise_statuses(&decl.name, rule, &binding, &facts)?;
            let held_keys: Vec<String> = premises
                .iter()
                .filter_map(|status| status.held.as_ref().map(|held| self.key_of(held)))
                .collect();
            let held: Vec<Expr> = premises.iter().filter_map(|s| s.held.clone()).collect();
            let missing: Vec<Expr> = premises.iter().flat_map(|s| s.missing.clone()).collect();
            let missing_branches: Vec<Option<usize>> = premises
                .iter()
                .flat_map(|status| {
                    if status.branches.is_empty() {
                        status.missing.iter().map(|_| None).collect::<Vec<_>>()
                    } else {
                        status
                            .branches
                            .iter()
                            .map(|(branch, _)| Some(*branch))
                            .collect::<Vec<_>>()
                    }
                })
                .collect();
            let choices: Vec<PremiseSelection> =
                premises.iter().map(|s| s.selection.clone()).collect();
            let blocked_by: Vec<Expr> = {
                let mut out = Vec::new();
                for u in &rule.unlesses {
                    let closed = close_pattern(&rule.open_unless_text(u), &binding);
                    if blocked(std::slice::from_ref(&closed), &facts, self.env)? {
                        out.push(closed);
                    }
                }
                out
            };
            // Guards are judged from the candidate's own bindings. A guard
            // whose parameter the conclusion match left open stays undecided
            // (`None`), which is reported as such — never silently `false`.
            let guards = judge_candidate_guards(self.env, &decl.name, rule, &binding)?;
            candidates.push(GapCandidate {
                rule: decl.name.clone(),
                bindings: binding,
                held,
                missing,
                missing_branches,
                choices,
                premises,
                blocked_by,
                guards,
                sources: decl.sources.clone(),
                applicability: self.judge_instance(&decl.scope, &held_keys),
            });
        }
        Ok(candidates)
    }

    /// Is `goal` already being expanded on this path?
    ///
    /// The structural key decides the normal case. A key miss compares with
    /// kernel conversion as well, so an eta variant of an ancestor is caught.
    /// A comparison that fails is not treated as equality: it only means this
    /// path is not cut here, and the depth cap still bounds the expansion.
    fn gap_on_path(&self, goal: &Expr, path: &[GapPathEntry]) -> bool {
        let key = structural_key(self.env, goal);
        path.iter().any(|entry| {
            entry.key == key
                || convertible(self.env, &Ctx::new(), &entry.goal, goal).unwrap_or(false)
        })
    }
}

// ---------------------------------------------------------------- priorities

/// Collect every declared priority edge of the environment.
///
/// A top-level `priority` declaration carries the namespace that asserted it
/// and its sources. A rule-internal clause (`defeated_by` / `prefer`) may only
/// order rules of the declaring rule's own package: the loader refuses a
/// cross-package clause, and one that reaches this function from a directly
/// built environment is ignored here (the certificate checker rejects it).
/// An edge whose endpoints are not two declared rules cannot decide a
/// derivation and is dropped.
fn declared_priorities(env: &Env) -> BTreeMap<(Name, Name), Vec<PriorityEdge>> {
    let mut declared: BTreeMap<(Name, Name), Vec<PriorityEdge>> = BTreeMap::new();
    for priority in env.priorities() {
        if !is_rule(env, &priority.winner) || !is_rule(env, &priority.loser) {
            continue;
        }
        insert_edge(
            &mut declared,
            PriorityEdge {
                winner: priority.winner,
                loser: priority.loser,
                origin: PriorityOrigin::Declaration {
                    declared_in: priority.declared_in,
                    sources: priority.sources,
                },
            },
        );
    }
    for decl in env.rules() {
        let DeclKind::Rule(rule) = &decl.kind else {
            continue;
        };
        for beater in &rule.exceptions {
            if !same_package(env, rule, beater) {
                continue;
            }
            insert_edge(
                &mut declared,
                PriorityEdge {
                    winner: beater.clone(),
                    loser: decl.name.clone(),
                    origin: PriorityOrigin::RuleClause {
                        rule: decl.name.clone(),
                        clause: PriorityClause::DefeatedBy,
                        sources: decl.sources.clone(),
                    },
                },
            );
        }
        for loser in &rule.prefers {
            if !same_package(env, rule, loser) {
                continue;
            }
            insert_edge(
                &mut declared,
                PriorityEdge {
                    winner: decl.name.clone(),
                    loser: loser.clone(),
                    origin: PriorityOrigin::RuleClause {
                        rule: decl.name.clone(),
                        clause: PriorityClause::Prefer,
                        sources: decl.sources.clone(),
                    },
                },
            );
        }
    }
    for edges in declared.values_mut() {
        edges.sort_by_key(PriorityEdge::sort_key);
    }
    declared
}

fn insert_edge(declared: &mut BTreeMap<(Name, Name), Vec<PriorityEdge>>, edge: PriorityEdge) {
    declared
        .entry((edge.winner.clone(), edge.loser.clone()))
        .or_default()
        .push(edge);
}

fn is_rule(env: &Env, name: &Name) -> bool {
    matches!(
        env.get(name).map(|decl| &decl.kind),
        Some(DeclKind::Rule(_))
    )
}

/// Does the rule-internal clause of `rule` target a rule of the same package?
///
/// `None` (a case file) is a package of its own: two case rules are in the
/// same package, a case rule and a module rule are not.
fn same_package(env: &Env, rule: &RuleDecl, target: &Name) -> bool {
    let Some(decl) = env.get(target) else {
        return false;
    };
    let DeclKind::Rule(target_rule) = &decl.kind else {
        return false;
    };
    target_rule.declared_in == rule.declared_in
}

/// The parts of the priority graph the reasoner keeps.
struct PriorityGraph {
    /// Rule name -> strongly connected component.
    scc: BTreeMap<Name, u32>,
    /// Edges between different components: the ones that can decide.
    effective: BTreeMap<Name, BTreeSet<Name>>,
    /// Components that declare a cycle: more than one rule, or a rule whose
    /// priority edge points at itself (only constructible through a directly
    /// built environment; the language refuses both spellings).
    cycles: Vec<Vec<Name>>,
}

/// Build the priority graph: nodes are the environment's rules, edges are the
/// declared priority edges between them.
fn priority_graph(
    env: &Env,
    declared: &BTreeMap<(Name, Name), Vec<PriorityEdge>>,
) -> PriorityGraph {
    let nodes: BTreeSet<Name> = env
        .rules()
        .into_iter()
        .map(|decl| decl.name.clone())
        .collect();
    let mut adjacency: BTreeMap<Name, Vec<Name>> = nodes
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
    let scc = kosaraju(&adjacency);
    let mut effective: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();
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
    let mut components: BTreeMap<u32, Vec<Name>> = BTreeMap::new();
    for (name, component) in &scc {
        components.entry(*component).or_default().push(name.clone());
    }
    let mut cycles: Vec<Vec<Name>> = components
        .into_values()
        .filter(|members| {
            members.len() > 1
                || members.iter().any(|name| {
                    adjacency
                        .get(name)
                        .is_some_and(|neighbors| neighbors.contains(name))
                })
        })
        .collect();
    for members in &mut cycles {
        members.sort();
    }
    cycles.sort();
    PriorityGraph {
        scc,
        effective,
        cycles,
    }
}

/// Iterative Kosaraju over the declared priority graph.
///
/// The graph is tiny (one node per rule), but the traversal is iterative and
/// every node and neighbour list is ordered by name, so the component ids are
/// reproducible and no rule set can overflow the stack.
fn kosaraju(adjacency: &BTreeMap<Name, Vec<Name>>) -> BTreeMap<Name, u32> {
    let mut visited: BTreeSet<Name> = BTreeSet::new();
    let mut finished: Vec<Name> = Vec::new();
    for start in adjacency.keys() {
        if visited.contains(start) {
            continue;
        }
        visited.insert(start.clone());
        let mut stack: Vec<(Name, usize)> = vec![(start.clone(), 0)];
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

    let mut reverse: BTreeMap<Name, Vec<Name>> = adjacency
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

    let mut component: BTreeMap<Name, u32> = BTreeMap::new();
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

// ---------------------------------------------------------------- matching

/// The fixed inputs of one rule enumeration. Bundling them keeps the recursive
/// `backtrack` signature short without hiding which environment and fact set
/// one enumeration belongs to.
struct Matching<'a> {
    env: &'a Env,
    /// The declaration's name, used only to name the rule in an error raised
    /// while judging an instance's guards.
    rule_name: &'a str,
    rule: &'a RuleDecl,
    facts: &'a BTreeMap<String, Expr>,
}

/// A premise-search budget: how many branch/witness alternatives one rule may
/// try in one enumeration. The count is reset at each enumeration (one fixed
/// point round or one witness index), and exceeding it is an explicit error.
struct SelectionBudget {
    attempts: usize,
}

impl SelectionBudget {
    fn new() -> Self {
        SelectionBudget { attempts: 0 }
    }

    fn charge(&mut self, rule_name: &str) -> Result<(), String> {
        self.attempts += 1;
        if self.attempts > MAX_SELECTION_ATTEMPTS_PER_RULE {
            return Err(format!(
                "规则 `{rule_name}` 的析取分支/存在见证选择尝试超过每轮 {} 次上限：\
                 析取与存在会按书写顺序尝试分支与见证，超过上限时显式报错，\
                 不静默截断搜索结果",
                MAX_SELECTION_ATTEMPTS_PER_RULE
            ));
        }
        Ok(())
    }
}

/// Is this term a concrete witness the certificate can record?
///
/// A witness must be an environment `obj` constant or an exact integer
/// literal. A compound term or a bare name that is not an individual would
/// silently invent an individual, so the reasoner refuses it instead of
/// producing a certificate its own checker would reject.
fn is_concrete_witness(env: &Env, witness: &Expr) -> bool {
    match witness {
        Expr::Num(_) => true,
        Expr::Const(name) => matches!(env.get(name).map(|decl| &decl.kind), Some(DeclKind::Obj)),
        _ => false,
    }
}

/// Every declared individual whose type is the (closed) domain type, sorted by
/// name.
///
/// Existential witnesses are not guessed: when the body does not mention the
/// witness, the search enumerates declared `obj` constants of the domain, so the
/// certificate can record a concrete, auditable individual. A domain with no
/// declared individual (for example `Int`, which has no finite enumeration)
/// yields no candidate and therefore no witness.
fn declared_individuals(env: &Env, domain: &Expr) -> Result<Vec<Expr>, String> {
    let mut names = Vec::new();
    for declaration in env.iter() {
        if !matches!(declaration.kind, DeclKind::Obj) {
            continue;
        }
        let same = convertible(env, &Ctx::new(), &declaration.ty, domain).map_err(|error| {
            format!(
                "无法判定个体 `{}` 的类型是否属于存在量词的域：{error}",
                declaration.name
            )
        })?;
        if same {
            names.push(declaration.name.clone());
        }
    }
    names.sort();
    Ok(names.into_iter().map(Expr::constant).collect())
}

/// The key of a fact that is kernel-equivalent to `proposition`, if one exists.
fn find_fact_key(
    env: &Env,
    facts: &BTreeMap<String, Expr>,
    proposition: &Expr,
) -> Result<Option<String>, String> {
    let key = key(env, proposition);
    if facts.contains_key(&key) {
        return Ok(Some(key));
    }
    for (fact_key, fact) in facts {
        if convertible(env, &Ctx::new(), fact, proposition).map_err(|error| {
            format!(
                "无法判定事实是否等价于「{}」：{error}",
                print_expr(proposition)
            )
        })? {
            return Ok(Some(fact_key.clone()));
        }
    }
    Ok(None)
}

/// Expand every match of one premise and recurse into the next premise.
///
/// This is the single premise walk both the plain and the demanding enumeration
/// use. `demand` carries the reasoner and the removed fact keys for
/// premise-driven universal instantiation; `None` is the plain enumeration.
/// The disjunctive and existential forms follow the same rule:
///
/// * branches are tried in **written order**, and the first branch that yields
///   at least one complete instance is used (the step proves one branch, not
///   all of them);
/// * an existential premise enumerates one witness per matching body. If the
///   body does not mention the witness, it enumerates declared individuals of
///   the domain in name order. Every witness is recorded, so two distinct
///   witnesses are two instances of the same rule.
#[allow(clippy::too_many_arguments)]
fn premise_walk(
    matching: &Matching,
    demand: Option<(&Reasoner<'_>, &BTreeSet<String>)>,
    idx: usize,
    binding: &mut Vec<(Name, Expr)>,
    keys: &mut Vec<String>,
    selections: &mut Vec<PremiseSelection>,
    budget: &mut SelectionBudget,
    out: &mut Vec<Instance>,
) -> Result<(), String> {
    let rule = matching.rule;
    if idx == rule.premises.len() {
        out.push(finish_instance(
            matching.env,
            matching.rule_name,
            rule,
            binding,
            keys.clone(),
            selections.clone(),
        )?);
        return Ok(());
    }

    match rule.open_premise(idx) {
        OpenPremise::Plain(pattern) => {
            let pattern = close_pattern(&pattern, binding);
            // A fact is not a linear resource: one established proposition may
            // satisfy several premises of the same rule, whether the rule writes
            // the same premise twice or writes two kernel-equivalent forms of it.
            let mut matched = false;
            for (k, fact) in matching.facts {
                let before = binding.len();
                let mut b = binding.clone();
                if !match_premise(matching.env, &pattern, fact, &mut b) {
                    continue;
                }
                matched = true;
                *binding = b;
                keys.push(k.clone());
                selections[idx] = PremiseSelection::Plain;
                premise_walk(
                    matching,
                    demand,
                    idx + 1,
                    binding,
                    keys,
                    selections,
                    budget,
                    out,
                )?;
                keys.pop();
                binding.truncate(before);
            }
            if !matched && !has_open_pattern(&pattern) {
                if let Some((reasoner, removed)) = demand {
                    if let Some(instance) = reasoner.demand_axiom(&pattern)? {
                        let key = reasoner.key_of(&instance.conclusion);
                        if !removed.contains(&key) && !matching.facts.contains_key(&key) {
                            keys.push(key);
                            selections[idx] = PremiseSelection::Plain;
                            premise_walk(
                                matching,
                                demand,
                                idx + 1,
                                binding,
                                keys,
                                selections,
                                budget,
                                out,
                            )?;
                            keys.pop();
                        }
                    }
                }
            }
        }
        OpenPremise::Or(branches) => {
            // Every written branch is tried, in order. A branch that yields a
            // complete instance proves the disjunction; another branch may
            // yield a different binding or a second independent proof, so a
            // branch is never dropped merely because an earlier one fired. The
            // selection budget bounds the total work; the certificate records
            // exactly which branch each instance used.
            for (branch, declared) in branches.iter().enumerate() {
                budget.charge(matching.rule_name)?;
                let pattern = close_pattern(declared, binding);
                for (k, fact) in matching.facts {
                    let before = binding.len();
                    let mut b = binding.clone();
                    if !match_premise(matching.env, &pattern, fact, &mut b) {
                        continue;
                    }
                    *binding = b;
                    keys.push(k.clone());
                    selections[idx] = PremiseSelection::Branch {
                        premise: idx,
                        branch,
                    };
                    premise_walk(
                        matching,
                        demand,
                        idx + 1,
                        binding,
                        keys,
                        selections,
                        budget,
                        out,
                    )?;
                    keys.pop();
                    binding.truncate(before);
                }
            }
            if let Some((reasoner, removed)) = demand {
                for (branch, declared) in branches.iter().enumerate() {
                    let pattern = close_pattern(declared, binding);
                    if has_open_pattern(&pattern) {
                        continue;
                    }
                    if let Some(instance) = reasoner.demand_axiom(&pattern)? {
                        let key = reasoner.key_of(&instance.conclusion);
                        if !removed.contains(&key) && !matching.facts.contains_key(&key) {
                            budget.charge(matching.rule_name)?;
                            keys.push(key);
                            selections[idx] = PremiseSelection::Branch {
                                premise: idx,
                                branch,
                            };
                            premise_walk(
                                matching,
                                demand,
                                idx + 1,
                                binding,
                                keys,
                                selections,
                                budget,
                                out,
                            )?;
                            keys.pop();
                        }
                    }
                }
            }
        }
        OpenPremise::Exists {
            binder,
            domain,
            body,
        } => {
            let pattern = close_pattern(&body, binding);
            let body_mentions_witness = open_names(&body).contains(&binder);
            if body_mentions_witness {
                let mut candidates = 0usize;
                for (k, fact) in matching.facts {
                    let before = binding.len();
                    let mut b = binding.clone();
                    if !match_premise(matching.env, &pattern, fact, &mut b) {
                        continue;
                    }
                    candidates += 1;
                    if candidates > MAX_WITNESS_CANDIDATES_PER_PREMISE {
                        return Err(format!(
                            "规则 `{}` 的第 {} 个存在前提的见证候选超过每个前提 {} 个上限：\
                             见证必须逐个枚举，超限时显式报错而不静默截断",
                            matching.rule_name,
                            idx + 1,
                            MAX_WITNESS_CANDIDATES_PER_PREMISE
                        ));
                    }
                    budget.charge(matching.rule_name)?;
                    let witness = b
                        .iter()
                        .rev()
                        .find(|(name, _)| *name == binder)
                        .map(|(_, value)| value.clone())
                        .ok_or_else(|| {
                            format!(
                                "规则 `{}` 的第 {} 个存在前提：匹配到了体，却没有得到见证 `?{}`",
                                matching.rule_name,
                                idx + 1,
                                binder
                            )
                        })?;
                    if !is_concrete_witness(matching.env, &witness) {
                        return Err(format!(
                            "规则 `{}` 的第 {} 个存在前提的见证 `{}` 不是已声明个体：\
                             事实里的这个项无法作为证书中的具体见证",
                            matching.rule_name,
                            idx + 1,
                            print_expr(&witness)
                        ));
                    }
                    *binding = b;
                    keys.push(k.clone());
                    selections[idx] = PremiseSelection::Witness {
                        premise: idx,
                        witness: witness.clone(),
                    };
                    premise_walk(
                        matching,
                        demand,
                        idx + 1,
                        binding,
                        keys,
                        selections,
                        budget,
                        out,
                    )?;
                    keys.pop();
                    binding.truncate(before);
                }
            } else {
                // The body does not mention the witness: any declared individual
                // of the domain satisfies it if the body holds. The witness is
                // enumerated from declarations, so it is always concrete.
                let closed_domain = close_pattern(&domain, binding);
                let closed_body = close_pattern(&body, binding);
                let individuals = declared_individuals(matching.env, &closed_domain)?;
                if individuals.len() > MAX_WITNESS_CANDIDATES_PER_PREMISE {
                    return Err(format!(
                        "规则 `{}` 的第 {} 个存在前提的候选个体超过每个前提 {} 个上限：\
                         见证必须逐个枚举，超限时显式报错而不静默截断",
                        matching.rule_name,
                        idx + 1,
                        MAX_WITNESS_CANDIDATES_PER_PREMISE
                    ));
                }
                for witness in individuals {
                    budget.charge(matching.rule_name)?;
                    let instance = substitute_pattern_constants(
                        &closed_body,
                        &[(binder.clone(), witness.clone())],
                    );
                    let Some(fact_key) = find_fact_key(matching.env, matching.facts, &instance)?
                    else {
                        continue;
                    };
                    keys.push(fact_key);
                    selections[idx] = PremiseSelection::Witness {
                        premise: idx,
                        witness: witness.clone(),
                    };
                    premise_walk(
                        matching,
                        demand,
                        idx + 1,
                        binding,
                        keys,
                        selections,
                        budget,
                        out,
                    )?;
                    keys.pop();
                }
            }
        }
    }
    Ok(())
}

/// The instance a complete binding produces: the rule's conclusion closed by
/// the binding, then the built-in arithmetic in it evaluated by the kernel, and
/// every guard judged against the same binding.
///
/// The two conclusion forms are kept apart on purpose. `computed` is what the
/// rule wrote (a record of the computation), `conclusion` is its value; a
/// certificate records both, and the checker re-derives the first from the rule
/// and the bindings and the second from the first. An overflow aborts the
/// reasoning with an error; it never becomes a wraparound or an unrecorded
/// number.
///
/// A guard is an instance condition, not a premise: it is *evaluated*, never
/// proved. Every guard must decide to `true` or `false`; an overflowing or
/// non-literal guard is an explicit error (naming the rule and the guard)
/// rather than a silent "does not fire", and an instance whose guard is `false`
/// is produced but does not fire, so gap reports can say why.
fn finish_instance(
    env: &Env,
    rule_name: &str,
    rule: &RuleDecl,
    binding: &[(Name, Expr)],
    premise_keys: Vec<String>,
    selections: Vec<PremiseSelection>,
) -> Result<Instance, String> {
    let raw = close_pattern(&rule.open_conclusion(), binding);
    let conclusion = evaluate_arithmetic(env, &raw).map_err(|error| {
        format!(
            "规则 `{rule_name}` 实例的结论无法计算：{error}（结论写的是「{}」）",
            print_expr(&raw)
        )
    })?;
    let computed = if conclusion == raw {
        None
    } else {
        Some(Box::new(raw))
    };
    let unlesses = (0..rule.unlesses.len())
        .map(|i| close_pattern(&rule.open_unless_text(&rule.unlesses[i]), binding))
        .collect();
    let guard_judgements = (0..rule.guards.len())
        .map(|i| {
            let instance = close_pattern(&rule.open_guard(i), binding);
            let holds = evaluate_comparison(env, &instance).map_err(|error| {
                format!(
                    "规则 `{rule_name}` 的第 {} 条守卫无法判定：{error}；\
                     守卫求值失败不当作 false",
                    i + 1
                )
            })?;
            Ok(GuardJudgement {
                index: i,
                instance,
                holds: Some(holds),
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    // Only parameters are certificate bindings. The witness of an existential
    // premise is not a telescope binder and is recorded in `selections`; a
    // premise binder itself is not a value.
    let bindings = rule
        .params
        .iter()
        .map(|(parameter, _)| {
            binding
                .iter()
                .rev()
                .find(|(name, _)| name == parameter)
                .map(|(_, value)| (parameter.clone(), value.clone()))
                .ok_or_else(|| {
                    format!("规则 `{rule_name}` 的参数 `{parameter}` 没有被这次实例的匹配确定")
                })
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(Instance {
        conclusion,
        computed,
        premise_keys,
        selections,
        unlesses,
        guard_judgements,
        bindings,
    })
}

/// Judge a gap candidate's guards from its own bindings.
///
/// A candidate's bindings come from matching the rule's head against the goal,
/// so a parameter that only appears in premises may be left open. A guard that
/// still mentions such a parameter (or whose operands are not integer
/// literals) cannot be decided; that is recorded as `holds: None` and shown as
/// "无法判定", never as `false`. An arithmetic overflow is an error even here:
/// a guard whose result does not fit in `i64` is not evidence about the case.
fn judge_candidate_guards(
    env: &Env,
    rule_name: &str,
    rule: &RuleDecl,
    binding: &[(Name, Expr)],
) -> Result<Vec<GuardJudgement>, String> {
    let mut out = Vec::with_capacity(rule.guards.len());
    for i in 0..rule.guards.len() {
        let instance = close_pattern(&rule.open_guard(i), binding);
        let evaluated = evaluate_arithmetic(env, &instance).map_err(|error| {
            format!(
                "规则 `{rule_name}` 的第 {} 条守卫无法计算：{error}（守卫形态「{}」）",
                i + 1,
                print_expr(&instance)
            )
        })?;
        let holds = std_deduce_kernel::builtin::truth_value(&evaluated);
        out.push(GuardJudgement {
            index: i,
            instance,
            holds,
        });
    }
    Ok(out)
}

/// Premise-driven universal elimination is folded into [`premise_walk`]: a
/// premise no fact satisfies but which is closed asks the reasoner for a
/// universal instance. The instance is a derived proposition, so it may satisfy
/// this premise even before the next fixed-point round carries it into the fact
/// set. The conclusion key is recorded as the premise key so the node graph can
/// cite the `axiom_instance` node; [`Reasoner::fixed_point`] adds the instance
/// to the next set in the same round. A removed conclusion never satisfies a
/// premise.
fn blocked(unlesses: &[Expr], facts: &BTreeMap<String, Expr>, env: &Env) -> Result<bool, String> {
    for unless in unlesses {
        // A comparison that could not be decided is not evidence that the
        // blocker is absent, and it is not evidence that it is present either:
        // an integer-overflow while evaluating the condition is an error that
        // must reach the user, never a silent "blocked" that can masquerade as
        // a rule cycle. It is also never "not blocked".
        if blocker_proved(env, facts, unless)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Is the blocker `unless` established by a known fact, up to kernel
/// definitional equality?
///
/// The normalized printed key is an exact fast path. Alpha- and eta-equivalent
/// facts have different keys, so a miss compares every fact with the kernel's
/// [`convertible`]. Normalizing the condition itself may fail (an `i64`
/// overflow in an arithmetic `unless` is such a failure); that error is
/// returned, never swallowed into a text key or into "blocked".
fn blocker_proved(
    env: &Env,
    facts: &BTreeMap<String, Expr>,
    unless: &Expr,
) -> Result<bool, String> {
    let unless_key = normalized_key(env, unless).map_err(|error| {
        format!(
            "无法判定阻断条件「{}」是否已成立：{error}",
            print_expr(unless)
        )
    })?;
    if facts.contains_key(&unless_key) {
        return Ok(true);
    }
    for fact in facts.values() {
        if convertible(env, &Ctx::new(), fact, unless).map_err(|error| {
            format!(
                "无法判定阻断条件「{}」是否已成立：{error}",
                print_expr(unless)
            )
        })? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Is `pattern` (containing `?x` constants) matchable against ground `fact`?
fn match_fact(p: &Expr, f: &Expr, b: &mut Vec<(Name, Expr)>) -> bool {
    match (p, f) {
        (Expr::Const(n), _) => match n.strip_prefix('?') {
            Some(pv) => {
                let key = std_deduce_kernel::name(pv);
                match b.iter().find(|(k, _)| *k == key) {
                    Some((_, prev)) => *prev == *f,
                    None => {
                        b.push((key, f.clone()));
                        true
                    }
                }
            }
            None => matches!(f, Expr::Const(fn_) if fn_.as_ref() == n.as_ref()),
        },
        (Expr::App { func: pf, arg: pa }, Expr::App { func: ff, arg: fa }) => {
            match_fact(pf, ff, b) && match_fact(pa, fa, b)
        }
        (Expr::Sort(x), Expr::Sort(y)) => x == y,
        (Expr::Num(x), Expr::Num(y)) => x == y,
        (Expr::Date(x), Expr::Date(y)) => x == y,
        _ => false,
    }
}

/// Is `pattern` (containing `?x` constants) matchable against ground `fact`,
/// up to kernel definitional equality?
///
/// The structural match is the fast path, and the only path most premises take.
/// When it fails, both sides are normalized once (beta, `def` delta, zeta) and
/// matched again, so a rule may write `夫妻 a b` while the fact records the
/// underlying `配偶 张三 李四`, and the other way round. The fallback is
/// deliberately conservative: an open term (a free de Bruijn index), a term
/// above the certificate's expression bound, a failed normalization, or a
/// pattern whose normalization drops a rule binder all mean "no match". It
/// never invents structure, and it is not consulted before the structural
/// match fails.
fn match_premise(env: &Env, pattern: &Expr, fact: &Expr, binding: &mut Vec<(Name, Expr)>) -> bool {
    let mut trial = binding.clone();
    if match_fact(pattern, fact, &mut trial) {
        *binding = trial;
        return true;
    }
    match_normalized_premise(env, pattern, fact, binding)
}

/// The normalization fallback of [`match_premise`].
fn match_normalized_premise(
    env: &Env,
    pattern: &Expr,
    fact: &Expr,
    binding: &mut Vec<(Name, Expr)>,
) -> bool {
    if !std_deduce_kernel::term::is_closed(pattern) || !std_deduce_kernel::term::is_closed(fact) {
        return false;
    }
    if !within_term_limit(pattern) || !within_term_limit(fact) {
        return false;
    }
    let Ok(normalized_pattern) = normalize(env, &Ctx::new(), pattern) else {
        return false;
    };
    let Ok(normalized_fact) = normalize(env, &Ctx::new(), fact) else {
        return false;
    };
    if !within_term_limit(&normalized_pattern) || !within_term_limit(&normalized_fact) {
        return false;
    }
    // Every binder the pattern mentions must survive normalization. If a
    // normalization erased one, the instance would have an unbound parameter,
    // and that is not a match at all.
    let survivors = open_names(&normalized_pattern);
    if !open_names(pattern)
        .iter()
        .all(|name| survivors.contains(name))
    {
        return false;
    }
    let mut trial = binding.clone();
    if !match_fact(&normalized_pattern, &normalized_fact, &mut trial) {
        return false;
    }
    *binding = trial;
    true
}

/// Is `premise` already established by the fact set?
///
/// The derivation and the gap diagnostics must answer this with one judgment,
/// otherwise a candidate can list no missing premise while the rule still
/// cannot fire (or the reverse). The normalized printed key is the exact fast
/// path; a miss runs [`match_premise`] against every fact. A premise that still
/// mentions an undetermined rule binder is not matched: that is an open
/// pattern, reported as such by the tree, not a premise some fact satisfies.
fn premise_satisfied(env: &Env, facts: &BTreeMap<String, Expr>, premise: &Expr) -> bool {
    if has_open_pattern(premise) {
        return facts.contains_key(&key(env, premise));
    }
    if facts.contains_key(&key(env, premise)) {
        return true;
    }
    facts
        .values()
        .any(|fact| match_premise(env, premise, fact, &mut Vec::new()))
}

/// Every rule binder (`?name` constant) a pattern mentions.
fn open_names(expression: &Expr) -> BTreeSet<Name> {
    fn go(expression: &Expr, names: &mut BTreeSet<Name>) {
        match expression {
            Expr::Const(name) => {
                if let Some(stripped) = name.strip_prefix('?') {
                    names.insert(std_deduce_kernel::name(stripped));
                }
            }
            Expr::Sort(_) | Expr::Var(_) | Expr::Num(_) | Expr::Date(_) => {}
            Expr::Pi {
                domain, codomain, ..
            } => {
                go(domain, names);
                go(codomain, names);
            }
            Expr::Lam { domain, body, .. } => {
                go(domain, names);
                go(body, names);
            }
            Expr::App { func, arg } => {
                go(func, names);
                go(arg, names);
            }
            Expr::Let { value, body, .. } => {
                go(value, names);
                go(body, names);
            }
        }
    }
    let mut names = BTreeSet::new();
    go(expression, &mut names);
    names
}

/// Substitute the `?x` constants of a pattern.
fn close_pattern(p: &Expr, binding: &[(Name, Expr)]) -> Expr {
    match p {
        Expr::Const(n) => match n.strip_prefix('?') {
            Some(pv) => {
                let key = std_deduce_kernel::name(pv);
                binding
                    .iter()
                    .rev()
                    .find(|(k, _)| *k == key)
                    .map(|(_, v)| v.clone())
                    .unwrap_or_else(|| p.clone())
            }
            None => p.clone(),
        },
        Expr::Sort(_) | Expr::Var(_) | Expr::Num(_) | Expr::Date(_) => p.clone(),
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

/// Is a fact's declared type itself a proposition?
///
/// `侵占 张三 : Prop` — yes, so the ledger entry asserts that proposition.
/// `Prop : Type 1` — no, so the entry only names a constant.
fn declared_type_is_prop(env: &Env, ty: &Expr) -> bool {
    check::infer(env, &Ctx::new(), ty)
        .ok()
        .and_then(|t| normalize(env, &Ctx::new(), &t).ok())
        .map(|t| matches!(t, Expr::Sort(0)))
        .unwrap_or(false)
}

fn same_keys(a: &BTreeMap<String, Expr>, b: &BTreeMap<String, Expr>) -> bool {
    a.len() == b.len() && a.keys().all(|k| b.contains_key(k))
}

fn key(env: &Env, e: &Expr) -> String {
    match normalize(env, &Ctx::new(), e) {
        Ok(n) => print_expr(&n),
        Err(_) => print_expr(e),
    }
}

/// The normalized printed key, with a normalization failure returned as an
/// error.
///
/// [`key`] falls back to the printed text because it is a display/ordering
/// helper. Where the key decides a judgement (a blocker condition), a failed
/// evaluation must not turn into a text key: that would let an overflowing
/// arithmetic condition silently compare as an opaque string.
fn normalized_key(env: &Env, e: &Expr) -> Result<String, String> {
    normalize(env, &Ctx::new(), e)
        .map(|n| print_expr(&n))
        .map_err(|error| format!("{error}"))
}

// ---------------------------------------------------------------- gaps

#[derive(Debug, Clone)]
pub struct GapExplanation {
    pub goal: Expr,
    pub candidates: Vec<GapCandidate>,
    /// Universal facts whose body unifies with the goal, with the bindings an
    /// instance would need. Empty when the goal is proved or when no universal
    /// fact matches it.
    pub axiom_candidates: Vec<AxiomCandidate>,
    pub note: Option<String>,
}

/// What a gap node's proposition is, as far as the settled state is concerned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GapStatus {
    /// Nothing in the fact base proves it; `GapTree::candidates` says what
    /// each rule still needs.
    Unreachable,
    /// It is in the settled fact base.
    Proved,
    /// It is in the settled fact base only because an enabled interpretation
    /// licensed it. Rules never consume an interpretation conclusion, so as a
    /// rule premise it is still missing: the gap is real even though the
    /// proposition is proved in the query's one-step sense.
    InterpretedOnly,
    /// It is a side of an unresolved conflict, so it is not asserted and a
    /// human still has to decide between the sides.
    Conflicted,
    /// It took part in a conflict that was decided against it. The decision is
    /// recorded, so this is not an open issue: it is reported as decided and
    /// kept out of the issue scan.
    Defeated,
    /// The term is not a proposition and cannot be a goal.
    NotAProposition,
    /// The term still contains a rule-telescope binder (`?name`): the goal does
    /// not determine every parameter of the candidate, so this premise cannot
    /// be stated — let alone expanded — as it stands.
    OpenPattern,
    /// The same proposition is already being expanded on this path; the rule
    /// cycle is cut here instead of recursing forever.
    Cycle,
}

/// An explicit limit that stopped a gap expansion or an issue scan.
///
/// A limit is always reported where it applies: `GapTree::limit` for a node
/// whose premises are not expanded, `GapRule::limit` for a rule whose repeated
/// attempts are refused, `IssueScan::limits` for the scan itself.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum GapLimit {
    /// The expansion reached the maximum depth.
    Depth { limit: usize },
    /// The expansion reached the maximum number of nodes (the root counts).
    Nodes { limit: usize },
    /// One rule was already expanded the maximum number of times.
    RuleAttempts { rule: Name, limit: usize },
    /// The issue scan reached its maximum number of conclusions.
    Issues { limit: usize },
    /// The issue scan reached its maximum number of excluded rules.
    Excluded { limit: usize },
}

/// The bounds of a gap tree or an issue scan.
///
/// The defaults are deliberately small: a legal chain is short, and an
/// explanation that would need more than a few hundred nodes is a sign that
/// the theory, not the printer, should be fixed. Reaching a limit is reported,
/// never silently applied.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GapLimits {
    /// Maximum depth of the gap tree (the root is depth 0).
    pub max_depth: usize,
    /// Maximum number of gap nodes in one tree (the root counts; with
    /// `max_nodes == 0` the tree is a stub that only carries the limit).
    pub max_nodes: usize,
    /// Maximum number of times one rule may be expanded inside one tree, and
    /// the maximum number of parameter tuples the issue scan tries per rule.
    pub max_rule_attempts: usize,
    /// Maximum number of contestable conclusions the issue scan lists.
    pub max_issues: usize,
    /// Maximum number of excluded rules the issue scan lists.
    pub max_excluded: usize,
}

impl Default for GapLimits {
    fn default() -> Self {
        GapLimits {
            max_depth: 6,
            max_nodes: 128,
            max_rule_attempts: 8,
            max_issues: 32,
            max_excluded: 16,
        }
    }
}

/// Why a proposition is still open, expanded recursively.
#[derive(Debug, Clone)]
pub struct GapTree {
    /// The proposition this node explains.
    pub goal: Expr,
    pub status: GapStatus,
    /// Rules whose head matches `goal`, in rule-name order.
    pub candidates: Vec<GapRule>,
    /// Universal facts whose body unifies with `goal`, in axiom-name order.
    /// A successful instance closes the goal and never leaves a gap; these
    /// candidates are the ones the derivation did not demand or refused, with
    /// the values an instance would need.
    pub axiom_candidates: Vec<AxiomCandidate>,
    /// Set when this node's candidates are listed but their missing premises
    /// were not expanded, because a node limit was reached.
    pub limit: Option<GapLimit>,
}

/// One rule that could conclude a gap, with what it still needs.
#[derive(Debug, Clone)]
pub struct GapRule {
    pub rule: Name,
    /// The rule's temporal/spatial judgement for this case. An excluded
    /// rule is still a candidate: the reader sees the rule, what it lacks and
    /// the concrete reason it cannot apply. An unchecked rule is expanded
    /// because it may still fire; an inapplicable/undecidable one is listed
    /// but not expanded.
    pub applicability: Applicability,
    /// Premises that already hold for this instantiation, in the rule's
    /// premise order. The certificate's root gap candidate records them; the
    /// recursive tree keeps them so a derived report can attribute a fact to
    /// a nested gap instead of treating it as unrelated.
    pub held: Vec<Expr>,
    /// Missing premises in the rule's own premise order, each with the gap
    /// that explains why it is missing.
    pub missing: Vec<GapPremise>,
    /// `unless` conditions that already hold; each one stops this rule.
    pub blocked_by: Vec<Expr>,
    /// Guard judgements for this candidate instance. A false or undecided
    /// guard is the reason the candidate cannot fire even with every premise,
    /// and it is printed rather than silently omitted.
    pub guards: Vec<GuardJudgement>,
    pub sources: Vec<SourceRef>,
    /// Set when this rule was not expanded because it already used up its
    /// attempts.
    pub limit: Option<GapLimit>,
}

/// One missing premise and its recursive gap.
#[derive(Debug, Clone)]
pub struct GapPremise {
    pub premise: Expr,
    /// `None` when a node limit stopped the expansion; the enclosing
    /// `GapTree::limit` or `GapRule::limit` says which.
    pub gap: Option<Box<GapTree>>,
    /// For a failing disjunction: one entry per written branch, each with its
    /// own gap. Empty for a plain or existential premise.
    pub branches: Vec<GapBranch>,
    /// For a failing existence: the body and the declared individuals that were
    /// tried, with an explicit truncation flag. `None` otherwise.
    pub exists: Option<GapExists>,
}

/// One branch of a failing disjunction, with what that branch itself lacks.
#[derive(Debug, Clone)]
pub struct GapBranch {
    /// Zero-based branch index in the written order.
    pub index: usize,
    /// The instantiated branch proposition.
    pub proposition: Expr,
    /// `None` when a node limit stopped this branch's expansion.
    pub gap: Option<Box<GapTree>>,
}

/// The witnesses a failing existence search could enumerate.
#[derive(Debug, Clone)]
pub struct GapExists {
    /// The open body `P ?w` (or the closed body when it does not mention the
    /// witness).
    pub body: Expr,
    /// Declared individuals of the domain that the search tried, at most
    /// [`MAX_GAP_WITNESS_CANDIDATES`].
    pub candidates: Vec<Expr>,
    /// Whether more declared individuals exist than the display bound.
    pub truncated: bool,
}

/// A rule whose every enumerated instance is excluded by the applicability
/// judgement, with the distinct verdicts those instances produced.
///
/// The exclusion is per instance, not a rule-level shortcut: an instance with
/// a held premise event inside the range is not excluded just because some
/// other instance is. Only when no enumerable instance may fire is the rule
/// reported here.
#[derive(Debug, Clone, PartialEq)]
pub struct ExcludedRule {
    /// The rule whose instances were all excluded.
    pub rule: Name,
    /// The distinct verdicts of the excluded instances, deduplicated.
    pub verdicts: Vec<Applicability>,
}

/// Every contestable conclusion under the current fact set.
#[derive(Debug, Clone)]
pub struct IssueScan {
    /// One gap tree per contestable conclusion. Trees are sorted by the rule
    /// that first produced the goal and then by structural goal key; a
    /// conclusion no rule produces (a conflict side) sorts first.
    pub issues: Vec<GapTree>,
    /// Limits that stopped the scan itself (an issue cap, a per-rule
    /// enumeration cap or an excluded-rule cap), sorted and deduplicated.
    pub limits: Vec<GapLimit>,
    /// Rules that produced no contestable conclusion because their parameter
    /// types have no declared constant, or because their conclusion depends on
    /// a premise proof and cannot be stated from facts.
    pub uninstantiable: Vec<Name>,
    /// Rules every enumerable instance of which is excluded (`不适用` or
    /// `无法判定`), with the per-instance verdicts. An undecidable instance
    /// needs an explicit reference time that this version does not offer yet;
    /// the rule is reported instead of silently absent from the scan.
    pub excluded: Vec<ExcludedRule>,
}

impl GapRule {
    /// A candidate whose missing premises are listed but not expanded.
    fn unexpanded(candidate: GapCandidate, limit: Option<GapLimit>) -> Self {
        let missing = unexpanded_gap_premises(candidate.premises);
        GapRule {
            rule: candidate.rule,
            applicability: candidate.applicability,
            held: candidate.held,
            missing,
            blocked_by: candidate.blocked_by,
            guards: candidate.guards,
            sources: candidate.sources,
            limit,
        }
    }
}

/// Turn a candidate's per-premise statuses into unexpanded gap entries.
fn unexpanded_gap_premises(premises: Vec<PremiseStatus>) -> Vec<GapPremise> {
    premises
        .into_iter()
        .filter(|status| status.held.is_none())
        .map(|status| {
            let fallback = Expr::Sort(0);
            if !status.branches.is_empty() {
                return GapPremise {
                    premise: status
                        .missing
                        .first()
                        .cloned()
                        .unwrap_or_else(|| fallback.clone()),
                    gap: None,
                    branches: status
                        .branches
                        .into_iter()
                        .map(|(index, proposition)| GapBranch {
                            index,
                            proposition,
                            gap: None,
                        })
                        .collect(),
                    exists: None,
                };
            }
            let body = status.missing.first().cloned().unwrap_or(fallback);
            let exists = status.exists.then(|| GapExists {
                body: body.clone(),
                candidates: status.exists_candidates,
                truncated: status.exists_truncated,
            });
            GapPremise {
                premise: body,
                gap: None,
                branches: Vec::new(),
                exists,
            }
        })
        .collect()
}

/// The budget shared by every node of one gap tree.
struct GapBudget<'a> {
    limits: &'a GapLimits,
    nodes: usize,
    /// Rule name -> number of expansions attempted in this tree.
    attempts: BTreeMap<Name, usize>,
}

impl<'a> GapBudget<'a> {
    fn new(limits: &'a GapLimits) -> Self {
        GapBudget {
            limits,
            nodes: 0,
            attempts: BTreeMap::new(),
        }
    }
}

/// One proposition already being expanded on the current path.
struct GapPathEntry {
    key: String,
    goal: Expr,
}

/// A collision-free structural identity for the gap tree's maps.
///
/// It is the certificate's own [`std_deduce_cert::expression_key`] applied to
/// the normal form: binder names do not matter, `def`/beta/zeta are unfolded,
/// and a bound variable can never collide with a same-named constant. Printed
/// text is not used for identity anywhere in the gap tree.
fn structural_key(env: &Env, expression: &Expr) -> String {
    // `normalize` has no failure path for the closed terms built from
    // declarations. If it ever returned an error, the structural encoding of
    // the term itself is still a structural key: deduplication would get
    // coarser, but no gap result is decided by printed text.
    let normalized = normalize(env, &Ctx::new(), expression).unwrap_or_else(|_| expression.clone());
    std_deduce_cert::expression_key(&normalized)
}

/// Does the expression still mention a rule-telescope binder (`?name`)?
///
/// Such a conclusion depends on a particular premise proof; it is not a
/// proposition that can be stated from facts, so the issue scan does not list
/// it. The check is structural, not textual: `?name` is the reasoner's own
/// encoding, never a constant the language can declare.
fn has_open_pattern(expression: &Expr) -> bool {
    match expression {
        Expr::Const(name) => name.starts_with('?'),
        Expr::App { func, arg } => has_open_pattern(func) || has_open_pattern(arg),
        Expr::Pi {
            domain, codomain, ..
        } => has_open_pattern(domain) || has_open_pattern(codomain),
        Expr::Lam { domain, body, .. } => has_open_pattern(domain) || has_open_pattern(body),
        Expr::Let { value, body, .. } => has_open_pattern(value) || has_open_pattern(body),
        Expr::Sort(_) | Expr::Var(_) | Expr::Num(_) | Expr::Date(_) => false,
    }
}

/// Every constant of the environment, grouped by its declared type's
/// structural key, sorted by name.
///
/// Rules are constants too (their type is the rule telescope), so a
/// higher-order parameter can be instantiated with one. Meta declarations
/// (`contrary`, `unique`, `priority`, `open`, `risk`, `interpret`) name no term
/// and are skipped.
fn constant_values(env: &Env) -> BTreeMap<String, Vec<Expr>> {
    let mut by_type: BTreeMap<String, Vec<Expr>> = BTreeMap::new();
    for decl in env.iter() {
        if matches!(
            &decl.kind,
            DeclKind::Contrary { .. }
                | DeclKind::Unique { .. }
                | DeclKind::Priority { .. }
                | DeclKind::OpenConcept { .. }
                | DeclKind::Risk { .. }
                | DeclKind::Interpretation(_)
        ) {
            continue;
        }
        by_type
            .entry(structural_key(env, &decl.ty))
            .or_default()
            .push(Expr::Const(decl.name.clone()));
    }
    for candidates in by_type.values_mut() {
        candidates.sort_by(|a, b| const_name(a).cmp(const_name(b)));
        candidates.dedup_by(|a, b| structural_key(env, a) == structural_key(env, b));
    }
    by_type
}

fn const_name(expression: &Expr) -> &str {
    match expression {
        Expr::Const(name) => name,
        _ => "",
    }
}

/// Collect the typed parameter tuples of `rule`, at most `limit` of them.
///
/// A parameter's type is opened with `?<earlier parameter>` constants and
/// closed with the values chosen so far, so a dependent parameter (such as
/// `y : 亲属 x`) only accepts values of the instantiated type. The traversal is
/// iterative: a rule with many parameters cannot overflow the call stack.
///
/// `truncated` is set only when a tuple was actually left out because `out`
/// already holds `limit` values; a rule with exactly `limit` tuples does not
/// report a truncation.
fn collect_param_bindings(
    env: &Env,
    rule: &RuleDecl,
    values: &BTreeMap<String, Vec<Expr>>,
    limit: usize,
    out: &mut Vec<Vec<(Name, Expr)>>,
    truncated: &mut bool,
) {
    // One frame per parameter level: the values of that level's type and how
    // many of them have been tried.
    let mut stack: Vec<(Vec<Expr>, usize)> = Vec::new();
    let mut binding: Vec<(Name, Expr)> = Vec::new();
    loop {
        if stack.len() == rule.params.len() {
            if out.len() == limit {
                *truncated = true;
                return;
            }
            out.push(binding.clone());
            if !advance_param_frame(&mut stack, &mut binding, rule) {
                return;
            }
            continue;
        }
        let level = stack.len();
        let parameter_type = close_pattern(&rule.open_param_type(level), &binding);
        let candidates = values
            .get(&structural_key(env, &parameter_type))
            .cloned()
            .unwrap_or_default();
        if candidates.is_empty() {
            if !advance_param_frame(&mut stack, &mut binding, rule) {
                return;
            }
            continue;
        }
        stack.push((candidates, 0));
        if !advance_param_frame(&mut stack, &mut binding, rule) {
            return;
        }
    }
}

/// Pick the next value for the deepest parameter frame, dropping exhausted
/// frames. Returns `false` when every tuple has been visited.
fn advance_param_frame(
    stack: &mut Vec<(Vec<Expr>, usize)>,
    binding: &mut Vec<(Name, Expr)>,
    rule: &RuleDecl,
) -> bool {
    loop {
        let Some((candidates, next)) = stack.last_mut() else {
            return false;
        };
        if *next < candidates.len() {
            let value = candidates[*next].clone();
            *next += 1;
            let level = stack.len() - 1;
            binding.truncate(level);
            binding.push((rule.params[level].0.clone(), value));
            return true;
        }
        stack.pop();
        binding.truncate(stack.len());
    }
}

// ---------------------------------------------------------------- verify

/// Independent check: is every step of this derivation a *legal instance* of
/// the rule it cites?
///
/// This shares no search state with the reasoner, only the environment.
///
/// It is the reason crate's internal checker, used by its own tests. The CLI's
/// user-visible check renders the generated certificate and runs
/// [`std_deduce_cert::check`] and [`std_deduce_cert::kernel_proof`] instead.
///
/// A rule application is legal when there is a single binding of the rule's
/// parameters such that:
///
/// 1. the conclusion is the instantiated conclusion;
/// 2. the i-th cited node is the instantiated i-th premise — in the rule's
///    own premise order, which is the order the reasoner records;
/// 3. no instantiated `unless` condition is proved anywhere in the derivation.
///
/// Point 3 is checked against *all* facts proved in the tree, not just those
/// already visited: the reasoner's semantics is a fixed point, under which a
/// fact derived later retracts an earlier conclusion. A derivation that keeps
/// the conclusion while also proving its blocker is therefore invalid, no
/// matter where the blocker sits. Proved propositions are compared by kernel
/// definitional equality, so alpha- and eta-variants of a blocker count as the
/// same proposition.
pub fn verify(env: &Env, d: &Derivation) -> Result<(), String> {
    // Pass 1: every node must be well-formed on its own, and we collect the
    // propositions proved anywhere in the tree for the `unless` check below.
    let mut proved: BTreeMap<String, Expr> = BTreeMap::new();
    for (id, node) in d.nodes.iter().enumerate() {
        match node {
            Node::Assumption { prop, .. } => {
                check::check(env, &Ctx::new(), prop, &Expr::Sort(0))
                    .map_err(|e| format!("节点 {id}：假设不是命题：{e}"))?;
                proved.insert(key(env, prop), prop.clone());
            }
            Node::RuleApplication { conclusion, .. } => {
                check::check(env, &Ctx::new(), conclusion, &Expr::Sort(0))
                    .map_err(|e| format!("节点 {id}：结论不是命题：{e}"))?;
                proved.insert(key(env, conclusion), conclusion.clone());
            }
            Node::InterpretationApplication { conclusion, .. } => {
                check::check(env, &Ctx::new(), conclusion, &Expr::Sort(0))
                    .map_err(|e| format!("节点 {id}：结论不是命题：{e}"))?;
                proved.insert(key(env, conclusion), conclusion.clone());
            }
            Node::AxiomInstance { conclusion, .. } => {
                check::check(env, &Ctx::new(), conclusion, &Expr::Sort(0))
                    .map_err(|e| format!("节点 {id}：公理实例的结论不是命题：{e}"))?;
                proved.insert(key(env, conclusion), conclusion.clone());
            }
            Node::Gap { .. } => {}
        }
    }

    // Pass 2: rebuild each interpretation application and each rule
    // application from its own evidence.
    for (id, node) in d.nodes.iter().enumerate() {
        if let Node::InterpretationApplication {
            interpretation,
            conclusion,
            premise,
        } = node
        {
            if !d
                .interpretations
                .iter()
                .any(|record| record.id == *interpretation)
            {
                return Err(format!(
                    "节点 {id}：解释 `{interpretation}` 未记录在本次启用的解释中"
                ));
            }
            let decl = env
                .get(interpretation)
                .ok_or_else(|| format!("节点 {id}：未知解释 `{interpretation}`"))?;
            let DeclKind::Interpretation(declared) = &decl.kind else {
                return Err(format!("节点 {id}：`{interpretation}` 不是解释"));
            };
            if *premise >= id {
                return Err(format!("节点 {id}：前提 {premise} 不是先前的节点"));
            }
            let actual = node_prop(&d.nodes[*premise])
                .ok_or_else(|| format!("节点 {id}：前提 {premise} 是未闭合的缺口，不能充当前提"))?;
            if !convertible(env, &Ctx::new(), actual, &declared.from)
                .map_err(|e| format!("节点 {id}：无法判定解释前提是否等价：{e}"))?
            {
                return Err(format!(
                    "节点 {id}：解释 `{interpretation}` 的 from 是 `{}`，而引用的节点 {premise} 证成的是 `{}`",
                    print_expr(&declared.from),
                    print_expr(actual)
                ));
            }
            if !convertible(env, &Ctx::new(), conclusion, &declared.to)
                .map_err(|e| format!("节点 {id}：无法判定解释结论是否等价：{e}"))?
            {
                return Err(format!(
                    "节点 {id}：解释 `{interpretation}` 的 to 是 `{}`，而本步写的是 `{}`",
                    print_expr(&declared.to),
                    print_expr(conclusion)
                ));
            }
            continue;
        }
        if let Node::AxiomInstance {
            axiom,
            identity,
            bindings,
            conclusion,
            ..
        } = node
        {
            let decl = env
                .get(axiom)
                .ok_or_else(|| format!("节点 {id}：未知全称公理 `{axiom}`"))?;
            let DeclKind::Fact {
                identity: declared_identity,
            } = &decl.kind
            else {
                return Err(format!("节点 {id}：`{axiom}` 不是断言命题的事实声明"));
            };
            if !declared_identity.seeds_derivation() {
                return Err(format!(
                    "节点 {id}：`{axiom}` 登记为对方争议，不能作为公理实例化的依据"
                ));
            }
            if declared_identity != identity {
                return Err(format!(
                    "节点 {id}：公理 `{axiom}` 的事实身份是{}，而本步记录的是{}",
                    declared_identity.label_zh(),
                    identity.label_zh()
                ));
            }
            let Some((binders, body)) = named_binders(env, &decl.ty)
                .map_err(|e| format!("节点 {id}：无法解析公理 `{axiom}` 的类型：{e}"))?
            else {
                return Err(format!(
                    "节点 {id}：`{axiom}` 的类型不是带命名绑定变量的全称命题"
                ));
            };
            if bindings.len() != binders.len() {
                return Err(format!(
                    "节点 {id}：公理 `{axiom}` 有 {} 个绑定变量，本步记录了 {} 个绑定",
                    binders.len(),
                    bindings.len()
                ));
            }
            let mut values = Vec::with_capacity(binders.len());
            for (index, (binder, (parameter, value))) in
                binders.iter().zip(bindings.iter()).enumerate()
            {
                if binder != parameter {
                    return Err(format!(
                        "节点 {id}：第 {} 个绑定变量应是 `{binder}`，本步记录的是 `{parameter}`",
                        index + 1
                    ));
                }
                if !is_closed(value) {
                    return Err(format!("节点 {id}：绑定变量 `{binder}` 的值不是闭合项"));
                }
                values.push(value.clone());
            }
            let expected = instantiate_telescope(&body, &values);
            let applied = Expr::apps(Expr::constant(axiom), values.iter().cloned());
            check::check(env, &Ctx::new(), &applied, &expected)
                .map_err(|e| format!("节点 {id}：公理 `{axiom}` 的实例不满足其绑定类型：{e}"))?;
            if !is_closed(&expected) {
                return Err(format!(
                    "节点 {id}：公理 `{axiom}` 的实例结论不是闭合命题（绑定不足或发生变量捕获）"
                ));
            }
            if key(env, &expected) != key(env, conclusion) {
                return Err(format!(
                    "节点 {id}：公理 `{axiom}` 按绑定得到的结论是 `{}`，而本步写的是 `{}`",
                    print_expr(&expected),
                    print_expr(conclusion)
                ));
            }
            continue;
        }
        let Node::RuleApplication {
            rule,
            conclusion,
            premises,
            selections,
            ..
        } = node
        else {
            continue;
        };

        let decl = env
            .get(rule)
            .ok_or_else(|| format!("节点 {id}：未知规则 `{rule}`"))?;
        let DeclKind::Rule(r) = &decl.kind else {
            return Err(format!("节点 {id}：`{rule}` 不是规则"));
        };

        if premises.len() != r.premises.len() {
            return Err(format!(
                "节点 {id}：规则 `{rule}` 有 {} 个前提，本步只引用了 {} 个节点",
                r.premises.len(),
                premises.len()
            ));
        }
        for p in premises {
            if *p >= id {
                return Err(format!("节点 {id}：前提 {p} 不是先前的节点"));
            }
        }

        // The premises determine the instance; the conclusion must then be
        // exactly what that instance yields. Doing it in this order (rather
        // than fitting the conclusion first and forgiving the premises) is
        // what makes a forged conclusion impossible: the forger has no
        // freedom left once the cited premises are fixed.
        let mut binding: Vec<(Name, Expr)> = Vec::new();
        for (i, p) in premises.iter().enumerate() {
            let actual = node_prop(&d.nodes[*p])
                .ok_or_else(|| format!("节点 {id}：前提 {p} 是未闭合的缺口，不能充当前提"))?;
            let selection = selections.get(i);
            match (&r.premises[i].kind, selection) {
                (PremiseKind::Plain(_), None | Some(PremiseSelection::Plain)) => {
                    let pattern = close_pattern(&r.open_premise_plain(i), &binding);
                    if !match_premise(env, &pattern, actual, &mut binding) {
                        return Err(format!(
                            "节点 {id}：规则 `{rule}` 的第 {} 个前提是 `{}`，\
                             而引用的节点 {p} 证成的是 `{}`",
                            i + 1,
                            print_expr(&pattern),
                            print_expr(actual)
                        ));
                    }
                }
                (PremiseKind::Or(branches), Some(PremiseSelection::Branch { branch, .. })) => {
                    if *branch >= branches.len() {
                        return Err(format!(
                            "节点 {id}：规则 `{rule}` 的第 {} 个前提只有 {} 个分支，\
                             本步选择的是第 {} 个",
                            i + 1,
                            branches.len(),
                            branch + 1
                        ));
                    }
                    let pattern = close_pattern(&r.open_branch(i, *branch), &binding);
                    if !match_premise(env, &pattern, actual, &mut binding) {
                        return Err(format!(
                            "节点 {id}：规则 `{rule}` 的第 {} 个前提选择了第 {} 个析取分支 `{}`，\
                             而引用的节点 {p} 证成的是 `{}`",
                            i + 1,
                            branch + 1,
                            print_expr(&pattern),
                            print_expr(actual)
                        ));
                    }
                }
                (
                    PremiseKind::Exists { binder, .. },
                    Some(PremiseSelection::Witness { witness, .. }),
                ) => {
                    if !is_concrete_witness(env, witness) {
                        return Err(format!(
                            "节点 {id}：规则 `{rule}` 的第 {} 个前提的见证 `{}` 不是已声明个体",
                            i + 1,
                            print_expr(witness)
                        ));
                    }
                    let body = close_pattern(&r.open_exists_body(i), &binding);
                    let expected =
                        substitute_pattern_constants(&body, &[(binder.clone(), witness.clone())]);
                    if !convertible(env, &Ctx::new(), &expected, actual)
                        .map_err(|error| format!("节点 {id}：无法判定见证体的等价性：{error}"))?
                    {
                        return Err(format!(
                            "节点 {id}：规则 `{rule}` 的第 {} 个存在前提在见证 `{}` 下的体是 `{}`，\
                             而引用的节点 {p} 证成的是 `{}`",
                            i + 1,
                            print_expr(witness),
                            print_expr(&expected),
                            print_expr(actual)
                        ));
                    }
                }
                (PremiseKind::Or(_), _) => {
                    return Err(format!(
                        "节点 {id}：规则 `{rule}` 的第 {} 个前提是析取，本步没有记录选择",
                        i + 1
                    ));
                }
                (PremiseKind::Exists { .. }, _) => {
                    return Err(format!(
                        "节点 {id}：规则 `{rule}` 的第 {} 个前提是存在量词，本步没有记录见证",
                        i + 1
                    ));
                }
                (PremiseKind::Plain(_), Some(_)) => {
                    return Err(format!(
                        "节点 {id}：规则 `{rule}` 的第 {} 个前提是普通命题，不能记录选择",
                        i + 1
                    ));
                }
            }
        }

        // A parameter no premise constrains is free: the step would be
        // asserting a fact about an individual of the writer's choosing.
        for (binder, _) in &r.params {
            if !binding.iter().any(|(k, _)| *k == *binder) {
                return Err(format!(
                    "节点 {id}：参数 `{binder}` 未被任何前提确定，本步不是规则 `{rule}` 的完整实例"
                ));
            }
        }

        // Now the conclusion must be the instance the premises produced.
        let open_conclusion = r.open_conclusion();
        let expected = close_pattern(&open_conclusion, &binding);
        if key(env, &expected) != key(env, conclusion) {
            return Err(format!(
                "节点 {id}：前提确立的实例结论是 `{}`，而本步写的是 `{}`",
                print_expr(&expected),
                print_expr(conclusion)
            ));
        }

        // Guards are instance conditions, so this step only exists if every one
        // of them holds. They are re-evaluated from the declaration and the
        // binding the premises produced, not from any recorded form; a guard
        // that was not judged is an error, never a pass.
        for i in 0..r.guards.len() {
            let closed = close_pattern(&r.open_guard(i), &binding);
            let holds = evaluate_comparison(env, &closed).map_err(|error| {
                format!(
                    "节点 {id}：规则 `{rule}` 的第 {} 条守卫无法判定：{error}；\
                     守卫求值失败不当作 false",
                    i + 1
                )
            })?;
            if !holds {
                return Err(format!(
                    "节点 {id}：规则 `{rule}` 的第 {} 条守卫「{}」不成立，本步不该成立",
                    i + 1,
                    print_expr(&closed)
                ));
            }
        }

        // A blocker that holds anywhere in the derivation invalidates the
        // step: under the fixed-point semantics the conclusion would have
        // been retracted. A comparison that fails is an error, never a pass.
        for u in &r.unlesses {
            let closed = close_pattern(&r.open_unless_text(u), &binding);
            if blocker_proved(env, &proved, &closed)
                .map_err(|message| format!("节点 {id}：{message}"))?
            {
                return Err(format!(
                    "节点 {id}：规则 `{rule}` 的阻断条件「{}」已成立，本步不该成立",
                    print_expr(&closed)
                ));
            }
        }
    }
    Ok(())
}

/// The proposition a node proves, if it proves one.
fn node_prop(n: &Node) -> Option<&Expr> {
    match n {
        Node::Assumption { prop, .. } => Some(prop),
        Node::RuleApplication { conclusion, .. } => Some(conclusion),
        Node::InterpretationApplication { conclusion, .. } => Some(conclusion),
        Node::AxiomInstance { conclusion, .. } => Some(conclusion),
        Node::Gap { .. } => None,
    }
}

// ---------------------------------------------------------------- certificate

/// Convert a derivation into the versioned certificate format.
///
/// Node order, premise order, bindings, sources, conflicts and the root are
/// preserved exactly, so the certificate describes the same proof graph as
/// the derivation. Every gap becomes a `MissingPremise` obligation and every
/// unresolved conflict becomes an `UnresolvedConflict` obligation; both carry
/// the node or propositions they are about, and the unresolved description
/// names the reason. No source, subject or object is invented for them. A
/// generation timestamp stays empty, and the environment identity is
/// [`std_deduce_cert::EnvironmentIdentity::Unrecorded`]: this crate knows
/// nothing about packs or corpora, so only the CLI can stamp a real identity
/// before exporting.
///
/// `env` is the environment the derivation was produced in. It is read for one
/// thing only: the `open` markers ([`Env::open_predicates`]). When the root's
/// proof graph turns such a concept (`重大`, `情节严重`) into a proved
/// proposition through a rule, a universal instance or the root assumption, the
/// certificate gains one `open_concept` obligation naming the concepts and the
/// nodes that state them, so an open concept is never exported as an
/// unconditional conclusion. An `interpretation_application` that licenses the
/// concept releases the obligation: the sourced interpretation is the human
/// reading. The obligation is computed by
/// [`std_deduce_cert::open_concept_dependency`], the same function the
/// certificate checker recomputes with; a derivation over no open concept, or
/// one that only licensed it through an enabled interpretation, records none.
///
/// `priority_order` is the [`Reasoner::priority_order`] of the reasoner that
/// produced `d`. It is consulted only to say how many recorded priority edges
/// lie on a priority cycle in an unresolved-conflict description; a derivation
/// without an unusable priority never reads it. Passing an order from another
/// environment would misdescribe that count, so callers get it from the
/// reasoner that produced the derivation.
///
/// Every kernel expression goes through [`std_deduce_cert::CertExpr::try_from`].
/// An expression that cannot be represented aborts the conversion with an
/// error naming the node and the field, rather than being dropped.
pub fn certificate(
    env: &Env,
    d: &Derivation,
    priority_order: &PriorityOrder,
) -> Result<std_deduce_cert::Certificate, String> {
    let mut assumptions = Vec::new();
    let mut nodes = Vec::with_capacity(d.nodes.len());
    let mut open_obligations = Vec::new();

    // Only the interpretations this derivation cites are listed: an
    // application node or a conflict witness. They are sorted by id, and the
    // nodes and conflict witnesses refer to them by index in that order.
    let mut used: BTreeSet<Name> = BTreeSet::new();
    for node in &d.nodes {
        if let Node::InterpretationApplication { interpretation, .. } = node {
            used.insert(interpretation.clone());
        }
    }
    for conflict in &d.conflicts {
        for provenance in [&conflict.left_by, &conflict.right_by] {
            if let Provenance::Interpretation(interpretation) = provenance {
                used.insert(interpretation.clone());
            }
        }
    }
    let mut records: Vec<&InterpretationRecord> = d
        .interpretations
        .iter()
        .filter(|record| used.contains(&record.id))
        .collect();
    records.sort_by(|a, b| a.id.cmp(&b.id));
    let interpretations: Vec<std_deduce_cert::Interpretation> = records
        .iter()
        .map(|record| {
            Ok::<_, String>(std_deduce_cert::Interpretation {
                id: record.id.to_string(),
                direction: (&record.direction).into(),
                from: cert_expr(&record.from, None, &format!("解释 `{}` 的 from", record.id))?,
                to: cert_expr(&record.to, None, &format!("解释 `{}` 的 to", record.id))?,
                sources: record
                    .sources
                    .iter()
                    .map(std_deduce_cert::Source::from)
                    .collect(),
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let interpretation_index: BTreeMap<Name, usize> = records
        .iter()
        .enumerate()
        .map(|(index, record)| (record.id.clone(), index))
        .collect();
    for name in &used {
        if !interpretation_index.contains_key(name) {
            return Err(format!("推导引用了未在本次启用记录中登记的解释 `{name}`"));
        }
    }

    for (id, node) in d.nodes.iter().enumerate() {
        match node {
            Node::Assumption {
                prop,
                identity,
                sources,
                label,
                occurred_at,
                occurred_in,
            } => {
                let assumption = assumptions.len();
                assumptions.push(std_deduce_cert::Assumption {
                    proposition: cert_expr(prop, Some(id), "假设命题")?,
                    identity: std_deduce_cert::FactIdentity::from(identity),
                    sources: sources.iter().map(std_deduce_cert::Source::from).collect(),
                    label: label.clone(),
                    occurred_at: explicit_option(occurred_at.clone()),
                    occurred_in: explicit_option(occurred_in.clone()),
                });
                nodes.push(std_deduce_cert::Node::Assumption { assumption });
            }
            Node::RuleApplication {
                rule,
                conclusion,
                computed,
                premises,
                selections,
                guard_judgements,
                bindings,
                sources,
                applicability,
            } => {
                let mut converted = Vec::with_capacity(bindings.len());
                for (parameter, value) in bindings {
                    converted.push(std_deduce_cert::Binding {
                        parameter: parameter.to_string(),
                        value: cert_expr(value, Some(id), &format!("参数 `{parameter}` 的绑定值"))?,
                    });
                }
                let scope = rule_scope(env, rule, id)?;
                let computed = match computed {
                    Some(expression) => Some(cert_expr(expression, Some(id), "计算前的结论")?),
                    None => None,
                };
                let guards = cert_guards(env, rule, guard_judgements, Some(id))?;
                let mut choices = Vec::new();
                for selection in selections {
                    if let Some(choice) = selection.certificate_choice()? {
                        choices.push(choice);
                    }
                }
                nodes.push(std_deduce_cert::Node::RuleApplication {
                    rule: rule.to_string(),
                    conclusion: cert_expr(conclusion, Some(id), "结论")?,
                    computed,
                    premises: premises.clone(),
                    choices,
                    bindings: converted,
                    guards,
                    sources: sources.iter().map(std_deduce_cert::Source::from).collect(),
                    applicability: Box::new(applicability::certificate_applicability(
                        &scope,
                        applicability,
                    )),
                });
            }
            Node::InterpretationApplication {
                interpretation,
                conclusion,
                premise,
            } => {
                let Some(index) = interpretation_index.get(interpretation) else {
                    return Err(format!(
                        "节点 {id} 引用的解释 `{interpretation}` 没有进入证书的解释表"
                    ));
                };
                nodes.push(std_deduce_cert::Node::InterpretationApplication {
                    interpretation: *index,
                    premise: *premise,
                    conclusion: cert_expr(conclusion, Some(id), "结论")?,
                });
            }
            Node::AxiomInstance {
                axiom,
                identity,
                bindings,
                conclusion,
                sources,
            } => {
                let converted = bindings
                    .iter()
                    .map(|(parameter, value)| {
                        Ok(std_deduce_cert::Binding {
                            parameter: parameter.to_string(),
                            value: cert_expr(
                                value,
                                Some(id),
                                &format!("绑定变量 `{parameter}` 的取值"),
                            )?,
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                nodes.push(std_deduce_cert::Node::AxiomInstance {
                    axiom: axiom.to_string(),
                    identity: std_deduce_cert::FactIdentity::from(identity),
                    bindings: converted,
                    conclusion: cert_expr(conclusion, Some(id), "公理实例的结论")?,
                    sources: sources.iter().map(std_deduce_cert::Source::from).collect(),
                });
            }
            Node::Gap {
                prop,
                candidates,
                axiom_candidates,
                note,
            } => {
                let mut converted = Vec::with_capacity(candidates.len());
                for candidate in candidates {
                    let bindings = candidate
                        .bindings
                        .iter()
                        .map(|(parameter, value)| {
                            Ok(std_deduce_cert::Binding {
                                parameter: parameter.to_string(),
                                value: cert_expr(
                                    value,
                                    Some(id),
                                    &format!(
                                        "候选规则 `{}` 的参数 `{parameter}` 绑定值",
                                        candidate.rule
                                    ),
                                )?,
                            })
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    let held = candidate
                        .held
                        .iter()
                        .enumerate()
                        .map(|(i, expr)| {
                            cert_expr(
                                expr,
                                Some(id),
                                &format!(
                                    "候选规则 `{}` 的第 {} 个已持有前提",
                                    candidate.rule,
                                    i + 1
                                ),
                            )
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    let missing = candidate
                        .missing
                        .iter()
                        .enumerate()
                        .map(|(i, expr)| {
                            cert_expr(
                                expr,
                                Some(id),
                                &format!("候选规则 `{}` 的第 {} 个缺失前提", candidate.rule, i + 1),
                            )
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    let blocked_by = candidate
                        .blocked_by
                        .iter()
                        .enumerate()
                        .map(|(i, expr)| {
                            cert_expr(
                                expr,
                                Some(id),
                                &format!("候选规则 `{}` 的第 {} 个阻断条件", candidate.rule, i + 1),
                            )
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    let scope = rule_scope(env, &candidate.rule, id)?;
                    let guards = cert_guards(env, &candidate.rule, &candidate.guards, Some(id))?;
                    let mut choices = Vec::new();
                    for selection in &candidate.choices {
                        if let Some(choice) = selection.certificate_choice()? {
                            choices.push(choice);
                        }
                    }
                    converted.push(std_deduce_cert::GapCandidate {
                        rule: candidate.rule.to_string(),
                        bindings,
                        held,
                        missing,
                        missing_branches: candidate.missing_branches.clone(),
                        choices,
                        blocked_by,
                        guards,
                        sources: candidate
                            .sources
                            .iter()
                            .map(std_deduce_cert::Source::from)
                            .collect(),
                        applicability: applicability::certificate_applicability(
                            &scope,
                            &candidate.applicability,
                        ),
                    });
                }
                let converted_axioms = axiom_candidates
                    .iter()
                    .map(|candidate| {
                        let bindings = candidate
                            .bindings
                            .iter()
                            .map(|(variable, value)| {
                                Ok(std_deduce_cert::Binding {
                                    parameter: variable.to_string(),
                                    value: cert_expr(
                                        value,
                                        Some(id),
                                        &format!(
                                            "缺口公理候选 `{}` 的绑定变量 `{variable}` 取值",
                                            candidate.axiom
                                        ),
                                    )?,
                                })
                            })
                            .collect::<Result<Vec<_>, String>>()?;
                        Ok(std_deduce_cert::GapAxiomCandidate {
                            axiom: candidate.axiom.to_string(),
                            bindings,
                            problem: candidate.problem.clone(),
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                nodes.push(std_deduce_cert::Node::Gap {
                    proposition: cert_expr(prop, Some(id), "缺口命题")?,
                    candidates: converted,
                    axiom_candidates: converted_axioms,
                    note: note.clone(),
                });
                open_obligations.push(std_deduce_cert::OpenObligation {
                    id: format!("gap-{id}"),
                    kind: std_deduce_cert::ObligationKind::MissingPremise,
                    description: match note {
                        Some(note) => format!("缺口「{}」：{note}", print_expr(prop)),
                        None => format!("缺口「{}」：没有可用的推导", print_expr(prop)),
                    },
                    nodes: vec![id],
                });
            }
        }
    }

    // The certificate's witness table follows the derivation's: entries are
    // ordered by the structural key of the conclusion and witnesses by the
    // order the reasoner already fixed (rule name, then binding structure).
    let mut groups: Vec<&WitnessGroup> = d.alternatives.iter().collect();
    groups.sort_by_key(|group| structural_key(env, &group.proposition));
    let mut alternatives = Vec::with_capacity(groups.len());
    for (index, group) in groups.iter().enumerate() {
        let label = format!("第 {} 条结论见证", index + 1);
        if group.witnesses.len() > std_deduce_cert::MAX_CERT_WITNESSES_PER_CONCLUSION {
            return Err(format!(
                "{label}的见证数量超过每个结论 {} 条上限：实际 {} 条",
                std_deduce_cert::MAX_CERT_WITNESSES_PER_CONCLUSION,
                group.witnesses.len()
            ));
        }
        if group.truncated
            && group.witnesses.len() != std_deduce_cert::MAX_CERT_WITNESSES_PER_CONCLUSION
        {
            return Err(format!(
                "{label}标记为截断，但见证数量是 {} 条而不是上限 {} 条：截断标记与实际记录不符",
                group.witnesses.len(),
                std_deduce_cert::MAX_CERT_WITNESSES_PER_CONCLUSION
            ));
        }
        for witness in &group.witnesses {
            if *witness >= d.nodes.len() {
                return Err(format!(
                    "{label}引用的见证节点 {witness} 越界：推导只有 {} 个节点",
                    d.nodes.len()
                ));
            }
        }
        alternatives.push(std_deduce_cert::Alternative {
            proposition: cert_expr(&group.proposition, None, &format!("{label}的命题"))?,
            witnesses: group.witnesses.clone(),
            truncated: group.truncated,
        });
    }

    let conflicts = d
        .conflicts
        .iter()
        .enumerate()
        .map(|(i, conflict)| {
            Ok(std_deduce_cert::Conflict {
                left: cert_expr(&conflict.left, None, &format!("冲突 {} 的左命题", i + 1))?,
                right: cert_expr(&conflict.right, None, &format!("冲突 {} 的右命题", i + 1))?,
                left_by: cert_provenance(&conflict.left_by, &interpretation_index)?,
                right_by: cert_provenance(&conflict.right_by, &interpretation_index)?,
                resolution: cert_resolution(&conflict.resolution),
            })
        })
        .collect::<Result<Vec<_>, String>>()?;

    for (index, conflict) in d.conflicts.iter().enumerate() {
        let Resolution::Unresolved { reason } = &conflict.resolution else {
            continue;
        };
        let explanation = match reason {
            UnresolvedReason::ConflictingAssumptions => {
                // Both sides are facts recorded as assumption nodes; the
                // identity each side was registered under decides which
                // sentence describes the standoff.
                match (
                    recorded_identity(d, &conflict.left),
                    recorded_identity(d, &conflict.right),
                ) {
                    (Some(left), Some(right)) if left.is_strict() && right.is_strict() => {
                        "两侧都是严格事实，事实之间没有先后".to_owned()
                    }
                    (Some(left), Some(right)) if !left.is_strict() && !right.is_strict() => {
                        "两侧都只是主张，未经证明，不能判出一方胜出".to_owned()
                    }
                    // One strict fact and one claim is decided, not unresolved,
                    // so an unmatched or mixed pair means this derivation does
                    // not describe the conflict. Fall back to the reason-only
                    // wording rather than invent an identity.
                    _ => "两侧都是事实，身份无法确定，不能判出一方胜出".to_owned(),
                }
            }
            UnresolvedReason::NonStrictFact { identity } => {
                // The fact side is the one the conflict records as an
                // assumption. `resolve` records this reason only for a
                // fact-versus-conclusion pair (a rule application or an
                // interpretation application); a missing fact side is an
                // internal inconsistency, never a reason to invent one.
                let fact_side = match (&conflict.left_by, &conflict.right_by) {
                    (Provenance::Assumption, _) => &conflict.left,
                    (_, Provenance::Assumption) => &conflict.right,
                    _ => {
                        return Err(format!(
                            "第 {} 个冲突记录为「主张与结论」未决，但两侧都不是事实：\
                             内部状态不一致",
                            index + 1
                        ));
                    }
                };
                let beaten = if matches!(conflict.left_by, Provenance::Interpretation(_))
                    || matches!(conflict.right_by, Provenance::Interpretation(_))
                {
                    "解释结论"
                } else {
                    "规则结论"
                };
                format!(
                    "「{}」只是「{}」，未经证明，不能自动胜过{beaten}",
                    print_expr(fact_side),
                    identity.label_zh()
                )
            }
            UnresolvedReason::UnknownWitnesses => {
                "有一方的规则见证已无法重建，无法核对优先关系".to_owned()
            }
            UnresolvedReason::NoPriority => {
                // Rules of one `revision` group are versions of the same
                // provision; saying only "no priority was declared" would hide
                // that the reader is choosing between an old and a new version.
                match shared_revision_group(env, &conflict.left_by, &conflict.right_by) {
                    Some(group) => format!(
                        "没有声明任何优先关系；两侧是同一法条的两个历史版本（revision 组 `{}`），\
                         没有声明哪一版优先，系统不自动选新法或旧法",
                        group.label()
                    ),
                    None => "没有声明任何优先关系".to_owned(),
                }
            }
            UnresolvedReason::PriorityUnusable { declared } => {
                let in_cycle = declared
                    .iter()
                    .filter(|edge| priority_order.same_cycle(&edge.winner, &edge.loser))
                    .count();
                format!(
                    "已有 {} 条优先声明，但不足以裁决；其中 {} 条落在优先级环内",
                    declared.len(),
                    in_cycle
                )
            }
        };
        open_obligations.push(std_deduce_cert::OpenObligation {
            id: format!("conflict-{index}"),
            kind: std_deduce_cert::ObligationKind::UnresolvedConflict,
            description: format!(
                "冲突未决：「{}」与「{}」（{explanation}）",
                print_expr(&conflict.left),
                print_expr(&conflict.right)
            ),
            nodes: Vec::new(),
        });
    }

    let mut certificate = std_deduce_cert::Certificate {
        format_version: std_deduce_cert::FormatVersion::CURRENT,
        // The reasoner knows nothing about profiles, pack versions or corpus
        // files; the CLI stamps the real identity before exporting. The marker
        // cannot be serialized, so this certificate can never reach disk.
        environment: std_deduce_cert::EnvironmentIdentity::Unrecorded,
        assumptions,
        interpretations,
        nodes,
        root: d.root,
        alternatives,
        conflicts,
        open_obligations,
        metadata: std_deduce_cert::Metadata {
            generated_at: None,
            tool: Some("std-deduce".to_owned()),
            tool_version: Some(env!("CARGO_PKG_VERSION").to_owned()),
        },
    };
    // A root derivation that turns an open concept into a proved proposition
    // must say so. The obligation is recomputed from the environment markers
    // and the proof graph by the same function the certificate checker uses,
    // and a derivation over no open concept records none of it.
    if let Some(dependency) = std_deduce_cert::open_concept_dependency(env, &certificate)? {
        certificate.open_obligations.push(dependency.obligation());
    }
    Ok(certificate)
}

/// The recorded scope of the rule a derivation step applies.
///
/// The applicability record must quote the environment's declaration, so the
/// checker can compare it field by field. A step that names a declaration this
/// environment no longer holds cannot be converted rather than being exported
/// with a guessed scope.
fn rule_scope(
    env: &Env,
    rule: &Name,
    node: usize,
) -> Result<std_deduce_kernel::meta::Scope, String> {
    let Some(decl) = env.get(rule) else {
        return Err(format!(
            "节点 {node} 引用的规则 `{rule}` 不在当前环境中，无法记录其适用范围"
        ));
    };
    let DeclKind::Rule(_) = &decl.kind else {
        return Err(format!(
            "节点 {node} 引用的 `{rule}` 不是规则，无法记录其适用范围"
        ));
    };
    Ok(decl.scope.clone())
}

/// An optional string in the certificate's explicit form: a value or `null`.
fn explicit_option(value: Option<String>) -> std_deduce_cert::Explicit<String> {
    match value {
        Some(value) => std_deduce_cert::Explicit::some(value),
        None => std_deduce_cert::Explicit::none(),
    }
}

/// Encode one kernel expression, naming its location on failure.
fn cert_expr(expr: &Expr, node: Option<usize>, role: &str) -> Result<CertExpr, String> {
    CertExpr::try_from(expr).map_err(|error| match node {
        Some(id) => format!("节点 {id} 的{role}无法转换为证书表达式：{error}"),
        None => format!("{role}无法转换为证书表达式：{error}"),
    })
}

/// Encode one instance's guard judgements for the certificate.
///
/// The record carries the *declared* guard (rebuilt from the environment rule
/// as `open_guard`, parameters as `?<name>`), the guard closed by the recorded
/// bindings, and the evaluated truth value. The certificate checker recomputes
/// all three from the rule declaration and the bindings, so this function only
/// encodes what the reasoner already judged; it never decides a guard itself.
fn cert_guards(
    env: &Env,
    rule: &Name,
    judgements: &[GuardJudgement],
    node: Option<usize>,
) -> Result<Vec<std_deduce_cert::GuardRecord>, String> {
    if judgements.is_empty() {
        return Ok(Vec::new());
    }
    let decl = env
        .get(rule)
        .ok_or_else(|| format!("规则 `{rule}` 不在环境中，无法记录守卫判定"))?;
    let DeclKind::Rule(declared) = &decl.kind else {
        return Err(format!("`{rule}` 不是规则，无法记录守卫判定"));
    };
    if judgements.len() != declared.guards.len() {
        return Err(format!(
            "规则 `{rule}` 声明了 {} 条守卫，但推导只记录了 {} 条",
            declared.guards.len(),
            judgements.len()
        ));
    }
    let mut out = Vec::with_capacity(judgements.len());
    for judgement in judgements {
        let i = judgement.index;
        if i >= declared.guards.len() {
            return Err(format!(
                "规则 `{rule}` 的守卫序号 {i} 超出声明范围（共 {} 条）",
                declared.guards.len()
            ));
        }
        let expression = cert_expr(
            &declared.open_guard(i),
            node,
            &format!("规则 `{rule}` 第 {} 条守卫的声明形式", i + 1),
        )?;
        let instance = cert_expr(
            &judgement.instance,
            node,
            &format!("规则 `{rule}` 第 {} 条守卫的求值形态", i + 1),
        )?;
        out.push(std_deduce_cert::GuardRecord {
            index: i,
            expression,
            instance,
            holds: match judgement.holds {
                Some(value) => std_deduce_cert::Explicit::some(value),
                None => std_deduce_cert::Explicit::none(),
            },
        });
    }
    Ok(out)
}

/// The identity the derivation recorded for an assumption of `expr`.
///
/// [`certificate`] converts a derivation without access to the reasoner's
/// assumption table, so it reads the identity from the derivation's assumption
/// nodes — the same entries the table produced. A fact that appears as a
/// conflict side is recorded as an assumption node; no match means the side was
/// derived, not assumed, and therefore has no identity.
fn recorded_identity(d: &Derivation, expr: &Expr) -> Option<FactIdentity> {
    d.nodes.iter().find_map(|node| match node {
        Node::Assumption { prop, identity, .. } if prop == expr => Some(*identity),
        _ => None,
    })
}

fn cert_provenance(
    provenance: &Provenance,
    interpretation_index: &BTreeMap<Name, usize>,
) -> Result<std_deduce_cert::Provenance, String> {
    Ok(match provenance {
        Provenance::Assumption => std_deduce_cert::Provenance::Assumption,
        Provenance::Rules(rules) => std_deduce_cert::Provenance::Rules {
            rules: rules.iter().map(ToString::to_string).collect(),
        },
        Provenance::Axiom(axiom) => std_deduce_cert::Provenance::Axiom {
            axiom: axiom.to_string(),
        },
        Provenance::Interpretation(interpretation) => {
            let Some(index) = interpretation_index.get(interpretation) else {
                return Err(format!(
                    "冲突引用了解释 `{interpretation}`，但它没有进入证书的解释表"
                ));
            };
            std_deduce_cert::Provenance::Interpretation {
                interpretation: *index,
            }
        }
    })
}

fn cert_resolution(resolution: &Resolution) -> std_deduce_cert::Resolution {
    match resolution {
        Resolution::Defeated { winner, basis } => std_deduce_cert::Resolution::Defeated {
            winner: cert_side(*winner),
            basis: match basis {
                ResolutionBasis::Assumption => std_deduce_cert::ResolutionBasis::Assumption,
                ResolutionBasis::Priority { edges } => std_deduce_cert::ResolutionBasis::Priority {
                    edges: edges.iter().map(cert_priority_edge).collect(),
                },
            },
        },
        Resolution::Unresolved { reason } => std_deduce_cert::Resolution::Unresolved {
            reason: match reason {
                UnresolvedReason::ConflictingAssumptions => {
                    std_deduce_cert::UnresolvedReason::ConflictingAssumptions
                }
                UnresolvedReason::NonStrictFact { identity } => {
                    std_deduce_cert::UnresolvedReason::NonStrictFact {
                        identity: std_deduce_cert::FactIdentity::from(identity),
                    }
                }
                UnresolvedReason::UnknownWitnesses => {
                    std_deduce_cert::UnresolvedReason::UnknownWitnesses
                }
                UnresolvedReason::NoPriority => std_deduce_cert::UnresolvedReason::NoPriority,
                UnresolvedReason::PriorityUnusable { declared } => {
                    std_deduce_cert::UnresolvedReason::PriorityUnusable {
                        declared: declared.iter().map(cert_priority_edge).collect(),
                    }
                }
            },
        },
    }
}

fn cert_side(side: Side) -> std_deduce_cert::Side {
    match side {
        Side::Left => std_deduce_cert::Side::Left,
        Side::Right => std_deduce_cert::Side::Right,
    }
}

fn cert_priority_edge(edge: &PriorityEdge) -> std_deduce_cert::PriorityEdge {
    std_deduce_cert::PriorityEdge {
        winner: edge.winner.to_string(),
        loser: edge.loser.to_string(),
        origin: match &edge.origin {
            PriorityOrigin::Declaration {
                declared_in,
                sources,
            } => std_deduce_cert::PriorityOrigin::PriorityDeclaration {
                declared_in: declared_in.to_string(),
                sources: sources.iter().map(std_deduce_cert::Source::from).collect(),
            },
            PriorityOrigin::RuleClause {
                rule,
                clause,
                sources,
            } => std_deduce_cert::PriorityOrigin::RuleClause {
                declaring_rule: rule.to_string(),
                clause: match clause {
                    PriorityClause::Prefer => std_deduce_cert::PriorityClause::Prefer,
                    PriorityClause::DefeatedBy => std_deduce_cert::PriorityClause::DefeatedBy,
                },
                rule_sources: sources.iter().map(std_deduce_cert::Source::from).collect(),
            },
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A side whose witnesses can no longer be rebuilt must not lose by
    /// itself: the old "every rule on the other side is beaten" test was
    /// vacuously true for an empty side, so the other side won for free.
    #[test]
    fn an_empty_witness_never_loses_the_conflict_by_itself() {
        let env = Env::new();
        let reasoner = Reasoner::new(&env);
        let present = vec![std_deduce_kernel::name("r")];
        let empty: Vec<Name> = Vec::new();
        assert_eq!(
            reasoner.resolve(
                &Support::Rules(empty.clone()),
                &Support::Rules(present.clone())
            ),
            Resolution::Unresolved {
                reason: UnresolvedReason::UnknownWitnesses,
            }
        );
        assert_eq!(
            reasoner.resolve(&Support::Rules(present), &Support::Rules(empty)),
            Resolution::Unresolved {
                reason: UnresolvedReason::UnknownWitnesses,
            }
        );
    }
}
