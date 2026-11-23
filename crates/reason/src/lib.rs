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
//! * a strict assumption (a fact) outranks a defeasible conclusion;
//! * a declared priority between the rules on the two sides decides the
//!   conflict: `defeated_by` / `prefer` inside one package, or a top-level
//!   `priority … over …` declaration with its sources. A priority edge that
//!   lies on a priority cycle cannot decide anything, and priorities are never
//!   transitive: `A over B` and `B over C` do not make `A over C`;
//! * otherwise the conflict is unresolved, and **neither** conclusion enters
//!   the fact base. The recorded reason says whether the sides are conflicting
//!   assumptions, lack a declared priority, have priorities that do not cover
//!   the conflict (or lie in a cycle), or whether one side's witnesses can no
//!   longer be rebuilt. It is not silently dropped: `conflicts()` reports it,
//!   and the CLI prints both derivations and exits non-zero.
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
//! ## Certificates
//!
//! [`certificate`] converts a derivation into the versioned certificate
//! format owned by the `cert` crate. The conversion is structural: node
//! order, premise order, bindings, sources, conflicts and the root are
//! carried over unchanged. It does not decide anything the derivation did
//! not already decide, and it refuses to drop an expression it cannot
//! encode.

use std::collections::{BTreeMap, BTreeSet};

use std_deduce_cert::CertExpr;
use std_deduce_kernel::conv::convertible;
use std_deduce_kernel::env::{Decl, DeclKind, Env, RuleDecl, SourceRef};
use std_deduce_kernel::norm::{normalize, spine};
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{check, Ctx, Expr, Name};

// ---------------------------------------------------------------- nodes

#[derive(Debug, Clone)]
pub enum Node {
    Assumption {
        prop: Expr,
        sources: Vec<SourceRef>,
        label: Option<String>,
    },
    RuleApplication {
        rule: Name,
        conclusion: Expr,
        premises: Vec<usize>,
        /// The rule's parameters and the values this step bound them to.
        bindings: Vec<(Name, Expr)>,
        sources: Vec<SourceRef>,
    },
    /// An unclosed goal. The honest replacement for `sorry`.
    Gap {
        prop: Expr,
        candidates: Vec<GapCandidate>,
        note: Option<String>,
    },
}

#[derive(Debug, Clone)]
pub struct GapCandidate {
    pub rule: Name,
    /// Premises that are not known.
    pub missing: Vec<Expr>,
    /// `unless` conditions that *are* known, i.e. why this rule is blocked.
    pub blocked_by: Vec<Expr>,
    pub sources: Vec<SourceRef>,
}

#[derive(Debug, Clone, Default)]
pub struct Derivation {
    pub nodes: Vec<Node>,
    pub root: Option<usize>,
    pub conflicts: Vec<Conflict>,
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
    Assumption,
    Rules(Vec<Name>),
}

/// How a conflict was adjudicated.
///
/// A conflict is never decided by an internal preference: it is either
/// defeated by a declared priority or by the strictness of an assumption, or
/// it is reported as unresolved with the reason.
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
    /// A strict fact (assumption) outranks a defeasible conclusion.
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
    /// Both sides are strict facts; neither outranks the other.
    ConflictingAssumptions,
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

// ---------------------------------------------------------------- internals

struct Assumption {
    prop: Expr,
    sources: Vec<SourceRef>,
    label: Option<String>,
}

/// One instantiation of a rule against a set of known facts.
struct Instance {
    conclusion: Expr,
    premise_keys: Vec<String>,
    /// Open `unless` expressions, already closed by this instantiation.
    unlesses: Vec<Expr>,
    /// The rule's parameters and the values this instantiation bound them to.
    bindings: Vec<(Name, Expr)>,
}

/// The settled result: the set of facts and a derivation for each.
struct Fixed {
    facts: BTreeMap<String, Expr>,
    nodes: Vec<Node>,
    ids: BTreeMap<String, usize>,
    conflicts: Vec<Conflict>,
    /// Conclusions that were derived but kept out of `facts` because of a
    /// conflict, keyed by the same normalised key as `facts`.
    contested: BTreeMap<String, Conflict>,
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
    /// symmetric contradiction relation, closed from `contrary` declarations
    contraries: BTreeMap<Name, BTreeSet<Name>>,
    /// predicate -> argument positions declared single-valued (`unique`)
    uniques: BTreeMap<Name, BTreeSet<usize>>,
    fixed: Option<Fixed>,
    max_rounds: usize,
}

impl<'a> Reasoner<'a> {
    pub fn new(env: &'a Env) -> Self {
        let declared = declared_priorities(env);
        let graph = priority_graph(env, &declared);
        let mut contraries: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();
        for (a, b) in env.contrary_pairs() {
            contraries.entry(a.clone()).or_default().insert(b.clone());
            contraries.entry(b).or_default().insert(a);
        }
        let mut uniques: BTreeMap<Name, BTreeSet<usize>> = BTreeMap::new();
        for (pred, index) in env.unique_positions() {
            uniques.entry(pred).or_default().insert(index);
        }
        Reasoner {
            env,
            assumptions: Vec::new(),
            declared,
            scc: graph.scc,
            effective: graph.effective,
            cycles: graph.cycles,
            contraries,
            uniques,
            fixed: None,
            max_rounds: 256,
        }
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

    /// Register an assumption. Its type must be a proposition.
    pub fn assume(
        &mut self,
        prop: &Expr,
        sources: Vec<SourceRef>,
        label: Option<String>,
    ) -> Result<(), String> {
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
        self.assumptions.push(Assumption {
            prop: prop.clone(),
            sources,
            label,
        });
        Ok(())
    }

    /// Register every axiom in the ledger as an assumption.
    ///
    /// An axiom has two shapes, and they assert different things:
    ///
    /// - `axiom h : 侵占 张三` — the declared type is a proposition; what it
    ///   asserts is that proposition.
    /// - `axiom 假 : Prop` — the declared type is a *sort*; this only declares
    ///   a proposition constant. Asserting it would mean asserting `Prop`,
    ///   which lives in `Type`. Such declarations contribute nothing to
    ///   reasoning and are skipped.
    ///
    /// Rules are declarations too, but they drive the reasoner rather than
    /// seed it, so they are not assumptions.
    pub fn assume_ledger_axioms(&mut self) -> Result<(), String> {
        // Sorted by declaration name: the assumption list feeds the node
        // order, so it must not depend on the order independent packages were
        // loaded in.
        let env = self.env;
        let mut axioms: Vec<&Decl> = env
            .iter()
            .filter(|decl| matches!(decl.kind, DeclKind::Axiom))
            .collect();
        axioms.sort_by(|a, b| a.name.cmp(&b.name));
        for decl in axioms {
            if !declared_type_is_prop(self.env, &decl.ty) {
                continue;
            }
            self.assume(&decl.ty, decl.sources.clone(), Some(decl.name.to_string()))?;
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
            let facts = self.fixed_point(&removed)?;
            let conflicts = self.detect_conflicts(&facts);
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
                let fixed = self.build_nodes(facts, conflicts, contested)?;
                self.fixed = Some(fixed);
                return Ok(());
            }
            removed = next_removed;
        }
        Err("冲突裁决在 256 轮内未收敛".into())
    }

    fn fixed_point(&self, removed: &BTreeSet<String>) -> Result<BTreeMap<String, Expr>, String> {
        let seeds: BTreeMap<String, Expr> = self
            .assumptions
            .iter()
            .map(|a| (self.key_of(&a.prop), a.prop.clone()))
            .filter(|(k, _)| !removed.contains(k))
            .collect();
        let mut k = seeds.clone();
        let mut previous: Option<BTreeMap<String, Expr>> = None;

        for _round in 0..self.max_rounds {
            let mut next = seeds.clone();
            let rules = self.rules();
            for (_name, rule) in &rules {
                for inst in self.enumerate(rule, &k) {
                    if blocked(&inst.unlesses, &k, self.env) {
                        continue;
                    }
                    next.entry(self.key_of(&inst.conclusion))
                        .or_insert_with(|| inst.conclusion.clone());
                }
            }
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

    fn rules(&self) -> Vec<(Name, RuleDecl)> {
        self.ordered_rules()
            .into_iter()
            .filter_map(|d| match &d.kind {
                DeclKind::Rule(r) => Some((d.name.clone(), (**r).clone())),
                _ => None,
            })
            .collect()
    }

    /// Every rule declaration of the environment, ordered by name, so that
    /// iteration never depends on the order independent packages were loaded
    /// in.
    fn ordered_rules(&self) -> Vec<&'a Decl> {
        let mut rules = self.env.rules();
        rules.sort_by(|a, b| a.name.cmp(&b.name));
        rules
    }

    /// Are two facts in conflict? Either their heads are declared contrary and
    /// their arguments match, or they share a head and differ exactly at a
    /// position declared `unique`.
    fn in_conflict(&self, a: &Expr, b: &Expr) -> bool {
        let (ha, aa) = spine(a);
        let (hb, ab) = spine(b);
        let (Expr::Const(ha), Expr::Const(hb)) = (ha, hb) else {
            return false;
        };
        if aa.len() != ab.len() {
            return false;
        }
        if ha != hb {
            return self.contraries.get(ha).is_some_and(|set| set.contains(hb))
                && aa
                    .iter()
                    .zip(ab.iter())
                    .all(|(x, y)| self.key_of(x) == self.key_of(y));
        }
        let Some(positions) = self.uniques.get(ha) else {
            return false;
        };
        let differing: Vec<usize> = (0..aa.len())
            .filter(|i| self.key_of(aa[*i]) != self.key_of(ab[*i]))
            .collect();
        differing.len() == 1 && positions.contains(&differing[0])
    }

    fn detect_conflicts(&self, facts: &BTreeMap<String, Expr>) -> Vec<Conflict> {
        let items: Vec<(&String, &Expr)> = facts.iter().collect();
        let mut out = Vec::new();
        for i in 0..items.len() {
            for j in (i + 1)..items.len() {
                let (ka, a) = items[i];
                let (kb, b) = items[j];
                if !self.in_conflict(a, b) {
                    continue;
                }
                let lb = self.provenance(ka, facts);
                let rb = self.provenance(kb, facts);
                let resolution = self.resolve(&lb, &rb);
                out.push(Conflict {
                    left: a.clone(),
                    right: b.clone(),
                    left_by: lb,
                    right_by: rb,
                    resolution,
                });
            }
        }
        out
    }

    fn provenance(&self, target: &str, facts: &BTreeMap<String, Expr>) -> Provenance {
        if self
            .assumptions
            .iter()
            .any(|a| self.key_of(&a.prop) == target)
        {
            return Provenance::Assumption;
        }
        Provenance::Rules(self.derivers(target, facts))
    }

    /// Every rule that has an unblocked instance concluding `target`, with all
    /// premises already in `facts`.
    fn derivers(&self, target: &str, facts: &BTreeMap<String, Expr>) -> Vec<Name> {
        let mut out = BTreeSet::new();
        for decl in self.env.rules() {
            let DeclKind::Rule(rule) = &decl.kind else {
                continue;
            };
            for inst in self.enumerate(rule, facts) {
                if self.key_of(&inst.conclusion) != target {
                    continue;
                }
                if blocked(&inst.unlesses, facts, self.env) {
                    continue;
                }
                if inst.premise_keys.iter().all(|pk| facts.contains_key(pk)) {
                    out.insert(decl.name.clone());
                }
            }
        }
        out.into_iter().collect()
    }

    /// Facts are strict and always win over defeasible conclusions. Between
    /// rules, a side wins only when every rule on it beats every rule on the
    /// other side through a declared priority that is not part of a cycle, and
    /// the other side is not covered in return. Priorities are not transitive
    /// and are never guessed: anything else is unresolved, with the reason.
    fn resolve(&self, left: &Provenance, right: &Provenance) -> Resolution {
        match (left, right) {
            (Provenance::Assumption, Provenance::Assumption) => Resolution::Unresolved {
                reason: UnresolvedReason::ConflictingAssumptions,
            },
            (Provenance::Assumption, _) => Resolution::Defeated {
                winner: Side::Left,
                basis: ResolutionBasis::Assumption,
            },
            (_, Provenance::Assumption) => Resolution::Defeated {
                winner: Side::Right,
                basis: ResolutionBasis::Assumption,
            },
            (Provenance::Rules(l), Provenance::Rules(r)) => {
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

    /// Build nodes in dependency order: an assumption first, then any rule
    /// application whose premises all already have ids.
    fn build_nodes(
        &self,
        facts: BTreeMap<String, Expr>,
        conflicts: Vec<Conflict>,
        contested: BTreeMap<String, Conflict>,
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
            let id = nodes.len();
            nodes.push(Node::Assumption {
                prop: a.prop.clone(),
                sources: a.sources.clone(),
                label: a.label.clone(),
            });
            ids.insert(k, id);
        }

        let mut pending: Vec<String> = facts
            .keys()
            .filter(|k| !ids.contains_key(k.as_str()))
            .cloned()
            .collect();
        pending.sort();

        while !pending.is_empty() {
            let mut progressed = false;
            let mut i = 0;
            while i < pending.len() {
                let target = pending[i].clone();
                if let Some((rule, inst, sources)) = self.witness(&target, &facts, &ids) {
                    let id = nodes.len();
                    let premises: Vec<usize> = inst.premise_keys.iter().map(|pk| ids[pk]).collect();
                    nodes.push(Node::RuleApplication {
                        rule,
                        conclusion: inst.conclusion,
                        premises,
                        bindings: inst.bindings,
                        sources,
                    });
                    ids.insert(target, id);
                    pending.remove(i);
                    progressed = true;
                } else {
                    i += 1;
                }
            }
            if !progressed {
                return Err(format!(
                    "无法为以下结论构造推导（可能存在依赖环）：{}",
                    pending.join("，")
                ));
            }
        }

        Ok(Fixed {
            facts,
            nodes,
            ids,
            conflicts,
            contested,
        })
    }

    /// Find an unblocked rule application that concludes `target` and whose
    /// premises already have node ids.
    fn witness(
        &self,
        target: &str,
        facts: &BTreeMap<String, Expr>,
        ids: &BTreeMap<String, usize>,
    ) -> Option<(Name, Instance, Vec<SourceRef>)> {
        for decl in self.ordered_rules() {
            let DeclKind::Rule(rule) = &decl.kind else {
                continue;
            };
            for inst in self.enumerate(rule, facts) {
                if self.key_of(&inst.conclusion) != target {
                    continue;
                }
                if blocked(&inst.unlesses, facts, self.env) {
                    continue;
                }
                if inst.premise_keys.iter().all(|pk| ids.contains_key(pk)) {
                    return Some((decl.name.clone(), inst, decl.sources.clone()));
                }
            }
        }
        None
    }

    /// Enumerate instances of `rule` against `facts`.
    ///
    /// Ordered backtracking over the premise list: premise `i` is a pattern
    /// open over the rule's binders; try each known fact, match, extend the
    /// binding, recurse. Facts are ground, so this is first-order matching.
    fn enumerate(&self, rule: &RuleDecl, facts: &BTreeMap<String, Expr>) -> Vec<Instance> {
        let mut out = Vec::new();
        let mut binding: Vec<(Name, Expr)> = Vec::new();
        let mut keys: Vec<String> = Vec::new();
        let rules = rule.clone();
        backtrack(
            &rules,
            0,
            facts,
            &mut binding,
            &mut keys,
            &mut out,
            rule.unlesses.len(),
        );
        out
    }

    // ------------------------------------------------------------ queries

    /// The environment this reasoner reads. Exposed so callers can check a
    /// certificate against the same declarations the derivation used.
    pub fn env(&self) -> &Env {
        self.env
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
                conflicts: f.conflicts.clone(),
            },
            None => Derivation::default(),
        }
    }

    /// A derivation that reaches `prop` even when it is not in the fact base.
    ///
    /// Used to show both sides of an unresolved conflict: the conclusion is
    /// not asserted, but the argument for it must still be inspectable.
    pub fn derivation_for(&self, prop: &Expr) -> Option<Derivation> {
        let k = self.key_of(prop);
        let base = self.fixed.as_ref()?;
        let mut facts = base.facts.clone();
        facts.insert(k.clone(), prop.clone());
        let fixed = self.build_nodes(facts, Vec::new(), BTreeMap::new()).ok()?;
        Some(Derivation {
            root: fixed.ids.get(&k).copied(),
            nodes: fixed.nodes,
            conflicts: Vec::new(),
        })
    }

    /// Why is `goal` unreachable? List candidate rules with what each is
    /// missing and what is blocking it.
    pub fn explain(&self, goal: &Expr) -> GapExplanation {
        let mut candidates = Vec::new();
        let note = if check::check(self.env, &Ctx::new(), goal, &Expr::Sort(0)).is_err() {
            Some("目标不是命题".to_string())
        } else if self.conflict_for(goal).is_some() {
            Some("目标处于冲突中：未决的结论不进入事实库，需要人工裁决".to_string())
        } else if self.knows(goal) {
            Some("目标已可推出".to_string())
        } else {
            None
        };
        if note.is_some() {
            return GapExplanation {
                goal: goal.clone(),
                candidates,
                note,
            };
        }
        let facts: BTreeMap<String, Expr> = self
            .fixed
            .as_ref()
            .map(|f| f.facts.clone())
            .unwrap_or_default();

        for decl in self.ordered_rules() {
            let DeclKind::Rule(rule) = &decl.kind else {
                continue;
            };
            // Match the rule head against the goal to get a candidate
            // instantiation, then instantiate premises and blockers with it.
            let mut binding = Vec::new();
            if !match_fact(&rule.open_conclusion(), goal, &mut binding) {
                continue;
            }
            let missing: Vec<Expr> = (0..rule.premises.len())
                .map(|i| close_pattern(&rule.open_premise(i), &binding))
                .filter(|p| !facts.contains_key(&self.key_of(p)))
                .collect();
            let blocked_by: Vec<Expr> = rule
                .unlesses
                .iter()
                .map(|u| close_pattern(&rule.open_unless_text(u), &binding))
                .filter(|u| blocked(std::slice::from_ref(u), &facts, self.env))
                .collect();
            candidates.push(GapCandidate {
                rule: decl.name.clone(),
                missing,
                blocked_by,
                sources: decl.sources.clone(),
            });
        }
        GapExplanation {
            goal: goal.clone(),
            candidates,
            note,
        }
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

fn backtrack(
    rule: &RuleDecl,
    idx: usize,
    facts: &BTreeMap<String, Expr>,
    binding: &mut Vec<(Name, Expr)>,
    keys: &mut Vec<String>,
    out: &mut Vec<Instance>,
    unless_len: usize,
) {
    if idx == rule.premises.len() {
        let conclusion = close_pattern(&rule.open_conclusion(), binding);
        let unlesses: Vec<Expr> = (0..unless_len)
            .map(|i| close_pattern(&rule.open_unless_text(&rule.unlesses[i]), binding))
            .collect();
        out.push(Instance {
            conclusion,
            premise_keys: keys.clone(),
            unlesses,
            bindings: binding.clone(),
        });
        return;
    }

    let pattern = close_pattern(&rule.open_premise(idx), binding);
    for (k, fact) in facts {
        if keys.contains(k) {
            continue;
        }
        let before = binding.len();
        let mut b = binding.clone();
        if !match_fact(&pattern, fact, &mut b) {
            continue;
        }
        *binding = b;
        keys.push(k.clone());
        backtrack(rule, idx + 1, facts, binding, keys, out, unless_len);
        keys.pop();
        binding.truncate(before);
    }
}

fn blocked(unlesses: &[Expr], facts: &BTreeMap<String, Expr>, env: &Env) -> bool {
    unlesses.iter().any(|u| {
        // A comparison that could not be decided is not evidence that the
        // blocker is absent: an undecidable condition may still hold, so the
        // conservative answer is "blocked". Never turn a failed comparison
        // into "not blocked".
        blocker_proved(env, facts, u).unwrap_or(true)
    })
}

/// Is the blocker `unless` established by a known fact, up to kernel
/// definitional equality?
///
/// The normalized printed key is an exact fast path. Alpha- and eta-equivalent
/// facts have different keys, so a miss compares every fact with the kernel's
/// [`convertible`]. A conversion error is returned to the caller, which must
/// not read it as "not a blocker".
fn blocker_proved(
    env: &Env,
    facts: &BTreeMap<String, Expr>,
    unless: &Expr,
) -> Result<bool, String> {
    if facts.contains_key(&key(env, unless)) {
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
        _ => false,
    }
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
        Expr::Sort(_) | Expr::Var(_) => p.clone(),
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

/// Is an axiom's declared type itself a proposition?
///
/// `侵占 张三 : Prop` — yes, so the axiom asserts that proposition.
/// `Prop : Type 1` — no, so the axiom only names a proposition constant.
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

// ---------------------------------------------------------------- gaps

#[derive(Debug, Clone)]
pub struct GapExplanation {
    pub goal: Expr,
    pub candidates: Vec<GapCandidate>,
    pub note: Option<String>,
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
            Node::Gap { .. } => {}
        }
    }

    // Pass 2: rebuild each rule application from its own evidence.
    for (id, node) in d.nodes.iter().enumerate() {
        let Node::RuleApplication {
            rule,
            conclusion,
            premises,
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
            if !match_fact(&r.open_premise(i), actual, &mut binding) {
                return Err(format!(
                    "节点 {id}：规则 `{rule}` 的第 {} 个前提是 `{}`，而引用的节点 {p} 证成的是 `{}`",
                    i + 1,
                    print_expr(&close_pattern(&r.open_premise(i), &binding)),
                    print_expr(actual)
                ));
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
    d: &Derivation,
    priority_order: &PriorityOrder,
) -> Result<std_deduce_cert::Certificate, String> {
    let mut assumptions = Vec::new();
    let mut nodes = Vec::with_capacity(d.nodes.len());
    let mut open_obligations = Vec::new();

    for (id, node) in d.nodes.iter().enumerate() {
        match node {
            Node::Assumption {
                prop,
                sources,
                label,
            } => {
                let assumption = assumptions.len();
                assumptions.push(std_deduce_cert::Assumption {
                    proposition: cert_expr(prop, Some(id), "假设命题")?,
                    sources: sources.iter().map(std_deduce_cert::Source::from).collect(),
                    label: label.clone(),
                });
                nodes.push(std_deduce_cert::Node::Assumption { assumption });
            }
            Node::RuleApplication {
                rule,
                conclusion,
                premises,
                bindings,
                sources,
                ..
            } => {
                let mut converted = Vec::with_capacity(bindings.len());
                for (parameter, value) in bindings {
                    converted.push(std_deduce_cert::Binding {
                        parameter: parameter.to_string(),
                        value: cert_expr(value, Some(id), &format!("参数 `{parameter}` 的绑定值"))?,
                    });
                }
                nodes.push(std_deduce_cert::Node::RuleApplication {
                    rule: rule.to_string(),
                    conclusion: cert_expr(conclusion, Some(id), "结论")?,
                    premises: premises.clone(),
                    bindings: converted,
                    sources: sources.iter().map(std_deduce_cert::Source::from).collect(),
                });
            }
            Node::Gap {
                prop,
                candidates,
                note,
            } => {
                let mut converted = Vec::with_capacity(candidates.len());
                for candidate in candidates {
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
                    converted.push(std_deduce_cert::GapCandidate {
                        rule: candidate.rule.to_string(),
                        missing,
                        blocked_by,
                        sources: candidate
                            .sources
                            .iter()
                            .map(std_deduce_cert::Source::from)
                            .collect(),
                    });
                }
                nodes.push(std_deduce_cert::Node::Gap {
                    proposition: cert_expr(prop, Some(id), "缺口命题")?,
                    candidates: converted,
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

    let conflicts = d
        .conflicts
        .iter()
        .enumerate()
        .map(|(i, conflict)| {
            Ok(std_deduce_cert::Conflict {
                left: cert_expr(&conflict.left, None, &format!("冲突 {} 的左命题", i + 1))?,
                right: cert_expr(&conflict.right, None, &format!("冲突 {} 的右命题", i + 1))?,
                left_by: cert_provenance(&conflict.left_by),
                right_by: cert_provenance(&conflict.right_by),
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
                "两侧都是已知事实，严格事实之间没有先后".to_owned()
            }
            UnresolvedReason::UnknownWitnesses => {
                "有一方的规则见证已无法重建，无法核对优先关系".to_owned()
            }
            UnresolvedReason::NoPriority => "没有声明任何优先关系".to_owned(),
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

    Ok(std_deduce_cert::Certificate {
        format_version: std_deduce_cert::FormatVersion::CURRENT,
        // The reasoner knows nothing about profiles, pack versions or corpus
        // files; the CLI stamps the real identity before exporting. The marker
        // cannot be serialized, so this certificate can never reach disk.
        environment: std_deduce_cert::EnvironmentIdentity::Unrecorded,
        assumptions,
        nodes,
        root: d.root,
        conflicts,
        open_obligations,
        metadata: std_deduce_cert::Metadata {
            generated_at: None,
            tool: Some("std-deduce".to_owned()),
            tool_version: Some(env!("CARGO_PKG_VERSION").to_owned()),
        },
    })
}

/// Encode one kernel expression, naming its location on failure.
fn cert_expr(expr: &Expr, node: Option<usize>, role: &str) -> Result<CertExpr, String> {
    CertExpr::try_from(expr).map_err(|error| match node {
        Some(id) => format!("节点 {id} 的{role}无法转换为证书表达式：{error}"),
        None => format!("{role}无法转换为证书表达式：{error}"),
    })
}

fn cert_provenance(provenance: &Provenance) -> std_deduce_cert::Provenance {
    match provenance {
        Provenance::Assumption => std_deduce_cert::Provenance::Assumption,
        Provenance::Rules(rules) => std_deduce_cert::Provenance::Rules {
            rules: rules.iter().map(ToString::to_string).collect(),
        },
    }
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
                &Provenance::Rules(empty.clone()),
                &Provenance::Rules(present.clone())
            ),
            Resolution::Unresolved {
                reason: UnresolvedReason::UnknownWitnesses,
            }
        );
        assert_eq!(
            reasoner.resolve(&Provenance::Rules(present), &Provenance::Rules(empty)),
            Resolution::Unresolved {
                reason: UnresolvedReason::UnknownWitnesses,
            }
        );
    }
}
