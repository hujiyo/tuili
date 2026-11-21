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
//! is resolved in exactly two ways:
//!
//! * an explicit `defeated_by` / `prefer` beats the other side, or one side is
//!   an assumption (facts are strict and outrank defeasible conclusions);
//! * otherwise the conflict is unresolved, and **neither** conclusion enters
//!   the fact base. It is not silently dropped: `conflicts()` reports it, and
//!   the CLI prints both derivations and exits non-zero.
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
use std_deduce_kernel::env::{DeclKind, Env, RuleDecl, SourceRef};
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolution {
    Defeated { winner: Side },
    Unresolved,
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
    /// rule -> rules it beats (`defeated_by` / `prefer`)
    defeats: BTreeMap<Name, BTreeSet<Name>>,
    /// symmetric contradiction relation, closed from `contrary` declarations
    contraries: BTreeMap<Name, BTreeSet<Name>>,
    /// predicate -> argument positions declared single-valued (`unique`)
    uniques: BTreeMap<Name, BTreeSet<usize>>,
    fixed: Option<Fixed>,
    max_rounds: usize,
}

impl<'a> Reasoner<'a> {
    pub fn new(env: &'a Env) -> Self {
        let mut defeats: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();
        for decl in env.iter() {
            if let DeclKind::Rule(r) = &decl.kind {
                // `defeated_by X` means X beats this rule, so the edge points
                // from X to this one. `prefer X` means this rule beats X.
                for beater in &r.exceptions {
                    defeats
                        .entry(beater.clone())
                        .or_default()
                        .insert(decl.name.clone());
                }
                for loser in &r.prefers {
                    defeats
                        .entry(decl.name.clone())
                        .or_default()
                        .insert(loser.clone());
                }
            }
        }
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
            defeats,
            contraries,
            uniques,
            fixed: None,
            max_rounds: 256,
        }
    }

    /// Register an assumption. Its type must be a proposition.
    pub fn assume(
        &mut self,
        prop: &Expr,
        sources: Vec<SourceRef>,
        label: Option<String>,
    ) -> Result<(), String> {
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
        for decl in self.env.iter() {
            if !matches!(decl.kind, DeclKind::Axiom) {
                continue;
            }
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
                    Resolution::Unresolved => {
                        next_removed.insert(self.key_of(&c.left));
                        next_removed.insert(self.key_of(&c.right));
                    }
                    Resolution::Defeated { winner } => {
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
        self.env
            .rules()
            .iter()
            .filter_map(|d| match &d.kind {
                DeclKind::Rule(r) => Some((d.name.clone(), (**r).clone())),
                _ => None,
            })
            .collect()
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
    /// rules, a side wins only when it beats every rule on the other side and
    /// is not out-beaten in return; anything else is unresolved.
    fn resolve(&self, left: &Provenance, right: &Provenance) -> Resolution {
        match (left, right) {
            (Provenance::Assumption, Provenance::Assumption) => Resolution::Unresolved,
            (Provenance::Assumption, _) => Resolution::Defeated { winner: Side::Left },
            (_, Provenance::Assumption) => Resolution::Defeated {
                winner: Side::Right,
            },
            (Provenance::Rules(l), Provenance::Rules(r)) => {
                let beats = |a: &[Name], b: &[Name]| {
                    !a.is_empty()
                        && b.iter().all(|loser| {
                            a.iter().any(|winner| {
                                self.defeats
                                    .get(winner)
                                    .is_some_and(|set| set.contains(loser))
                            })
                        })
                };
                match (beats(l, r), beats(r, l)) {
                    (true, false) => Resolution::Defeated { winner: Side::Left },
                    (false, true) => Resolution::Defeated {
                        winner: Side::Right,
                    },
                    _ => Resolution::Unresolved,
                }
            }
        }
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
            if !facts.contains_key(&k) {
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

        for decl in self.env.rules() {
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
/// the node or propositions they are about, and their description is the
/// existing note or proposition text. No source, subject or object is
/// invented for them. A generation timestamp stays empty.
///
/// Every kernel expression goes through [`std_deduce_cert::CertExpr::try_from`].
/// An expression that cannot be represented aborts the conversion with an
/// error naming the node and the field, rather than being dropped.
pub fn certificate(d: &Derivation) -> Result<std_deduce_cert::Certificate, String> {
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
        if matches!(conflict.resolution, Resolution::Unresolved) {
            open_obligations.push(std_deduce_cert::OpenObligation {
                id: format!("conflict-{index}"),
                kind: std_deduce_cert::ObligationKind::UnresolvedConflict,
                description: format!(
                    "冲突未决：「{}」与「{}」",
                    print_expr(&conflict.left),
                    print_expr(&conflict.right)
                ),
                nodes: Vec::new(),
            });
        }
    }

    Ok(std_deduce_cert::Certificate {
        format_version: std_deduce_cert::FormatVersion::CURRENT,
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
        Resolution::Defeated { winner } => std_deduce_cert::Resolution::Defeated {
            winner: match winner {
                Side::Left => std_deduce_cert::Side::Left,
                Side::Right => std_deduce_cert::Side::Right,
            },
        },
        Resolution::Unresolved => std_deduce_cert::Resolution::Unresolved,
    }
}
