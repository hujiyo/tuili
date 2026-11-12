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
//! ## Three commitments
//!
//! 1. **No negation as failure.** A rule fires only when every premise has
//!    been derived, and an `unless P` blocks only when `P` *itself* has been
//!    derived. "We could not prove it, so it is false" is impossible here.
//! 2. **No silent conflict resolution.** Contradictory conclusions are
//!    recorded with how, if at all, they were settled.
//! 3. **No hidden gaps.** An unreachable goal yields a gap node listing the
//!    candidate rules, which premises are missing, and which blocking
//!    conditions already hold. There is no `sorry` equivalent.

use std::collections::{BTreeMap, BTreeSet};

use std_deduce_kernel::env::{DeclKind, Env, RuleDecl, SourceRef};
use std_deduce_kernel::norm::normalize;
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
        instance: Vec<String>,
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

#[derive(Debug, Clone)]
pub struct Conflict {
    pub left: Expr,
    pub right: Expr,
    pub left_rule: Name,
    pub right_rule: Option<Name>,
    pub resolution: Resolution,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolution {
    Defeated { winner: Name, loser: Name },
    Unresolved,
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
    binding_strings: Vec<String>,
}

/// The settled result: the set of facts and a derivation for each.
struct Fixed {
    facts: BTreeMap<String, Expr>,
    nodes: Vec<Node>,
    ids: BTreeMap<String, usize>,
    conflicts: Vec<Conflict>,
}

// ---------------------------------------------------------------- reasoner

pub struct Reasoner<'a> {
    env: &'a Env,
    assumptions: Vec<Assumption>,
    /// rule -> rules it beats (`defeated_by` / `prefer`)
    defeats: BTreeMap<Name, BTreeSet<Name>>,
    fixed: Option<Fixed>,
    max_rounds: usize,
}

impl<'a> Reasoner<'a> {
    pub fn new(env: &'a Env) -> Self {
        let mut defeats: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();
        for decl in env.iter() {
            if let DeclKind::Rule(r) = &decl.kind {
                for loser in r.exceptions.iter().chain(r.prefers.iter()) {
                    defeats
                        .entry(decl.name.clone())
                        .or_default()
                        .insert(loser.clone());
                }
            }
        }
        Reasoner {
            env,
            assumptions: Vec::new(),
            defeats,
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
    /// The operator is applied to the *whole* assumption set on every round
    /// rather than incrementally. This is not an optimisation detail: `unless`
    /// makes it anti-monotone, so a conclusion that was derivable last round
    /// may have to be retracted this round. Copying the previous result
    /// forward (the usual `insert if absent` loop) would pin every conclusion
    /// forever and quietly resurrect blocked ones.
    pub fn saturate(&mut self) -> Result<(), String> {
        let seeds: BTreeMap<String, Expr> = self
            .assumptions
            .iter()
            .map(|a| (self.key_of(&a.prop), a.prop.clone()))
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
            if same_keys(&k, &next) {
                let fixed = self.build_nodes(next)?;
                self.fixed = Some(fixed);
                return Ok(());
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

    /// Build nodes in dependency order: an assumption first, then any rule
    /// application whose premises all already have ids.
    fn build_nodes(&self, facts: BTreeMap<String, Expr>) -> Result<Fixed, String> {
        let mut nodes: Vec<Node> = Vec::new();
        let mut ids: BTreeMap<String, usize> = BTreeMap::new();

        for a in &self.assumptions {
            let id = nodes.len();
            nodes.push(Node::Assumption {
                prop: a.prop.clone(),
                sources: a.sources.clone(),
                label: a.label.clone(),
            });
            ids.insert(self.key_of(&a.prop), id);
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
                    let premises: Vec<usize> = inst
                        .premise_keys
                        .iter()
                        .map(|pk| ids[pk])
                        .collect();
                    nodes.push(Node::RuleApplication {
                        rule,
                        conclusion: inst.conclusion,
                        premises,
                        instance: inst.binding_strings,
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
            conflicts: self.conflicts(),
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
            self.env,
            &mut binding,
            &mut keys,
            &mut out,
            rule.unlesses.len(),
        );
        out
    }

    fn conflicts(&self) -> Vec<Conflict> {
        // Negation is not a connective yet, so contradictory facts cannot be
        // recognised automatically. Recording stays empty rather than
        // pretending. `defeated_by` priorities are exposed through `explain`.
        let _ = &self.defeats;
        Vec::new()
    }

    // ------------------------------------------------------------ queries

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

    /// Why is `goal` unreachable? List candidate rules with what each is
    /// missing and what is blocking it.
    pub fn explain(&self, goal: &Expr) -> GapExplanation {
        let mut candidates = Vec::new();
        let note = if check::check(self.env, &Ctx::new(), goal, &Expr::Sort(0)).is_err() {
            Some("目标不是命题".to_string())
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
                .filter(|u| facts.contains_key(&self.key_of(u)))
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
    env: &Env,
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
            binding_strings: binding
                .iter()
                .map(|(n, v)| format!("{n} ↦ {}", print_expr(v)))
                .collect(),
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
        backtrack(rule, idx + 1, facts, env, binding, keys, out, unless_len);
        keys.pop();
        binding.truncate(before);
    }
}

fn blocked(unlesses: &[Expr], facts: &BTreeMap<String, Expr>, env: &Env) -> bool {
    unlesses.iter().any(|u| facts.contains_key(&key(env, u)))
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
        Expr::Pi { name, domain, codomain } => Expr::Pi {
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
/// matter where the blocker sits.
pub fn verify(env: &Env, d: &Derivation) -> Result<(), String> {
    // Pass 1: every node must be well-formed on its own, and we collect the
    // propositions proved anywhere in the tree for the `unless` check below.
    let mut proved: BTreeSet<String> = BTreeSet::new();
    for (id, node) in d.nodes.iter().enumerate() {
        match node {
            Node::Assumption { prop, .. } => {
                check::check(env, &Ctx::new(), prop, &Expr::Sort(0))
                    .map_err(|e| format!("节点 {id}：假设不是命题：{e}"))?;
                proved.insert(key(env, prop));
            }
            Node::RuleApplication { conclusion, .. } => {
                check::check(env, &Ctx::new(), conclusion, &Expr::Sort(0))
                    .map_err(|e| format!("节点 {id}：结论不是命题：{e}"))?;
                proved.insert(key(env, conclusion));
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
            let actual = node_prop(&d.nodes[*p]).ok_or_else(|| {
                format!("节点 {id}：前提 {p} 是未闭合的缺口，不能充当前提")
            })?;
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
        // been retracted.
        for u in &r.unlesses {
            let closed = close_pattern(&r.open_unless_text(u), &binding);
            if proved.contains(&key(env, &closed)) {
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

// ---------------------------------------------------------------- render

pub fn render(_env: &Env, d: &Derivation) -> String {
    let mut out = String::new();
    if let Some(root) = d.root {
        render_node(d, root, 0, &mut out);
        return out;
    }
    // No root: print every node not used as a premise elsewhere.
    let mut used = BTreeSet::new();
    for n in &d.nodes {
        if let Node::RuleApplication { premises, .. } = n {
            used.extend(premises.iter().copied());
        }
    }
    let mut roots = Vec::new();
    for (id, n) in d.nodes.iter().enumerate() {
        match n {
            Node::Assumption { .. } | Node::RuleApplication { .. } => {
                if !used.contains(&id) {
                    roots.push(id);
                }
            }
            Node::Gap { .. } => roots.push(id),
        }
    }
    for (i, id) in roots.into_iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        render_node(d, id, 0, &mut out);
    }
    out
}

fn render_node(d: &Derivation, id: usize, depth: usize, out: &mut String) {
    let pad = "  ".repeat(depth);
    match &d.nodes[id] {
        Node::Assumption {
            prop,
            sources,
            label,
        } => {
            out.push_str(&format!("{pad}· {}", print_expr(prop)));
            if let Some(l) = label {
                out.push_str(&format!("  [{l}]"));
            }
            if let Some(s) = sources.first() {
                out.push_str(&format!("  ← {}", s.one_line()));
            }
            out.push('\n');
        }
        Node::RuleApplication {
            rule,
            conclusion,
            premises,
            instance,
            sources,
        } => {
            out.push_str(&format!("{pad}▸ {}", print_expr(conclusion)));
            out.push_str(&format!("  ⟨{rule}⟩"));
            if let Some(s) = sources.first() {
                out.push_str(&format!(" ← {}", s.one_line()));
            }
            out.push('\n');
            if let Some(s) = sources.first() {
                if !s.note.is_empty() {
                    out.push_str(&format!("{pad}  注：{}\n", s.note));
                }
            }
            if !instance.is_empty() {
                out.push_str(&format!("{pad}  实例：{}\n", instance.join("，")));
            }
            for p in premises {
                render_node(d, *p, depth + 1, out);
            }
        }
        Node::Gap {
            prop,
            candidates,
            note,
        } => {
            out.push_str(&format!("{pad}? {}  【未闭合】\n", print_expr(prop)));
            if let Some(n) = note {
                out.push_str(&format!("{pad}  {n}\n"));
            }
            for c in candidates {
                out.push_str(&format!("{pad}  候选 ⟨{}⟩", c.rule));
                if let Some(s) = c.sources.first() {
                    out.push_str(&format!(" ← {}", s.one_line()));
                }
                out.push('\n');
                if !c.missing.is_empty() {
                    out.push_str(&format!(
                        "{pad}    缺：{}\n",
                        c.missing.iter().map(print_expr).collect::<Vec<_>>().join("；")
                    ));
                }
                for b in &c.blocked_by {
                    out.push_str(&format!("{pad}    被阻断：「{}」已成立\n", print_expr(b)));
                }
            }
        }
    }
}
