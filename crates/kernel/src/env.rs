//! The environment: the declaration ledger and the local context.
//!
//! The environment is an append-only ledger. A name collision is an error,
//! never a silent overwrite, and every declaration *may* carry provenance.
//! A legal derivation is worthless without knowing which version of which
//! article it used, so provenance is a first-class field rather than a comment.

use std::collections::BTreeMap;

use crate::check;
use crate::error::{Error, Result};
use crate::term::{Expr, Name};

/// Where a declaration comes from.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SourceRef {
    pub text: String,
    pub locator: String,
    pub version: String,
    pub effective: Option<String>,
    /// Why we formalised the article this way, when that is not obvious.
    pub note: String,
}

impl SourceRef {
    pub fn new(text: impl Into<String>, locator: impl Into<String>) -> Self {
        SourceRef {
            text: text.into(),
            locator: locator.into(),
            ..Default::default()
        }
    }
    pub fn with_version(mut self, v: impl Into<String>) -> Self {
        self.version = v.into();
        self
    }
    pub fn with_effective(mut self, v: impl Into<String>) -> Self {
        self.effective = Some(v.into());
        self
    }
    pub fn one_line(&self) -> String {
        let mut s = format!("「{}{}」", self.text, self.locator);
        if !self.version.is_empty() {
            s.push_str(&format!("（{}）", self.version));
        }
        s
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum DeclKind {
    /// A new sort: `sort 公民`.
    Sort,
    /// A predicate symbol: `pred 侵害 : 公民 → 行为 → Prop`.
    Pred,
    /// A bare assumption: `axiom 条款 : ...`.
    Axiom,
    /// An individual constant: `obj 张三 : 公民`.
    Obj,
    /// `def ... := ...`; unfolds during conversion.
    Def { body: Expr },
    /// A rule; opaque under conversion, driving the reasoner instead.
    Rule(Box<RuleDecl>),
    /// A marked interpretation: it turns a premise into another premise.
    Interpretation(Box<Interpretation>),
}

/// A defeasible rule.
#[derive(Debug, Clone, PartialEq)]
pub struct RuleDecl {
    pub params: Vec<(Name, Expr)>,
    pub premises: Vec<(Option<Name>, Expr)>,
    pub conclusion: Expr,
    /// Conditions whose truth *blocks* the rule (the `unless` clauses).
    /// These are part of the telescope, so they may mention any parameter.
    pub unlesses: Vec<Expr>,
    /// Rules that defeat this one.
    pub exceptions: Vec<Name>,
    /// Rules this one outranks, declared with `prefer R`. The reverse of
    /// `exceptions`, kept separately so the source of a priority is visible:
    /// `defeated_by` means "I lose to X", `prefer` means "I beat Y".
    pub prefers: Vec<Name>,
    pub sources: Vec<SourceRef>,
}

/// An interpretation before/after pair, with an explicit identity.
///
/// The point of making this a named object is auditability: a derivation can
/// cite which interpretation it applied, and another can cite a competing one.
#[derive(Debug, Clone, PartialEq)]
pub struct Interpretation {
    pub name: Name,
    pub from: Expr,
    pub to: Expr,
    pub sources: Vec<SourceRef>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Decl {
    pub name: Name,
    pub kind: DeclKind,
    /// Declared type. For `Rule`, the telescope over params and premises
    /// ending in the conclusion's sort.
    pub ty: Expr,
    pub sources: Vec<SourceRef>,
    /// Position in the ledger, assigned on insertion.
    pub index: u64,
}

/// The local context: a telescope. Each stored type is written in its own
/// prefix context, so a variable's type from depth `n` is lifted by `i`.
#[derive(Debug, Clone, Default)]
pub struct Ctx {
    bindings: Vec<(Option<Name>, Expr)>,
}

impl Ctx {
    pub fn new() -> Self {
        Ctx::default()
    }
    pub fn len(&self) -> usize {
        self.bindings.len()
    }
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
    pub fn push(&mut self, n: Option<Name>, ty: Expr) {
        self.bindings.push((n, ty));
    }
    pub fn type_of(&self, i: usize) -> Result<Expr> {
        let n = self.bindings.len();
        if i >= n {
            return Err(Error::OutOfScope { index: i, bound: n });
        }
        let (_, ty) = &self.bindings[n - 1 - i];
        Ok(crate::term::shift(ty, i as isize, 0))
    }
    pub fn names(&self) -> impl Iterator<Item = &Option<Name>> {
        self.bindings.iter().map(|(n, _)| n)
    }
}

/// The declaration store.
#[derive(Debug, Clone, Default)]
pub struct Env {
    decls: BTreeMap<Name, Decl>,
    order: Vec<Name>,
    next_index: u64,
}

impl Env {
    pub fn new() -> Self {
        Env::default()
    }
    pub fn get(&self, n: &str) -> Option<&Decl> {
        self.decls.get(n)
    }
    pub fn contains(&self, n: &str) -> bool {
        self.decls.contains_key(n)
    }
    pub fn iter(&self) -> impl Iterator<Item = &Decl> {
        self.order.iter().filter_map(|n| self.decls.get(n))
    }
    pub fn decls_ordered(&self) -> &[Name] {
        &self.order
    }
    pub fn len(&self) -> usize {
        self.decls.len()
    }

    /// Add a declaration. The type is checked to live in a sort, so a typo
    /// in a predicate signature cannot enter the ledger.
    pub fn insert(&mut self, mut decl: Decl, ctx: &Ctx) -> Result<Name> {
        if self.decls.contains_key(&decl.name) {
            return Err(Error::DuplicateName(decl.name.to_string()));
        }
        let ty_ty = check::infer(self, ctx, &decl.ty)?;
        match &ty_ty {
            Expr::Sort(_) => {}
            other => return Err(Error::NotASort(other.clone())),
        }
        if let DeclKind::Def { body } = &decl.kind {
            check::check(self, ctx, body, &decl.ty)?;
        }
        if let DeclKind::Rule(rule) = &decl.kind {
            rule.check(self, &Expr::Sort(0))?;
        }
        decl.index = self.next_index;
        self.next_index += 1;
        self.order.push(decl.name.clone());
        let name = decl.name.clone();
        self.decls.insert(name.clone(), decl);
        Ok(name)
    }

    pub fn rules(&self) -> Vec<&Decl> {
        self.iter()
            .filter(|d| matches!(d.kind, DeclKind::Rule(_)))
            .collect()
    }
    pub fn interpretations(&self) -> Vec<&Decl> {
        self.iter()
            .filter(|d| matches!(d.kind, DeclKind::Interpretation(_)))
            .collect()
    }
}

/// Build `∀ (p1 : t1) ... (pn : tn), body` from a telescope, outermost first.
pub fn telescope(params: &[(Name, Expr)], body: Expr) -> Expr {
    params
        .iter()
        .rev()
        .fold(body, |acc, (n, ty)| Expr::forall(n, ty.clone(), acc))
}

/// A rule's declared type: telescope over params and premises, ending in the
/// sort of the conclusion.
///
/// Premise types are written relative to the telescope prefix, and later
/// premises may mention earlier named ones. The conclusion is checked in the
/// *full* telescope, which is what makes dependency between premises usable.
pub fn rule_type(rule: &RuleDecl, conclusion_sort: u32) -> Expr {
    let params = rule.telescope();
    telescope(&params, Expr::Sort(conclusion_sort))
}

impl RuleDecl {
    /// All binders of the rule: params, then premises. `unless` conditions
    /// are not binders, so they are not listed here.
    pub fn telescope(&self) -> Vec<(Name, Expr)> {
        let mut out = self.params.clone();
        for (i, (n, ty)) in self.premises.iter().enumerate() {
            let n = n.clone().unwrap_or_else(|| crate::term::name(format!("_p{i}")));
            out.push((n, ty.clone()));
        }
        out
    }

    /// Names of the telescope binders, outermost first.
    pub fn binder_names(&self) -> Vec<Name> {
        self.telescope().into_iter().map(|(n, _)| n).collect()
    }

    /// Check a rule's internal consistency: every premise, every `unless`
    /// condition and the conclusion must be well-typed in the rule's
    /// telescope, and the conclusion must be a proposition.
    ///
    /// Scoping, which is the subtle part: premise `i` is written in the scope
    /// of *the params and the premises before it*, not of all premises. The
    /// conclusion is written in the scope of the whole telescope. Getting
    /// this wrong silently reinterprets de Bruijn indices, so it is spelled
    /// out step by step.
    pub fn check(&self, env: &Env, conclusion_ty: &Expr) -> Result<()> {
        let mut ctx = Ctx::new();
        for (i, (n, ty)) in self.params.iter().enumerate() {
            check::check_is_type(env, &ctx, ty)
                .map_err(|e| Error::other(format!("规则第 {} 个参数无法成立：{e}", i + 1)))?;
            // The stored type is relative to its own prefix, which is exactly
            // `ctx` before the push.
            ctx.push(Some(n.clone()), ty.clone());
        }
        for (i, (n, p)) in self.premises.iter().enumerate() {
            check::check_is_type(env, &ctx, p)
                .map_err(|e| Error::other(format!("前提 {} 不成立：{e}", i + 1)))?;
            let bind = n
                .clone()
                .unwrap_or_else(|| crate::term::name(format!("_p{i}")));
            ctx.push(Some(bind), p.clone());
        }
        for (i, u) in self.unlesses.iter().enumerate() {
            check::check(env, &ctx, u, &Expr::Sort(0))
                .map_err(|e| Error::other(format!("unless {} 不是命题：{e}", i + 1)))?;
        }
        let t = check::infer(env, &ctx, &self.conclusion)
            .map_err(|e| Error::other(format!("结论不成立：{e}")))?;
        if !crate::conv::convertible(env, &ctx, &t, conclusion_ty)? {
            return Err(Error::TypeMismatch {
                expected: conclusion_ty.clone(),
                actual: t,
            });
        }

        // A parameter that appears in the conclusion but in no premise cannot
        // be fixed at instantiation time: the reasoner would leave it as a
        // `?name` constant, producing a conclusion that is not closed. That
        // is a silent hole, so it is refused at load time instead.
        for (binder, _) in &self.params {
            let in_conclusion = mentions_pattern(&self.open_conclusion(), binder);
            if !in_conclusion {
                continue;
            }
            let in_premise = (0..self.premises.len())
                .any(|i| mentions_pattern(&self.open_premise(i), binder));
            if !in_premise {
                return Err(Error::other(format!(
                    "参数 `{binder}` 出现在结论里，但没有出现在任何前提里：\
                     实例化时它无法被确定，结论不会闭合。\
                     请把它纳入某条前提，或把它从结论里去掉。"
                )));
            }
        }
        Ok(())
    }

    /// Open a term of the rule telescope into a *pattern*: every bound
    /// variable is replaced by a constant named `?<binder>`. The reasoner
    /// matches grounded facts against these patterns, and the kernel never
    /// sees them, so no soundness claim rests on this translation.
    fn open(&self, e: &Expr, in_scope: usize) -> Expr {
        let names = self.binder_names();
        open_vars(e, &names, 0, in_scope)
    }

    pub fn open_param_type(&self, i: usize) -> Expr {
        self.open(&self.params[i].1, i)
    }

    pub fn open_premise(&self, i: usize) -> Expr {
        self.open(&self.premises[i].1, self.params.len() + i)
    }

    pub fn open_conclusion(&self) -> Expr {
        self.open(&self.conclusion, self.params.len() + self.premises.len())
    }

    pub fn open_unless(&self, i: usize) -> Expr {
        self.open(&self.unlesses[i], self.params.len() + self.premises.len())
    }

    /// Open an [`unless`] expression that has already been unpacked.
    pub fn open_unless_text(&self, e: &Expr) -> Expr {
        self.open(e, self.params.len() + self.premises.len())
    }
}

/// Replace free de Bruijn variables with `?name` constants.
fn open_vars(e: &Expr, names: &[Name], depth: usize, in_scope: usize) -> Expr {
    match e {
        Expr::Var(j) => {
            // `j - depth` is the index relative to the in-scope telescope.
            if *j < depth {
                Expr::Var(*j)
            } else {
                let rel = *j - depth;
                if rel < in_scope && in_scope <= names.len() {
                    // The innermost visible binder is `names[in_scope-1]`.
                    let binder = in_scope - 1 - rel;
                    Expr::constant(format!("?{}", names[binder]))
                } else {
                    Expr::Var(*j)
                }
            }
        }
        Expr::Sort(_) | Expr::Const(_) => e.clone(),
        Expr::Pi {
            name,
            domain,
            codomain,
        } => Expr::Pi {
            name: name.clone(),
            domain: Box::new(open_vars(domain, names, depth, in_scope)),
            codomain: Box::new(open_vars(codomain, names, depth + 1, in_scope)),
        },
        Expr::Lam {
            name,
            domain,
            body,
        } => Expr::Lam {
            name: name.clone(),
            domain: Box::new(open_vars(domain, names, depth, in_scope)),
            body: Box::new(open_vars(body, names, depth + 1, in_scope)),
        },
        Expr::App { func, arg } => Expr::App {
            func: Box::new(open_vars(func, names, depth, in_scope)),
            arg: Box::new(open_vars(arg, names, depth, in_scope)),
        },
        Expr::Let {
            name,
            value,
            body,
        } => Expr::Let {
            name: name.clone(),
            value: Box::new(open_vars(value, names, depth, in_scope)),
            body: Box::new(open_vars(body, names, depth + 1, in_scope)),
        },
    }
}

/// Is this a pattern variable, i.e. a constant produced by `open`?
pub fn is_pattern_var(e: &Expr) -> Option<&str> {
    match e {
        Expr::Const(n) => n.strip_prefix('?'),
        _ => None,
    }
}

/// Does an opened expression mention the pattern constant `?binder`?
fn mentions_pattern(e: &Expr, binder: &Name) -> bool {
    match is_pattern_var(e) {
        Some(pv) => pv == binder.as_ref(),
        None => match e {
            Expr::Sort(_) | Expr::Var(_) | Expr::Const(_) => false,
            Expr::Pi { domain, codomain, .. } => {
                mentions_pattern(domain, binder) || mentions_pattern(codomain, binder)
            }
            Expr::Lam { domain, body, .. } => {
                mentions_pattern(domain, binder) || mentions_pattern(body, binder)
            }
            Expr::App { func, arg } => {
                mentions_pattern(func, binder) || mentions_pattern(arg, binder)
            }
            Expr::Let { value, body, .. } => {
                mentions_pattern(value, binder) || mentions_pattern(body, binder)
            }
        },
    }
}
