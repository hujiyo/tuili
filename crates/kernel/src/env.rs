//! The environment: the declaration ledger and the local context.
//!
//! The environment is an append-only ledger. A name collision is an error,
//! never a silent overwrite, and every declaration *may* carry provenance.
//! A legal derivation is worthless without knowing which version of which
//! article it used, so provenance is a first-class field rather than a comment.

use std::collections::{BTreeMap, BTreeSet};

use crate::check;
use crate::error::{Error, Result};
use crate::term::{Expr, Name};

/// Where a declaration comes from.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SourceRef {
    /// The file or law name, for example `中华人民共和国宪法`.
    pub text: String,
    /// The article or section within `text`, for example `第三十九条`.
    pub locator: String,
    pub version: String,
    pub effective: Option<String>,
    /// Why we formalised the article this way, when that is not obvious.
    pub note: String,
    /// The quoted wording of the provision. `text` is the instrument name;
    /// this is the article's text.
    pub quote: String,
    pub url: String,
    pub jurisdiction: String,
    pub retrieved_at: String,
    pub hash: String,
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
    pub fn with_quote(mut self, v: impl Into<String>) -> Self {
        self.quote = v.into();
        self
    }
    pub fn with_url(mut self, v: impl Into<String>) -> Self {
        self.url = v.into();
        self
    }
    pub fn with_jurisdiction(mut self, v: impl Into<String>) -> Self {
        self.jurisdiction = v.into();
        self
    }
    pub fn with_retrieved_at(mut self, v: impl Into<String>) -> Self {
        self.retrieved_at = v.into();
        self
    }
    pub fn with_hash(mut self, v: impl Into<String>) -> Self {
        self.hash = v.into();
        self
    }
    /// The citation in one line: `「<text><locator>」`, followed by
    /// `（<version>）` when a version is recorded. Control characters are
    /// escaped, so the result is always exactly one line.
    pub fn one_line(&self) -> String {
        let mut s = format!(
            "「{}{}」",
            escape_control(&self.text),
            escape_control(&self.locator)
        );
        if !self.version.is_empty() {
            s.push_str(&format!("（{}）", escape_control(&self.version)));
        }
        s
    }

    /// Every non-empty field on its own line, with control characters
    /// escaped. Empty optional fields are omitted rather than printed blank.
    pub fn full(&self) -> String {
        let mut lines = Vec::new();
        for (label, value) in [
            ("文本", self.text.as_str()),
            ("条号", self.locator.as_str()),
            ("版本", self.version.as_str()),
            ("生效", self.effective.as_deref().unwrap_or("")),
            ("引文", self.quote.as_str()),
            ("链接", self.url.as_str()),
            ("管辖", self.jurisdiction.as_str()),
            ("抓取时间", self.retrieved_at.as_str()),
            ("哈希", self.hash.as_str()),
            ("备注", self.note.as_str()),
        ] {
            if !value.is_empty() {
                lines.push(format!("{label}：{}", escape_control(value)));
            }
        }
        lines.join("\n")
    }
}

/// Escape control characters so a source field cannot inject another output
/// line or a terminal control sequence. Newline, carriage return and tab get
/// their short forms; every other control character becomes `\u{XXXX}`.
fn escape_control(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for ch in value.chars() {
        match ch {
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            ch if ch.is_control() => {
                escaped.push_str(&format!("\\u{{{:04X}}}", ch as u32));
            }
            ch => escaped.push(ch),
        }
    }
    escaped
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
    /// Two predicates whose facts cannot both hold: any pair with these heads
    /// and identical arguments is a conflict. Declared, never guessed, because
    /// a legal system cannot read Chinese and decide on its own that 「该批准」
    /// and 「不该批准」 are opposites.
    Contrary { left: Name, right: Name },
    /// A predicate that can hold of only one value at argument `index`
    /// (zero-based): two facts with the same head that differ at `index` and
    /// agree everywhere else are a conflict. `unique 应适用 1` says one case
    /// can have only one applicable norm.
    Unique { pred: Name, index: usize },
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
    /// ending in the conclusion, so the constant can be applied to its
    /// arguments to prove that conclusion.
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
    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
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

    /// The declared contrary pairs, as written. The relation is symmetric;
    /// the reasoner closes it.
    pub fn contrary_pairs(&self) -> Vec<(Name, Name)> {
        self.iter()
            .filter_map(|d| match &d.kind {
                DeclKind::Contrary { left, right } => Some((left.clone(), right.clone())),
                _ => None,
            })
            .collect()
    }

    /// Declared single-valued argument positions, as `(predicate, index)`.
    pub fn unique_positions(&self) -> Vec<(Name, usize)> {
        self.iter()
            .filter_map(|d| match &d.kind {
                DeclKind::Unique { pred, index } => Some((pred.clone(), *index)),
                _ => None,
            })
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
/// conclusion. Applying the constant to a parameter and a proof of every
/// premise therefore yields a proof of the conclusion.
///
/// Premise types are written relative to the telescope prefix, and later
/// premises may mention earlier named ones. The conclusion is checked in the
/// *full* telescope, which is what makes dependency between premises usable.
pub fn rule_type(rule: &RuleDecl) -> Expr {
    let params = rule.telescope();
    telescope(&params, rule.conclusion.clone())
}

/// Refuse a telescope whose binder names are not pairwise distinct.
///
/// Opening a rule replaces each telescope binder by the constant `?<binder>`
/// (see `open_vars`), so two binders with the same name become one constant:
/// a premise proof could be taken for a parameter value, or the other way
/// round. The collision is reported instead of silently renamed, because only
/// the author knows which binding the rule meant.
pub fn check_unique_binders(binders: &[Name]) -> Result<()> {
    let mut seen = BTreeSet::new();
    for binder in binders {
        if !seen.insert(binder) {
            return Err(Error::other(format!(
                "参数/前提 binder `{binder}` 重名：重名会让推理器把不同的绑定打开成同一个 \
                 `?{binder}` 常量，从而把前提证明当成参数值（或反过来）。必须改名。"
            )));
        }
    }
    Ok(())
}

impl RuleDecl {
    /// All binders of the rule: params, then premises. `unless` conditions
    /// are not binders, so they are not listed here.
    pub fn telescope(&self) -> Vec<(Name, Expr)> {
        let mut out = self.params.clone();
        for (i, (n, ty)) in self.premises.iter().enumerate() {
            let n = n
                .clone()
                .unwrap_or_else(|| crate::term::name(format!("_p{i}")));
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
        // A binder name must be unique across params and premises. Opening
        // the rule replaces every binder by the constant `?<binder>`, so two
        // different bindings with the same name become the same constant: a
        // premise proof could be taken for a parameter value, or the other
        // way round. Renaming silently would hide which binding the source
        // meant, so it is refused before anything else.
        check_unique_binders(&self.binder_names())?;
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

        // Every parameter must be fixed by a premise at instantiation time.
        // If one appears in the conclusion or in an `unless` condition but in
        // no premise, the reasoner would leave it as a `?name` constant, so
        // the conclusion or the blocker never closes, and a certificate could
        // invent a binding to dodge the blocker. If it appears nowhere at all,
        // the reasoner never binds it, while the certificate checker demands a
        // binding for every parameter: the two disagree about what a complete
        // instance is. Both are silent holes, so they are refused at load time.
        for (binder, _) in &self.params {
            let in_premise =
                (0..self.premises.len()).any(|i| mentions_pattern(&self.open_premise(i), binder));
            if in_premise {
                continue;
            }
            let in_conclusion = mentions_pattern(&self.open_conclusion(), binder);
            let in_unless = self
                .unlesses
                .iter()
                .any(|u| mentions_pattern(&self.open_unless_text(u), binder));
            if in_conclusion || in_unless {
                return Err(Error::other(format!(
                    "参数 `{binder}` 出现在结论或 unless 阻断条件里，但没有出现在任何前提里：\
                     实例化时它无法被确定，结论或阻断条件不会闭合。\
                     请把它纳入某条前提，或把它从结论/unless 里去掉。"
                )));
            }
            return Err(Error::other(format!(
                "参数 `{binder}` 没有出现在任何前提里，也没有出现在结论或 unless 里：\
                 它是一个无法被实例化的空参数。请把它纳入某条前提，或删掉这个参数。"
            )));
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
        Expr::Lam { name, domain, body } => Expr::Lam {
            name: name.clone(),
            domain: Box::new(open_vars(domain, names, depth, in_scope)),
            body: Box::new(open_vars(body, names, depth + 1, in_scope)),
        },
        Expr::App { func, arg } => Expr::App {
            func: Box::new(open_vars(func, names, depth, in_scope)),
            arg: Box::new(open_vars(arg, names, depth, in_scope)),
        },
        Expr::Let { name, value, body } => Expr::Let {
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
            Expr::Pi {
                domain, codomain, ..
            } => mentions_pattern(domain, binder) || mentions_pattern(codomain, binder),
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
