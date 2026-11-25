//! Theory files: a named unit of declarations.
//!
//! A `Theory` is not a kernel object. It is a *documentation and audit*
//! device: it records that a group of declarations were formalised together,
//! from which source, and by whom. The kernel sees only the flat ledger,
//! which is what keeps the trusted core small.

use std_deduce_kernel::env::{Decl, Env, SourceRef};
use std_deduce_kernel::meta::{validate_date, validate_jurisdiction_code, Scope, ScopeOrigin};
use std_deduce_kernel::{Error, Expr, FactIdentity};

use crate::ast::{Defeater, Item, ScopeSpec, Term};
use crate::elab;
use crate::parser;

#[derive(Debug, Clone, Default)]
pub struct Theory {
    pub name: String,
    /// The explicit namespace declared by the theory's file, if any. A
    /// namespaced theory's `name` is the namespace, not the load path.
    pub namespace: Option<String>,
    /// Declarations made by this theory, in ledger order.
    pub decls: Vec<String>,
    /// Rules among those declarations.
    pub rules: Vec<String>,
    /// Theories this one builds on: the package names it imports, in first
    /// appearance order and without duplicates.
    pub requires: Vec<String>,
}

#[derive(Debug, Clone, Default)]
pub struct Library {
    pub theories: Vec<Theory>,
    pub env: Env,
}

/// How one file is loaded: what scope a rule inherits and whether its rules are
/// case-local extensions.
///
/// The default is a plain file: no pack defaults and no case-local marking.
/// A package loader passes the manifest's scope; the CLI passes
/// `case_local = true` only for a case file in `--closed-env
/// --allow-case-rules`. The kernel still stores the values only; it never uses
/// them to decide applicability.
#[derive(Debug, Clone, Default)]
pub struct LoadOptions {
    /// The containing law pack's manifest scope, inherited field by field by a
    /// rule that does not write that field itself. `origin` is ignored here;
    /// the loader sets [`ScopeOrigin::PackDefault`] when it inherits.
    pub pack_scope: Option<Scope>,
    /// Rules declared by this file are case-local extensions: they never
    /// inherit the pack manifest and are recorded as
    /// [`ScopeOrigin::CaseLocal`].
    pub case_local: bool,
}

impl Library {
    pub fn new() -> Self {
        Library::default()
    }

    pub fn theory(&self, n: &str) -> Option<&Theory> {
        self.theories.iter().find(|t| t.name == n)
    }

    /// Load source text into a theory. Everything is checked as it goes in;
    /// on the first error the library is left unchanged (we work on a clone
    /// and only commit at the end).
    pub fn load(&mut self, name: &str, src: &str) -> Result<LoadReport, LoadError> {
        self.load_with_options(name, src, &LoadOptions::default())
    }

    /// Load source text with an explicit rule-scope context.
    ///
    /// See [`LoadOptions`]. The scope values are validated here, so a bad date
    /// or code is refused with the same rule a manifest or `--as-of` uses; an
    /// inherited manifest scope is validated once per load as well, because a
    /// caller may build the defaults by hand instead of parsing a manifest.
    pub fn load_with_options(
        &mut self,
        name: &str,
        src: &str,
        options: &LoadOptions,
    ) -> Result<LoadReport, LoadError> {
        let items = parser::parse(src).map_err(|e| LoadError::at(e.msg, e.line, e.col))?;
        if let Some(scope) = &options.pack_scope {
            validate_pack_scope(scope).map_err(LoadError::new)?;
        }
        // Imports name packages, not files: every imported namespace must
        // already be in this session. This is checked before any declaration
        // is inserted, so an import failure cannot leave a partial theory.
        let imported = collect_imports(&items);
        for pack in &imported {
            let loaded = self
                .theories
                .iter()
                .any(|t| t.namespace.as_deref() == Some(pack.as_str()));
            if !loaded {
                return Err(LoadError::new(format!(
                    "包 `{pack}` 尚未加载；请通过注册表导入"
                )));
            }
        }
        // The parser guarantees that imports come first and that a
        // `namespace` item, when present, is the first non-import item and
        // appears once. A namespaced file is a module: every declaration name
        // and every reference to a declaration must be qualified. This is
        // checked over the whole file before anything is inserted, so a bad
        // module cannot leave a partial theory behind.
        let namespace = match items.iter().find(|item| !matches!(item, Item::Import(_))) {
            Some(Item::Namespace(ns)) => Some(ns.clone()),
            _ => None,
        };
        if let Some(ns) = namespace.as_deref() {
            check_module_names(ns, &items).map_err(LoadError::new)?;
        } else {
            // A file without a namespace is a case/example file: it may
            // *reference* qualified names from modules, but it must not
            // declare one, or it could squat on a module's name.
            check_case_decl_names(&items).map_err(LoadError::new)?;
        }
        let theory_name = namespace.clone().unwrap_or_else(|| name.to_string());
        if let Some(existing) = self.theories.iter().find(|t| t.name == theory_name) {
            if existing.namespace != namespace {
                return Err(LoadError::new(format!(
                    "理论 `{theory_name}` 已存在，但 namespace 不一致（已有 {}，本次 {}）；\
                         同名理论只有 namespace 相同才能合并",
                    namespace_label(&existing.namespace),
                    namespace_label(&namespace)
                )));
            }
        }
        let mut next = self.clone();
        let mut theory = Theory {
            name: theory_name.clone(),
            namespace: namespace.clone(),
            requires: imported.clone(),
            ..Default::default()
        };
        let mut report = LoadReport {
            imported,
            ..Default::default()
        };
        // The `(winner, loser)` of every top-level priority this file declares,
        // validated against the completed environment after the loop so a
        // priority may name a rule declared later in the same file.
        let mut priorities: Vec<(String, String)> = Vec::new();

        for item in items {
            match item {
                Item::Namespace(_) | Item::Import(_) => {}
                Item::Sort { name: n, source } => {
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Sort,
                        ty: std_deduce_kernel::Expr::Sort(1),
                        sources: source.into_iter().map(to_source).collect(),
                        scope: Scope::default(),
                        occurred_at: None,
                        occurred_in: None,
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError::new(format!("`sort {n}`：{e}")))?;
                    theory.decls.push(n.clone());
                    report.declared.push(n);
                }
                Item::Obj {
                    name: n,
                    ty,
                    source,
                } => {
                    // An individual is an axiom-like constant, but its type
                    // must be a *type* (a sort or a term of a sort), never a
                    // proposition. This catches `obj 张三 : 非法搜查 张三 甲宅`.
                    let ety = elab::elab_top(&next.env, &ty)
                        .map_err(|e| LoadError::new(format!("`obj {n}`：{}", e.msg)))?;
                    std_deduce_kernel::check::check_is_type(
                        &next.env,
                        &std_deduce_kernel::Ctx::new(),
                        &ety,
                    )
                    .map_err(|e| {
                        LoadError::new(format!("`obj {n}` 的类型必须是类型而不是命题：{e}"))
                    })?;
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Obj,
                        ty: ety,
                        sources: source.into_iter().map(to_source).collect(),
                        scope: Scope::default(),
                        occurred_at: None,
                        occurred_in: None,
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError::new(format!("`obj {n}`：{e}")))?;
                    theory.decls.push(n.clone());
                    report.declared.push(n);
                }
                Item::Pred {
                    name: n,
                    ty,
                    source,
                } => {
                    let ety = elab::elab_top(&next.env, &ty)
                        .map_err(|e| LoadError::new(format!("`pred {n}`：{}", e.msg)))?;
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Pred,
                        ty: ety,
                        sources: source.into_iter().map(to_source).collect(),
                        scope: Scope::default(),
                        occurred_at: None,
                        occurred_in: None,
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError::new(format!("`pred {n}`：{e}")))?;
                    theory.decls.push(n.clone());
                    report.declared.push(n);
                }
                Item::Axiom {
                    name: n,
                    ty,
                    source,
                    identity,
                    occurred_at,
                    occurred_in,
                } => {
                    // An asserted fact without provenance is not auditable: it
                    // would enter the fact base as if it had been proved. A
                    // source made only of whitespace names nothing and is not
                    // provenance either. This is checked before elaboration so
                    // a missing source is not masked by an unrelated type
                    // error.
                    if !source.as_ref().is_some_and(usable_source) {
                        return Err(LoadError::new(format!(
                                "axiom `{n}` 缺少 source 或来源为空白；断言事实必须有出处（法律名称 + 条号，或案件材料）"
                            )));
                    }
                    let ety = elab::elab_top(&next.env, &ty)
                        .map_err(|e| LoadError::new(format!("`axiom {n}`：{}", e.msg)))?;
                    // The elaborated type decides what the declaration is. A
                    // proposition is a fact and needs an identity; anything
                    // else only names a constant and must not carry one.
                    let is_proposition = std_deduce_kernel::check::check(
                        &next.env,
                        &std_deduce_kernel::Ctx::new(),
                        &ety,
                        &Expr::Sort(0),
                    )
                    .is_ok();
                    let (kind, occurred_at, occurred_in) = if is_proposition {
                        // A case file (no namespace) states what its user
                        // says; a module states what the package assumes.
                        // `verified` and `stipulated` are never a default:
                        // only an explicit clause may claim them.
                        let identity = identity.unwrap_or(if namespace.is_some() {
                            FactIdentity::Assumed
                        } else {
                            FactIdentity::UserAsserted
                        });
                        // An occurrence record belongs to a fact. The values
                        // are validated here with the same calendar/code rules
                        // as every other surface; nothing defaults them from a
                        // query date, so an unrecorded fact stays `None`.
                        if let Some(date) = &occurred_at {
                            validate_date(&format!("事实 `{n}` 的 occurred_at"), date)
                                .map_err(LoadError::new)?;
                        }
                        if let Some(code) = &occurred_in {
                            validate_jurisdiction_code(&format!("事实 `{n}` 的 occurred_in"), code)
                                .map_err(LoadError::new)?;
                        }
                        (
                            std_deduce_kernel::DeclKind::Fact { identity },
                            occurred_at,
                            occurred_in,
                        )
                    } else {
                        if identity.is_some() {
                            return Err(LoadError::new(format!(
                                "`axiom {n}` 声明的不是命题，不能有事实身份；命题常量请用 `axiom`（不带 identity）"
                            )));
                        }
                        if occurred_at.is_some() || occurred_in.is_some() {
                            return Err(LoadError::new(format!(
                                "`axiom {n}` 声明的不是命题，不能有 occurred_at / occurred_in；发生记录只属于事实（命题断言）"
                            )));
                        }
                        (std_deduce_kernel::DeclKind::Axiom, None, None)
                    };
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind,
                        ty: ety,
                        sources: source.into_iter().map(to_source).collect(),
                        scope: Scope::default(),
                        occurred_at,
                        occurred_in,
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError::new(format!("`axiom {n}`：{e}")))?;
                    theory.decls.push(n.clone());
                    report.declared.push(n);
                }
                Item::Def {
                    name: n,
                    ty,
                    body,
                    source,
                } => {
                    let ety = elab::elab_top(&next.env, &ty)
                        .map_err(|e| LoadError::new(format!("`def {n}`：{}", e.msg)))?;
                    let ebody = elab::elab_top(&next.env, &body)
                        .map_err(|e| LoadError::new(format!("`def {n}`：{}", e.msg)))?;
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Def { body: ebody },
                        ty: ety,
                        sources: source.into_iter().map(to_source).collect(),
                        scope: Scope::default(),
                        occurred_at: None,
                        occurred_in: None,
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError::new(format!("`def {n}`：{e}")))?;
                    theory.decls.push(n.clone());
                    report.declared.push(n);
                }
                Item::Contrary {
                    left,
                    right,
                    source,
                } => {
                    let l = std_deduce_kernel::name(&left);
                    let r = std_deduce_kernel::name(&right);
                    for p in [&l, &r] {
                        match next.env.get(p) {
                            Some(d) if matches!(d.kind, std_deduce_kernel::DeclKind::Pred) => {}
                            Some(_) => {
                                return Err(LoadError::new(format!(
                                    "`contrary {left} {right}`：`{p}` 不是谓词（pred）"
                                )))
                            }
                            None => {
                                return Err(LoadError::new(format!(
                                    "`contrary {left} {right}`：未知谓词 `{p}`"
                                )))
                            }
                        }
                    }
                    let al = pred_arity(&next.env, &l).unwrap_or(0);
                    let ar = pred_arity(&next.env, &r).unwrap_or(0);
                    if al != ar {
                        return Err(LoadError::new(format!(
                            "`contrary {left} {right}`：两个谓词的参数个数不同（{al} vs {ar}）"
                        )));
                    }
                    for (a, b) in next.env.contrary_pairs() {
                        if (a == l && b == r) || (a == r && b == l) {
                            return Err(LoadError::new(format!(
                                "`contrary {left} {right}`：这一对已经声明过了"
                            )));
                        }
                    }
                    let decl = Decl {
                        name: std_deduce_kernel::name(format!("contrary:{left}:{right}")),
                        kind: std_deduce_kernel::DeclKind::Contrary { left: l, right: r },
                        ty: Expr::Sort(0),
                        sources: source.into_iter().map(to_source).collect(),
                        scope: Scope::default(),
                        occurred_at: None,
                        occurred_in: None,
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError::new(format!("`contrary {left} {right}`：{e}")))?;
                    theory.decls.push(format!("contrary:{left}:{right}"));
                    report.declared.push(format!("contrary {left} {right}"));
                }
                Item::Unique {
                    pred,
                    index,
                    source,
                } => {
                    let p = std_deduce_kernel::name(&pred);
                    match next.env.get(&p) {
                        Some(d) if matches!(d.kind, std_deduce_kernel::DeclKind::Pred) => {}
                        Some(_) => {
                            return Err(LoadError::new(format!(
                                "`unique {pred} {index}`：`{p}` 不是谓词（pred）"
                            )))
                        }
                        None => {
                            return Err(LoadError::new(format!(
                                "`unique {pred} {index}`：未知谓词 `{p}`"
                            )))
                        }
                    }
                    let arity = pred_arity(&next.env, &p).unwrap_or(0);
                    if index == 0 || index > arity {
                        return Err(LoadError::new(format!(
                            "`unique {pred} {index}`：参数位置超出范围（该谓词有 {arity} 个参数）"
                        )));
                    }
                    let pos = index - 1;
                    for (q, i) in next.env.unique_positions() {
                        if q == p && i == pos {
                            return Err(LoadError::new(format!(
                                "`unique {pred} {index}`：这一条已经声明过了"
                            )));
                        }
                    }
                    let decl = Decl {
                        name: std_deduce_kernel::name(format!("unique:{pred}:{index}")),
                        kind: std_deduce_kernel::DeclKind::Unique {
                            pred: p,
                            index: pos,
                        },
                        ty: Expr::Sort(0),
                        sources: source.into_iter().map(to_source).collect(),
                        scope: Scope::default(),
                        occurred_at: None,
                        occurred_in: None,
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError::new(format!("`unique {pred} {index}`：{e}")))?;
                    theory.decls.push(format!("unique:{pred}:{index}"));
                    report.declared.push(format!("unique {pred} {index}"));
                }
                Item::Priority {
                    winner,
                    loser,
                    sources,
                } => {
                    // A priority is a normative claim about two rules, and it
                    // belongs to a law package: only a module knows which
                    // provision outranks which. A case file must not assert one
                    // of its own.
                    let Some(ns) = namespace.as_deref() else {
                        return Err(LoadError::new(
                            "`priority` 只能写在带 namespace 的模块里；案件文件不能声明顶层优先级",
                        ));
                    };
                    // A priority is a decision; a decision without provenance
                    // is not auditable and must not count as proved. A
                    // whitespace-only source names nothing either.
                    if !sources.iter().any(usable_source) {
                        return Err(LoadError::new(format!(
                            "`priority {winner} over {loser}`：优先关系必须有出处（法律名称 + 条号），没有出处的裁决不能被当作已证明"
                        )));
                    }
                    if winner == loser {
                        return Err(LoadError::new(format!(
                            "`priority {winner} over {loser}`：一条优先关系不能指向自己"
                        )));
                    }
                    let w = std_deduce_kernel::name(&winner);
                    let l = std_deduce_kernel::name(&loser);
                    let declared_in = std_deduce_kernel::name(ns);
                    // The reverse order is not a duplicate: it is a claim of the
                    // opposite direction by the same package.
                    for existing in next.env.priorities() {
                        if existing.declared_in == declared_in
                            && existing.winner == w
                            && existing.loser == l
                        {
                            return Err(LoadError::new(format!(
                                "`priority {winner} over {loser}`：这一条已经声明过了"
                            )));
                        }
                    }
                    let decl = Decl {
                        name: std_deduce_kernel::name(format!("priority:{ns}:{winner}:{loser}")),
                        kind: std_deduce_kernel::DeclKind::Priority {
                            winner: w,
                            loser: l,
                            declared_in,
                        },
                        ty: Expr::Sort(0),
                        sources: sources.iter().map(|s| to_source((*s).clone())).collect(),
                        scope: Scope::default(),
                        occurred_at: None,
                        occurred_in: None,
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| {
                            LoadError::new(format!("`priority {winner} over {loser}`：{e}"))
                        })?;
                    theory.decls.push(format!("priority:{ns}:{winner}:{loser}"));
                    report
                        .declared
                        .push(format!("priority {winner} over {loser}"));
                    priorities.push((winner, loser));
                }
                Item::Rule {
                    name: n,
                    params,
                    premises,
                    conclusion,
                    defeaters,
                    sources,
                    scope: scope_spec,
                } => {
                    // The scope clauses are metadata; validate them before any
                    // elaboration so a bad date is reported as such and not as
                    // a type error in the rule.
                    let scope = rule_scope(&n, &scope_spec, options).map_err(LoadError::new)?;
                    // A rule is the bridge from a legal provision to a
                    // conclusion; without a source the bridge cannot be
                    // audited. A source made only of whitespace names nothing
                    // and is rejected as well. This runs before every
                    // elaboration step so a missing source is reported as
                    // such, not as a type error.
                    if !sources.iter().any(usable_source) {
                        return Err(LoadError::new(format!(
                                "规则 `{n}` 缺少 source 或来源为空白；规则必须有出处（法律名称 + 条号，或案件材料）"
                            )));
                    }
                    // Every telescope binder is opened by the kernel as the
                    // constant `?<binder>`. Two binders with the same name
                    // would become one constant, so the reasoner could take a
                    // premise proof for a parameter value. The collision is
                    // refused before elaboration: once shadowing is in place,
                    // the rule would otherwise fail with a misleading type
                    // error instead of naming the real cause.
                    let mut binder_names: Vec<std_deduce_kernel::Name> = params
                        .iter()
                        .map(|(pn, _)| std_deduce_kernel::name(pn))
                        .collect();
                    binder_names.extend(premises.iter().enumerate().map(|(i, p)| match &p.name {
                        Some(pn) => std_deduce_kernel::name(pn),
                        None => std_deduce_kernel::name(format!("_p{i}")),
                    }));
                    std_deduce_kernel::env::check_unique_binders(&binder_names)
                        .map_err(|e| LoadError::new(format!("`rule {n}`：{e}")))?;

                    // One telescope elaboration: params and premises are
                    // elaborated in the same growing context, and the
                    // conclusion is elaborated in the full telescope. This
                    // is what lets a later premise mention an earlier one,
                    // and lets the conclusion depend on both.
                    let mut binds: Vec<(String, Expr)> = Vec::new();
                    let mut rule_params: Vec<(std_deduce_kernel::Name, Expr)> = Vec::new();
                    for (pn, pt) in &params {
                        let ty = elab::elab(&next.env, &binds, pt).map_err(|e| {
                            LoadError::new(format!("`rule {n}` 的参数 `{pn}`：{}", e.msg))
                        })?;
                        std_deduce_kernel::check::check_is_type(
                            &next.env,
                            &elab::ctx_of(&binds),
                            &ty,
                        )
                        .map_err(|e| {
                            LoadError::new(format!("`rule {n}` 的参数 `{pn}` 类型不合法：{e}"))
                        })?;
                        binds.push((pn.clone(), ty.clone()));
                        rule_params.push((std_deduce_kernel::name(pn), ty));
                    }

                    let mut rule_premises: Vec<(Option<std_deduce_kernel::Name>, Expr)> =
                        Vec::new();
                    for (i, p) in premises.iter().enumerate() {
                        let ty = elab::elab(&next.env, &binds, &p.ty).map_err(|e| {
                            LoadError::new(format!("`rule {n}` 的前提 {}：{}", i + 1, e.msg))
                        })?;
                        std_deduce_kernel::check::check(
                            &next.env,
                            &elab::ctx_of(&binds),
                            &ty,
                            &Expr::Sort(0),
                        )
                        .map_err(|e| {
                            LoadError::new(format!("`rule {n}` 的前提 {} 不是命题：{e}", i + 1))
                        })?;
                        let bind = p.name.clone().unwrap_or_else(|| format!("_p{i}"));
                        binds.push((bind.clone(), ty.clone()));
                        rule_premises.push((p.name.as_ref().map(std_deduce_kernel::name), ty));
                    }

                    let concl = elab::elab(&next.env, &binds, &conclusion)
                        .map_err(|e| LoadError::new(format!("`rule {n}` 的结论：{}", e.msg)))?;
                    std_deduce_kernel::check::check(
                        &next.env,
                        &elab::ctx_of(&binds),
                        &concl,
                        &Expr::Sort(0),
                    )
                    .map_err(|e| LoadError::new(format!("`rule {n}` 的结论不是命题：{e}")))?;

                    let mut unlesses = Vec::new();
                    let mut exceptions = Vec::new();
                    let mut prefers = Vec::new();
                    for d in &defeaters {
                        match d {
                            crate::ast::Defeater::Unless(t) => {
                                let e = elab::elab(&next.env, &binds, t).map_err(|e| {
                                    LoadError::new(format!("`rule {n}` 的 unless：{}", e.msg))
                                })?;
                                std_deduce_kernel::check::check(
                                    &next.env,
                                    &elab::ctx_of(&binds),
                                    &e,
                                    &Expr::Sort(0),
                                )
                                .map_err(|e| {
                                    LoadError::new(format!("`rule {n}` 的 unless 不是命题：{e}"))
                                })?;
                                unlesses.push(e);
                            }
                            crate::ast::Defeater::By(r) => {
                                exceptions.push(std_deduce_kernel::name(r));
                            }
                            crate::ast::Defeater::Prefer(r) => {
                                prefers.push(std_deduce_kernel::name(r));
                            }
                        }
                    }

                    let rdecl = std_deduce_kernel::RuleDecl {
                        params: rule_params,
                        premises: rule_premises,
                        conclusion: concl,
                        unlesses,
                        exceptions,
                        prefers,
                        sources: sources.iter().map(|s| to_source((*s).clone())).collect(),
                        declared_in: namespace.as_ref().map(std_deduce_kernel::name),
                    };
                    let ty = std_deduce_kernel::env::rule_type(&rdecl);
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Rule(Box::new(rdecl)),
                        ty,
                        sources: sources.iter().map(|s| to_source((*s).clone())).collect(),
                        scope,
                        occurred_at: None,
                        occurred_in: None,
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError::new(format!("`rule {n}`：{e}")))?;
                    theory.decls.push(n.clone());
                    theory.rules.push(n.clone());
                    report.declared.push(n);
                }
                Item::Interpretation { name: n, .. } => {
                    // The parser accepts an interpretation declaration, but
                    // nothing in the reasoner or the certificate layer reads
                    // it. Letting it into the ledger would make `:why` show a
                    // gap while `:inspect` claims an interpretation exists;
                    // refuse it explicitly until M2-8 implements the semantics.
                    return Err(LoadError::new(format!(
                        "`interpret {n}`：解释语义尚未实现（M2-8），推理器不消费解释"
                    )));
                }
                Item::Check(t) => {
                    let e = elab::elab_top(&next.env, &t).map_err(|e| LoadError::new(e.msg))?;
                    let ty = std_deduce_kernel::check::infer(
                        &next.env,
                        &std_deduce_kernel::Ctx::new(),
                        &e,
                    )
                    .map_err(|e| LoadError::new(e.to_string()))?;
                    report.checked.push(format!(
                        "{} : {}",
                        std_deduce_kernel::pretty::print_expr(&e),
                        std_deduce_kernel::pretty::print_expr(&ty)
                    ));
                }
                Item::Proposition(t) => {
                    let e = elab::elab_top(&next.env, &t).map_err(|e| LoadError::new(e.msg))?;
                    std_deduce_kernel::check::check(
                        &next.env,
                        &std_deduce_kernel::Ctx::new(),
                        &e,
                        &std_deduce_kernel::Expr::Sort(0),
                    )
                    .map_err(|e| LoadError::new(format!("`#proposition` 的项不是命题：{e}")))?;
                    report.checked.push(format!(
                        "命题：{}",
                        std_deduce_kernel::pretty::print_expr(&e)
                    ));
                }
                Item::Show(n) => {
                    if let Some(d) = next.env.get(&n) {
                        report.shown.push(format!(
                            "{} : {}",
                            d.name,
                            std_deduce_kernel::pretty::print_expr(&d.ty)
                        ));
                    } else {
                        return Err(LoadError::new(format!("`#show {n}`：未知名称")));
                    }
                }
                Item::Why(_) | Item::Gap(_) => {
                    return Err(LoadError::new(
                        "#why / #gap 需要推理引擎，请用独立的推理命令",
                    ))
                }
            }
        }

        // A `defeated_by` / `prefer` name is stored as an opaque string, so a
        // typo would silently disable the intended priority. Validate the
        // targets after the whole file is in the environment, which allows a
        // rule to name a rule declared later in the same file.
        check_rule_targets(&next.env, &theory.rules).map_err(LoadError::new)?;
        // A top-level `priority` may name rules declared later in the same
        // file as well, so its targets are checked against the completed
        // environment too.
        check_priority_targets(
            &next.env,
            &priorities,
            &report.imported,
            namespace.as_deref(),
        )
        .map_err(LoadError::new)?;

        // Commit only if everything above succeeded.
        if let Some(existing) = next.theories.iter_mut().find(|t| t.name == theory_name) {
            existing.decls.extend(theory.decls);
            existing.rules.extend(theory.rules);
            for pack in theory.requires {
                if !existing.requires.contains(&pack) {
                    existing.requires.push(pack);
                }
            }
        } else {
            next.theories.push(theory);
        }
        *self = next;
        Ok(report)
    }
}

#[derive(Debug, Clone, Default)]
pub struct LoadReport {
    pub declared: Vec<String>,
    pub checked: Vec<String>,
    pub shown: Vec<String>,
    /// Packages imported by this file, in first appearance order and without
    /// duplicates. An import is not a declaration and never enters the ledger.
    pub imported: Vec<String>,
}

/// Escape a path for a one-line diagnostic.
///
/// Newline, carriage return and tab get their short forms; other control
/// characters, U+2028/U+2029 and the bidi/format characters listed in
/// [`std_deduce_kernel::env::escape_control`] become `\u{XXXX}`. A literal
/// backslash is kept as is, so a Windows path stays readable instead of being
/// doubled.
pub fn escape_path(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for ch in value.chars() {
        match ch {
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            ch if ch.is_control()
                || matches!(
                    ch,
                    '\u{061C}'
                        | '\u{180E}'
                        | '\u{200B}'..='\u{200F}'
                        | '\u{2028}'
                        | '\u{2029}'
                        | '\u{202A}'..='\u{202E}'
                        | '\u{2060}'..='\u{206F}'
                        | '\u{FEFF}'
                ) =>
            {
                escaped.push_str(&format!("\\u{{{:04X}}}", ch as u32));
            }
            ch => escaped.push(ch),
        }
    }
    escaped
}

/// A failed load. The message is independent of where the error was found:
/// `msg` is the text shown to the user, and the optional line/column is a
/// source position when the loader has one.
#[derive(Debug, Clone)]
pub struct LoadError {
    pub msg: String,
    line: Option<usize>,
    col: Option<usize>,
}

impl LoadError {
    /// An error with no known source position (refinement, kernel, I/O or a
    /// whole-file check).
    pub fn new(msg: impl Into<String>) -> Self {
        LoadError {
            msg: msg.into(),
            line: None,
            col: None,
        }
    }

    /// An error at a 1-based source position.
    pub fn at(msg: impl Into<String>, line: usize, col: usize) -> Self {
        LoadError {
            msg: msg.into(),
            line: Some(line),
            col: Some(col),
        }
    }

    /// The 1-based `(line, column)`, when the loader knows it.
    pub fn position(&self) -> Option<(usize, usize)> {
        Some((self.line?, self.col?))
    }

    /// Render the error in Lean style. A positioned error is
    /// `path:line:col: error: msg`; one without a position is
    /// `path: error: msg`. The line/column is never invented for errors that
    /// do not carry one. The path is escaped, so it cannot inject a second
    /// diagnostic line or a terminal control sequence.
    pub fn render(&self, path: &str) -> String {
        let path = escape_path(path);
        match self.position() {
            Some((line, col)) => format!("{path}:{line}:{col}: error: {}", self.msg),
            None => format!("{path}: error: {}", self.msg),
        }
    }
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.msg)
    }
}
impl std::error::Error for LoadError {}
impl From<Error> for LoadError {
    fn from(e: Error) -> Self {
        LoadError::new(e.to_string())
    }
}

/// The package names imported by a file, in first appearance order, without
/// duplicates. Duplicate imports are legal: they name the same package and are
/// recorded once.
fn collect_imports(items: &[Item]) -> Vec<String> {
    let mut packs: Vec<String> = Vec::new();
    for item in items {
        if let Item::Import(pack) = item {
            if !packs.contains(pack) {
                packs.push(pack.clone());
            }
        }
    }
    packs
}

/// A qualified name has at least one dot and no empty dot-separated segment.
/// Whether the namespace exists is left to the elaborator's existing
/// unknown-name check.
fn is_qualified(name: &str) -> bool {
    name.contains('.') && name.split('.').all(|part| !part.is_empty())
}

/// Whether `name` is declared under exactly `ns.`.
fn has_namespace_prefix(ns: &str, name: &str) -> bool {
    name.strip_prefix(ns)
        .and_then(|rest| rest.strip_prefix('.'))
        .is_some_and(|rest| !rest.is_empty())
}

fn require_decl_name(ns: &str, kind: &str, name: &str) -> Result<(), String> {
    if !has_namespace_prefix(ns, name) {
        return Err(format!(
            "`{kind} {name}`：模块 `{ns}` 的声明名必须以 `{ns}.` 开头"
        ));
    }
    let rest = name
        .strip_prefix(ns)
        .and_then(|rest| rest.strip_prefix('.'))
        .unwrap_or_default();
    if rest.split('.').any(|part| part.is_empty()) {
        return Err(format!(
            "`{kind} {name}`：声明名 `{ns}.` 之后不能有空段（`.` 之间必须有内容）"
        ));
    }
    Ok(())
}

/// A non-namespaced file is a case/example file. Its declarations keep the
/// old unprefixed form, but a dotted declaration name would squat on a
/// module's qualified name and could collide with it later. References may
/// still be dotted; only declaration names are checked here.
fn check_case_decl_names(items: &[Item]) -> Result<(), String> {
    for item in items {
        let (kind, name) = match item {
            Item::Sort { name, .. } => ("sort", name),
            Item::Obj { name, .. } => ("obj", name),
            Item::Pred { name, .. } => ("pred", name),
            Item::Axiom { name, .. } => ("axiom", name),
            Item::Def { name, .. } => ("def", name),
            Item::Rule { name, .. } => ("rule", name),
            Item::Interpretation { name, .. } => ("interpret", name),
            // A priority is a normative claim, and only a law package may
            // assert one: a case file must not add its own.
            Item::Priority { .. } => {
                return Err(
                    "`priority` 只能写在带 namespace 的模块里；案件文件不能声明顶层优先级"
                        .to_string(),
                )
            }
            Item::Namespace(_)
            | Item::Import(_)
            | Item::Contrary { .. }
            | Item::Unique { .. }
            | Item::Check(_)
            | Item::Why(_)
            | Item::Gap(_)
            | Item::Proposition(_)
            | Item::Show(_) => continue,
        };
        if name.contains('.') {
            return Err(format!(
                "`{kind} {name}`：没有 namespace 的案件/示例文件不能声明带 `.` 的名字；\
                 带点名字只能由模块文件在 namespace 下声明"
            ));
        }
    }
    Ok(())
}

/// Validate every `defeated_by` / `prefer` target of the rules just loaded.
/// The targets are checked against the completed environment, so a forward
/// reference to a rule later in the same file is legal.
///
/// A rule-internal clause only orders rules of the declaring module: a
/// cross-package order is a normative claim of its own, so it must be declared
/// as a top-level `priority` with a source. The winner/loser direction depends
/// on the clause: `defeated_by X` makes `X` the winner, `prefer X` makes the
/// declaring rule the winner.
fn check_rule_targets(env: &Env, rules: &[String]) -> Result<(), String> {
    for rule_name in rules {
        let Some(decl) = env.get(rule_name) else {
            continue;
        };
        let std_deduce_kernel::DeclKind::Rule(rule) = &decl.kind else {
            continue;
        };
        for (clause, targets) in [("defeated_by", &rule.exceptions), ("prefer", &rule.prefers)] {
            for target in targets {
                let Some(target_decl) = env.get(target) else {
                    return Err(format!(
                        "`rule {rule_name}` 的 {clause} 目标 `{target}` 不存在；\
                         defeated_by/prefer 必须指向已加载或同文件后声明的规则"
                    ));
                };
                let std_deduce_kernel::DeclKind::Rule(target_rule) = &target_decl.kind else {
                    return Err(format!(
                        "`rule {rule_name}` 的 {clause} 目标 `{target}` 不是规则；\
                         defeated_by/prefer 必须指向规则"
                    ));
                };
                // A rule cannot outrank itself, in either clause direction.
                // This mirrors the top-level `priority r over r` refusal: the
                // edge would never participate in a resolution.
                if target.as_ref() == rule_name.as_str() {
                    return Err(format!(
                        "`rule {rule_name}` 的 `{clause}` 指向自己；规则不能优先于自身"
                    ));
                }
                if rule.declared_in == target_rule.declared_in {
                    continue;
                }
                let (winner, loser) = match clause {
                    "defeated_by" => (target.as_ref(), rule_name.as_str()),
                    _ => (rule_name.as_str(), target.as_ref()),
                };
                let target_ns = target_rule
                    .declared_in
                    .as_deref()
                    .unwrap_or("无 namespace（案件/示例文件）");
                return Err(format!(
                    "规则 `{rule_name}` 的 `{clause}` 指向了另一个包 `{target_ns}` 的规则 `{target}`；\
                     跨包优先关系必须用顶层 `priority {winner} over {loser}` 声明并写明 source，\
                     规则内子句只用于同一包内"
                ));
            }
        }
    }
    Ok(())
}

/// Validate the targets of the top-level `priority` declarations just loaded.
/// They are looked up in the completed environment, so a priority may name a
/// rule declared later in the same file.
///
/// Both names must be rules. A rule of another package may be ordered only
/// when that package is imported: a priority asserted from outside the package
/// is a claim about code the file has not opted into. A case rule is not part
/// of a package's normative order and cannot be a target at all.
fn check_priority_targets(
    env: &Env,
    priorities: &[(String, String)],
    imported: &[String],
    namespace: Option<&str>,
) -> Result<(), String> {
    for (winner, loser) in priorities {
        let what = format!("`priority {winner} over {loser}`");
        for target in [winner, loser] {
            let Some(decl) = env.get(target) else {
                return Err(format!("{what}：未知规则 `{target}`"));
            };
            let std_deduce_kernel::DeclKind::Rule(rule) = &decl.kind else {
                return Err(format!("{what}：`{target}` 不是规则"));
            };
            let Some(target_ns) = rule.declared_in.as_deref() else {
                return Err(format!("{what}：不能对案件文件里的规则声明优先级"));
            };
            if Some(target_ns) == namespace {
                continue;
            }
            if !imported.iter().any(|pack| pack == target_ns) {
                return Err(format!(
                    "{what}：目标规则在 `{target_ns}` 里，但本文件没有 `import {target_ns}`；\
                     跨包优先级必须显式 import 目标包"
                ));
            }
        }
    }
    Ok(())
}

fn namespace_label(namespace: &Option<String>) -> String {
    match namespace {
        Some(ns) => format!("`{ns}`"),
        None => "无 namespace（案件/示例文件）".into(),
    }
}

fn require_qualified_ref(ns: &str, what: &str, name: &str) -> Result<(), String> {
    if is_qualified(name) {
        Ok(())
    } else {
        Err(format!(
            "{what}：名称 `{name}` 未限定；模块 `{ns}` 内的引用必须写全限定名（如 `{ns}.{name}`）"
        ))
    }
}

/// Check a surface term's constant references. Local binders are `Var` at
/// elaboration time, so they are in `locals` and do not need a prefix; every
/// other `Ident` is a reference to a declaration and must be qualified.
fn check_term(ns: &str, what: &str, locals: &[String], term: &Term) -> Result<(), String> {
    match term {
        Term::Prop | Term::Type(_) => Ok(()),
        Term::Ident(s) => {
            if s == "_" || locals.iter().any(|local| local == s) {
                Ok(())
            } else {
                require_qualified_ref(ns, what, s)
            }
        }
        Term::Pi {
            name,
            domain,
            codomain,
        } => {
            check_term(ns, what, locals, domain)?;
            let mut inner = locals.to_vec();
            if let Some(n) = name {
                inner.push(n.clone());
            }
            check_term(ns, what, &inner, codomain)
        }
        Term::Lam { name, domain, body } => {
            check_term(ns, what, locals, domain)?;
            let mut inner = locals.to_vec();
            inner.push(name.clone());
            check_term(ns, what, &inner, body)
        }
        Term::App(func, arg) => {
            check_term(ns, what, locals, func)?;
            check_term(ns, what, locals, arg)
        }
    }
}

fn check_rule(
    ns: &str,
    name: &str,
    params: &[(String, Term)],
    premises: &[crate::ast::Premise],
    conclusion: &Term,
    defeaters: &[Defeater],
) -> Result<(), String> {
    let mut locals = Vec::new();
    for (param, ty) in params {
        let what = format!("`rule {name}` 的参数 `{param}`");
        check_term(ns, &what, &locals, ty)?;
        locals.push(param.clone());
    }
    for (i, premise) in premises.iter().enumerate() {
        let what = match &premise.name {
            Some(binder) => format!("`rule {name}` 的前提 `{binder}`"),
            None => format!("`rule {name}` 的前提 {}", i + 1),
        };
        check_term(ns, &what, &locals, &premise.ty)?;
        // A named premise binds its name; an unnamed one is opened by the
        // elaborator as the generated local `_p{i}`.
        match &premise.name {
            Some(binder) => locals.push(binder.clone()),
            None => locals.push(format!("_p{i}")),
        }
    }
    let what = format!("`rule {name}` 的结论");
    check_term(ns, &what, &locals, conclusion)?;
    for defeater in defeaters {
        match defeater {
            Defeater::Unless(t) => {
                let what = format!("`rule {name}` 的 unless");
                check_term(ns, &what, &locals, t)?;
            }
            Defeater::By(rule) => {
                let what = format!("`rule {name}` 的 defeated_by");
                require_qualified_ref(ns, &what, rule)?;
            }
            Defeater::Prefer(rule) => {
                let what = format!("`rule {name}` 的 prefer");
                require_qualified_ref(ns, &what, rule)?;
            }
        }
    }
    Ok(())
}

/// Enforce the module contract for one file: declarations live under the
/// file's namespace and every declaration reference is fully qualified. This
/// runs before loading so an unqualified name cannot silently resolve to a
/// same-named case-level declaration.
fn check_module_names(ns: &str, items: &[Item]) -> Result<(), String> {
    for item in items {
        match item {
            Item::Namespace(_) | Item::Import(_) => {}
            Item::Sort { name, .. } => require_decl_name(ns, "sort", name)?,
            Item::Obj { name, ty, .. } => {
                require_decl_name(ns, "obj", name)?;
                let what = format!("`obj {name}` 的类型");
                check_term(ns, &what, &[], ty)?;
            }
            Item::Pred { name, ty, .. } => {
                require_decl_name(ns, "pred", name)?;
                let what = format!("`pred {name}` 的类型");
                check_term(ns, &what, &[], ty)?;
            }
            Item::Axiom { name, ty, .. } => {
                require_decl_name(ns, "axiom", name)?;
                let what = format!("`axiom {name}` 的类型");
                check_term(ns, &what, &[], ty)?;
            }
            Item::Def { name, ty, body, .. } => {
                require_decl_name(ns, "def", name)?;
                let what = format!("`def {name}` 的类型");
                check_term(ns, &what, &[], ty)?;
                let what = format!("`def {name}` 的定义");
                check_term(ns, &what, &[], body)?;
            }
            Item::Rule {
                name,
                params,
                premises,
                conclusion,
                defeaters,
                ..
            } => {
                require_decl_name(ns, "rule", name)?;
                check_rule(ns, name, params, premises, conclusion, defeaters)?;
            }
            Item::Interpretation { name, from, to, .. } => {
                require_decl_name(ns, "interpret", name)?;
                let what = format!("`interpret {name}` 的 from");
                check_term(ns, &what, &[], from)?;
                let what = format!("`interpret {name}` 的 to");
                check_term(ns, &what, &[], to)?;
            }
            Item::Contrary { left, right, .. } => {
                let what = format!("`contrary {left} {right}`");
                require_qualified_ref(ns, &what, left)?;
                require_qualified_ref(ns, &what, right)?;
            }
            Item::Unique { pred, index, .. } => {
                let what = format!("`unique {pred} {index}`");
                require_qualified_ref(ns, &what, pred)?;
            }
            Item::Priority { winner, loser, .. } => {
                let what = format!("`priority {winner} over {loser}`");
                require_qualified_ref(ns, &what, winner)?;
                require_qualified_ref(ns, &what, loser)?;
            }
            Item::Check(t) => check_term(ns, "`#check` 的项", &[], t)?,
            Item::Why(t) => check_term(ns, "`#why` 的项", &[], t)?,
            Item::Gap(t) => check_term(ns, "`#gap` 的项", &[], t)?,
            Item::Proposition(t) => check_term(ns, "`#proposition` 的项", &[], t)?,
            Item::Show(name) => require_qualified_ref(ns, "`#show`", name)?,
        }
    }
    Ok(())
}

/// Number of arguments a predicate takes, read off its declared type.
fn pred_arity(env: &Env, name: &std_deduce_kernel::Name) -> Option<usize> {
    let d = env.get(name)?;
    if !matches!(d.kind, std_deduce_kernel::DeclKind::Pred) {
        return None;
    }
    let mut ty = d.ty.clone();
    let mut n = 0;
    loop {
        ty = std_deduce_kernel::norm::normalize(env, &std_deduce_kernel::Ctx::new(), &ty).ok()?;
        match ty {
            Expr::Pi { codomain, .. } => {
                n += 1;
                ty = *codomain;
            }
            _ => break,
        }
    }
    Some(n)
}

/// Whether a parsed source names something: both its text and its locator
/// must contain a non-whitespace character. Whitespace-only strings parse as
/// non-empty but are not provenance.
fn usable_source(source: &crate::ast::SourceSpec) -> bool {
    !source.text.trim().is_empty() && !source.locator.trim().is_empty()
}

/// Validate the pack-manifest scope a package loader passes in.
///
/// The manifest already validated these values, but [`Library::load_with_options`]
/// is public: a caller that builds a [`Scope`] by hand must not be able to put
/// an impossible date or code into the ledger. The check is structural only; it
/// does not judge whether the range makes legal sense.
fn validate_pack_scope(scope: &Scope) -> Result<(), String> {
    if let Some(date) = &scope.effective_from {
        validate_date("法律包清单的 effective_from", date)?;
    }
    if let Some(date) = &scope.effective_to {
        validate_date("法律包清单的 effective_to", date)?;
    }
    if let Some(code) = &scope.jurisdiction {
        validate_jurisdiction_code("法律包清单的 jurisdiction", code)?;
    }
    if let Some(code) = &scope.territory {
        validate_jurisdiction_code("法律包清单的 territory", code)?;
    }
    Ok(())
}

/// Combine a rule's written scope clauses with the containing pack's manifest.
///
/// Values are decided field by field: a written clause wins, and a missing one
/// falls back to the manifest for a pack rule. Case-local rules never inherit.
/// `repealed` is the exclusive end and must be written together with
/// `effective` and be later than it; the comparison is a plain string compare,
/// which is correct for validated `YYYY-MM-DD` values.
fn rule_scope(name: &str, written: &ScopeSpec, options: &LoadOptions) -> Result<Scope, String> {
    if let Some(date) = &written.effective_from {
        validate_date(&format!("`rule {name}` 的 effective"), date)?;
    }
    if let Some(date) = &written.effective_to {
        validate_date(&format!("`rule {name}` 的 repealed"), date)?;
    }
    if let Some(code) = &written.jurisdiction {
        validate_jurisdiction_code(&format!("`rule {name}` 的 jurisdiction"), code)?;
    }
    if let Some(code) = &written.territory {
        validate_jurisdiction_code(&format!("`rule {name}` 的 territory"), code)?;
    }
    if written.effective_to.is_some() && written.effective_from.is_none() {
        return Err(format!(
            "`rule {name}`：`repealed` 必须与 `effective` 同用；失效日不能没有生效起点"
        ));
    }
    if let (Some(from), Some(to)) = (&written.effective_from, &written.effective_to) {
        if to <= from {
            return Err(format!(
                "`rule {name}`：`repealed` `{to}` 必须晚于 `effective` `{from}`（失效日不含当天）"
            ));
        }
    }
    if options.case_local {
        return Ok(Scope {
            effective_from: written.effective_from.clone(),
            effective_to: written.effective_to.clone(),
            jurisdiction: written.jurisdiction.clone(),
            territory: written.territory.clone(),
            origin: ScopeOrigin::CaseLocal,
        });
    }
    let inherited = options.pack_scope.as_ref();
    let origin = if !written.is_empty() {
        ScopeOrigin::Rule
    } else if inherited.is_some() {
        ScopeOrigin::PackDefault
    } else {
        ScopeOrigin::Unspecified
    };
    Ok(Scope {
        effective_from: written
            .effective_from
            .clone()
            .or_else(|| inherited.and_then(|scope| scope.effective_from.clone())),
        effective_to: written
            .effective_to
            .clone()
            .or_else(|| inherited.and_then(|scope| scope.effective_to.clone())),
        jurisdiction: written
            .jurisdiction
            .clone()
            .or_else(|| inherited.and_then(|scope| scope.jurisdiction.clone())),
        territory: written
            .territory
            .clone()
            .or_else(|| inherited.and_then(|scope| scope.territory.clone())),
        origin,
    })
}

fn to_source(s: crate::ast::SourceSpec) -> SourceRef {
    SourceRef {
        text: s.text,
        locator: s.locator,
        version: s.version,
        effective: s.effective,
        note: s.note,
        quote: s.quote,
        url: s.url,
        jurisdiction: s.jurisdiction,
        retrieved_at: s.retrieved_at,
        hash: s.hash,
    }
}

#[cfg(test)]
mod tests {
    use super::{escape_path, LoadError};

    #[test]
    fn a_positioned_error_renders_lean_style() {
        let err = LoadError::at("期望项", 2, 3);
        assert_eq!(err.position(), Some((2, 3)));
        assert_eq!(err.render("x.std"), "x.std:2:3: error: 期望项");
        // Display stays the bare message, so existing text assertions hold.
        assert_eq!(err.to_string(), "期望项");
    }

    #[test]
    fn an_unpositioned_error_renders_without_a_location() {
        let err = LoadError::new("未知名称");
        assert_eq!(err.position(), None);
        assert_eq!(err.render("x.std"), "x.std: error: 未知名称");
        assert_eq!(err.to_string(), "未知名称");
    }

    #[test]
    fn escape_path_keeps_backslashes_and_escapes_diagnostic_characters() {
        // A literal backslash is a Windows separator, not an escape to double.
        let path = "C:\\案卷\\a\nb\r\t\u{001B}\u{202E}\u{2028}\u{FEFF}.std";
        let escaped = escape_path(path);
        assert_eq!(
            escaped,
            "C:\\案卷\\a\\nb\\r\\t\\u{001B}\\u{202E}\\u{2028}\\u{FEFF}.std"
        );
        assert!(!escaped.contains('\n'), "{escaped:?}");
        assert!(!escaped.contains('\r'), "{escaped:?}");
        assert!(!escaped.contains('\t'), "{escaped:?}");
        assert!(!escaped.contains('\u{001B}'), "{escaped:?}");
        assert!(!escaped.contains('\u{202E}'), "{escaped:?}");
        assert!(!escaped.contains("\\\\"), "backslashes must not be doubled");
    }

    #[test]
    fn a_load_error_render_escapes_the_path_onto_one_line() {
        let err = LoadError::at("坏声明", 1, 2);
        let rendered = err.render("C:\\案卷\\a\nb\u{001B}\u{202E}.std");
        assert_eq!(
            rendered,
            "C:\\案卷\\a\\nb\\u{001B}\\u{202E}.std:1:2: error: 坏声明"
        );
        assert_eq!(rendered.lines().count(), 1, "{rendered:?}");
        assert!(!rendered.contains('\u{001B}'), "{rendered:?}");
        assert!(!rendered.contains('\u{202E}'), "{rendered:?}");
    }
}
