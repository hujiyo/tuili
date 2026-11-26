//! Theory files: a named unit of declarations.
//!
//! A `Theory` is not a kernel object. It is a *documentation and audit*
//! device: it records that a group of declarations were formalised together,
//! from which source, and by whom. The kernel sees only the flat ledger,
//! which is what keeps the trusted core small.

use std_deduce_kernel::env::{
    check_unique_binders, Decl, Env, PremiseDecl, PremiseKind, SourceRef,
};
use std_deduce_kernel::meta::{validate_date, validate_jurisdiction_code, Scope, ScopeOrigin};
use std_deduce_kernel::{Error, Expr, FactIdentity};

use crate::ast::{Defeater, Item, PremiseKind as AstPremiseKind, ScopeSpec, Term};
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
    ///
    /// This is a complete single-file load, so it also checks the `revision`
    /// groups of the resulting environment once the file is in (see
    /// [`Library::check_revision_groups`]). A caller that loads one file as part
    /// of a larger transaction — a pack whose theory files split one provision's
    /// versions — uses [`Library::load_with_options`] and calls the group check
    /// when the transaction is complete.
    pub fn load(&mut self, name: &str, src: &str) -> Result<LoadReport, LoadError> {
        let snapshot = self.clone();
        let report = self.load_with_options(name, src, &LoadOptions::default())?;
        if let Err(error) = check_revision_groups(&self.env, &[]) {
            *self = snapshot;
            return Err(error);
        }
        Ok(report)
    }

    /// Check every `revision` group of the completed environment.
    ///
    /// The group relation is declared, not inferred, and the loader never picks
    /// a version. What it does guarantee, once a whole load transaction is
    /// complete, is that the declared groups mean something: at least two
    /// members, no two members with the same rule name, an effective range on
    /// every member, and no identifier naming an existing declaration. The
    /// check runs after all files and imports of the transaction are in, because
    /// a law pack may split one provision's versions across theory files.
    ///
    /// The caller owns the rollback: a failed check leaves this library as the
    /// caller left it (the CLI loads on a clone and commits only at the end).
    pub fn check_revision_groups(&self) -> Result<(), LoadError> {
        check_revision_groups(&self.env, &[])
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
        // Every `open` target with the position it was written at. The marker
        // itself enters the ledger immediately, but its target is validated
        // against the completed environment so a predicate may be declared
        // later in the same file.
        let mut open_concepts: Vec<(String, usize, usize)> = Vec::new();
        // Every `risk` target with its theme and position. Like `open`, the
        // marker is inserted after the whole file is in the environment, so it
        // may mark a predicate declared later in the same file.
        let mut risk_themes: Vec<(String, String, usize, usize)> = Vec::new();
        // Every rule's `revision <标识>` clause with its position. Grouping is
        // a declaration; the group checks run against the completed
        // environment (so a version declared later in the same file counts) and
        // still point at the clause that must be fixed.
        let mut revision_claims: Vec<(String, crate::ast::Revision)> = Vec::new();

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
                    line,
                    col,
                } => {
                    if let Some(err) = decl_name_clash(&next.env, &n, "pred", line, col) {
                        return Err(err);
                    }
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
                    line,
                    col,
                } => {
                    // The ledger has one namespace for every declaration
                    // kind, so a definition may not shadow an existing
                    // sort/obj/pred/axiom/fact/rule/def. Report the clash at
                    // the definition with both names, before the body is
                    // examined.
                    if let Some(err) = decl_name_clash(&next.env, &n, "def", line, col) {
                        return Err(err);
                    }
                    // A definition is a macro the kernel unfolds by delta: its
                    // body must be resolvable when the declaration loads. A
                    // self-reference, a reference to a name declared later
                    // (mutual recursion) or a name bound by no λ/∀ is refused
                    // here, before elaboration, so the error names the
                    // definition and the offending name at its own position
                    // instead of surfacing as a bare "unknown name".
                    check_definition_body(&n, &body, &next.env)
                        .map_err(|msg| LoadError::at(msg, line, col))?;
                    let ety = elab::elab_top(&next.env, &ty)
                        .map_err(|e| LoadError::at(format!("`def {n}`：{}", e.msg), line, col))?;
                    let ebody = elab::elab_top(&next.env, &body)
                        .map_err(|e| LoadError::at(format!("`def {n}`：{}", e.msg), line, col))?;
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
                        .map_err(|e| LoadError::at(format!("`def {n}`：{e}"), line, col))?;
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
                Item::Open { pred, line, col } => {
                    // The marker is metadata about a predicate, so it is
                    // inserted after the whole file is in the environment:
                    // that lets a predicate declared later in the same file be
                    // opened, and it lets the post-pass validate the target
                    // before it reports a repeated marker.
                    open_concepts.push((pred, line, col));
                }
                Item::Risk {
                    theme,
                    pred,
                    line,
                    col,
                } => {
                    // The marker records a declared theme for a predicate; its
                    // target and the theme keyword are validated after the
                    // whole file is in the environment, so a predicate declared
                    // later in the same file can be marked too.
                    risk_themes.push((theme, pred, line, col));
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
                    guards,
                    sources,
                    scope: scope_spec,
                    revision,
                    burden,
                    standard,
                    exception_burden,
                    exception_standard,
                } => {
                    // The scope clauses are metadata; validate them before any
                    // elaboration so a bad date is reported as such and not as
                    // a type error in the rule.
                    let scope = rule_scope(&n, &scope_spec, options).map_err(LoadError::new)?;
                    // Where the declared versions live. A module is grouped by
                    // its namespace; a case/example file is grouped by the file
                    // it was loaded from, so two case files that each write
                    // `revision 第二十条` do not merge into one group (and
                    // neither can complete the other's group).
                    let revision_group =
                        revision
                            .as_ref()
                            .map(|rev| std_deduce_kernel::RevisionGroup {
                                scope: match namespace.as_deref() {
                                    Some(ns) => std_deduce_kernel::RevisionScope::Namespace(
                                        std_deduce_kernel::name(ns),
                                    ),
                                    None => std_deduce_kernel::RevisionScope::File(
                                        std_deduce_kernel::name(&theory_name),
                                    ),
                                },
                                revision: std_deduce_kernel::name(&rev.id),
                            });
                    // Historical versions of one group share the declaration
                    // name space: a version may not reuse another version's
                    // rule name. The ledger refuses a duplicate name of any
                    // kind; when the clash is inside one revision group the
                    // error names the group and the clause position, because
                    // reusing a version's name is the mistake the `revision`
                    // declaration invited.
                    if let (Some(rev), Some(group)) = (&revision, &revision_group) {
                        if let Some(existing) = next.env.get(&std_deduce_kernel::name(&n)) {
                            if let std_deduce_kernel::DeclKind::Rule(existing_rule) = &existing.kind
                            {
                                if existing_rule.revision.as_ref() == Some(group) {
                                    return Err(LoadError::at(
                                        format!(
                                            "`rule {n}` 的 `revision {}`：同一 revision 组内不能有同名规则；\
                                             `{n}` 已经作为该组的一个历史版本声明过——同一组的每个版本必须是不同的规则",
                                            rev.id
                                        ),
                                        rev.line,
                                        rev.col,
                                    ));
                                }
                            }
                        }
                    }
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
                    let mut exists_binders: Vec<std_deduce_kernel::Name> = Vec::new();
                    for (i, p) in premises.iter().enumerate() {
                        let bind = match &p.name {
                            Some(pn) => std_deduce_kernel::name(pn),
                            None => std_deduce_kernel::name(format!("_p{i}")),
                        };
                        if let AstPremiseKind::Exists { binder, .. } = &p.kind {
                            let witness = std_deduce_kernel::name(binder);
                            if binder_names.contains(&witness) || exists_binders.contains(&witness)
                            {
                                return Err(LoadError::new(format!(
                                    "`rule {n}`：存在前提 {} 的见证变量 `{binder}` 与参数、\
                                     前提绑定或另一存在见证重名；见证会与规则绑定混成一个常量，必须改名",
                                    i + 1
                                )));
                            }
                            exists_binders.push(witness);
                        }
                        // Only a plain premise proof is a kernel binder. A
                        // compound premise is a logical side condition, so its
                        // (optional) name does not enter the telescope.
                        if matches!(p.kind, AstPremiseKind::Plain(_)) {
                            binder_names.push(bind);
                        }
                    }
                    check_unique_binders(&binder_names)
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

                    let mut rule_premises: Vec<PremiseDecl> = Vec::new();
                    for (i, p) in premises.iter().enumerate() {
                        let kind = match &p.kind {
                            AstPremiseKind::Plain(term) => {
                                let ty = elab::elab(&next.env, &binds, term).map_err(|e| {
                                    LoadError::new(format!(
                                        "`rule {n}` 的前提 {}：{}",
                                        i + 1,
                                        e.msg
                                    ))
                                })?;
                                std_deduce_kernel::check::check(
                                    &next.env,
                                    &elab::ctx_of(&binds),
                                    &ty,
                                    &Expr::Sort(0),
                                )
                                .map_err(|e| {
                                    LoadError::new(format!(
                                        "`rule {n}` 的前提 {} 不是命题：{e}",
                                        i + 1
                                    ))
                                })?;
                                PremiseKind::Plain(ty)
                            }
                            AstPremiseKind::Or(branches) => {
                                if branches.len() > std_deduce_kernel::MAX_OR_BRANCHES {
                                    return Err(LoadError::new(format!(
                                        "`rule {n}` 的前提 {} 的析取有 {} 个分支，\
                                         超过每个析取前提 {} 个分支的上限",
                                        i + 1,
                                        branches.len(),
                                        std_deduce_kernel::MAX_OR_BRANCHES
                                    )));
                                }
                                let mut encoded = Vec::with_capacity(branches.len());
                                for (j, branch) in branches.iter().enumerate() {
                                    let proposition = elab::elab(&next.env, &binds, branch)
                                        .map_err(|e| {
                                            LoadError::new(format!(
                                                "`rule {n}` 的前提 {} 的第 {} 个析取分支：{}",
                                                i + 1,
                                                j + 1,
                                                e.msg
                                            ))
                                        })?;
                                    std_deduce_kernel::check::check(
                                        &next.env,
                                        &elab::ctx_of(&binds),
                                        &proposition,
                                        &Expr::Sort(0),
                                    )
                                    .map_err(|e| {
                                        LoadError::new(format!(
                                            "`rule {n}` 的前提 {} 的第 {} 个析取分支不是命题：{e}",
                                            i + 1,
                                            j + 1
                                        ))
                                    })?;
                                    encoded.push(proposition);
                                }
                                PremiseKind::Or(encoded)
                            }
                            AstPremiseKind::Exists {
                                binder,
                                domain,
                                body,
                            } => {
                                let witness = std_deduce_kernel::name(binder);
                                let domain =
                                    elab::elab(&next.env, &binds, domain).map_err(|e| {
                                        LoadError::new(format!(
                                            "`rule {n}` 的前提 {} 的存在量词类型：{}",
                                            i + 1,
                                            e.msg
                                        ))
                                    })?;
                                std_deduce_kernel::check::check_is_type(
                                    &next.env,
                                    &elab::ctx_of(&binds),
                                    &domain,
                                )
                                .map_err(|e| {
                                    LoadError::new(format!(
                                        "`rule {n}` 的前提 {} 的存在量词类型不合法：{e}",
                                        i + 1
                                    ))
                                })?;
                                let mut witness_binds = binds.clone();
                                witness_binds.push((binder.clone(), domain.clone()));
                                let body =
                                    elab::elab(&next.env, &witness_binds, body).map_err(|e| {
                                        LoadError::new(format!(
                                            "`rule {n}` 的前提 {} 的存在量词体：{}",
                                            i + 1,
                                            e.msg
                                        ))
                                    })?;
                                std_deduce_kernel::check::check(
                                    &next.env,
                                    &elab::ctx_of(&witness_binds),
                                    &body,
                                    &Expr::Sort(0),
                                )
                                .map_err(|e| {
                                    LoadError::new(format!(
                                        "`rule {n}` 的前提 {} 的存在量词体不是命题：{e}",
                                        i + 1
                                    ))
                                })?;
                                PremiseKind::Exists {
                                    binder: witness,
                                    domain,
                                    body,
                                }
                            }
                        };
                        let premise = PremiseDecl {
                            name: p.name.as_ref().map(std_deduce_kernel::name),
                            kind,
                        };
                        let bind = premise.binder_or(i);
                        if matches!(premise.kind, PremiseKind::Plain(_)) {
                            binds.push((bind.to_string(), premise.kernel_type()));
                        }
                        rule_premises.push(premise);
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

                    // Pleading clauses on the exceptions are vacuous without an
                    // exception to plead: refuse the declaration instead of
                    // storing metadata that can never be read.
                    if unlesses.is_empty()
                        && (exception_burden.is_some() || exception_standard.is_some())
                    {
                        return Err(LoadError::new(format!(
                            "`rule {n}`：`exception_burden`/`exception_standard` 只对带 `unless` 的规则有意义，该规则没有例外"
                        )));
                    }

                    // Guards are instance conditions over the parameter values.
                    // Their checks run here, with the clause's own position, so
                    // a rejection points at the `guard` line in the rule that
                    // must be fixed; the kernel re-checks the same properties
                    // for environments built without this loader.
                    let mut rule_guards = Vec::new();
                    for (i, guard) in guards.iter().enumerate() {
                        let what = format!("`rule {n}` 的第 {} 条 guard 守卫", i + 1);
                        let at = |msg: String| {
                            LoadError::at(format!("{what}：{msg}"), guard.line, guard.col)
                        };
                        let mut free = Vec::new();
                        collect_free_names(&guard.term, &mut Vec::new(), &mut free);
                        for ident in &free {
                            // Locals shadow environment constants, in this
                            // order: a parameter is a value the instance binds.
                            if params.iter().any(|(pn, _)| pn == ident) {
                                // A parameter only used by a guard is never
                                // bound by the instance; the premise check in
                                // the kernel would report it later, without a
                                // position, so it is caught here with one.
                                let in_premise = premises
                                    .iter()
                                    .any(|p| premise_constrains_ident(&p.kind, ident));
                                if !in_premise {
                                    return Err(at(format!(
                                        "参数 `{ident}` 出现在守卫里，但没有出现在任何前提里：\
                                         实例化时它的值无法被确定，守卫不能判定。\
                                         请把它纳入某条前提（或把它从守卫里去掉）"
                                    )));
                                }
                                continue;
                            }
                            let is_premise_binder =
                                premises.iter().enumerate().any(|(j, p)| match &p.name {
                                    Some(pn) => pn == ident,
                                    None => format!("_p{j}") == *ident,
                                });
                            if is_premise_binder {
                                return Err(at(format!(
                                    "守卫引用了前提绑定 `{ident}`：守卫只能判定规则参数的值，\
                                     不能判定前提的证明；请改用参数，或把该条件写成 premise"
                                )));
                            }
                            if next.env.contains(ident)
                                || std_deduce_kernel::builtin::type_of(ident).is_some()
                            {
                                continue;
                            }
                            return Err(at(format!(
                                "守卫里有未绑定的自由变量 `{ident}`：守卫只能引用规则参数\
                                 或已声明的项（闭项），不能引用既没有声明、也没有被规则绑定的名字"
                            )));
                        }
                        let e =
                            elab::elab(&next.env, &binds, &guard.term).map_err(|e| at(e.msg))?;
                        if std_deduce_kernel::builtin::comparison_head(&e).is_none() {
                            return Err(at(
                                "守卫必须以比较 `less` / `le` 打头（例如 `(le a 5000)`）；\
                                 `guard 3000` 这类表达式不是比较，既不产生真值，也不能决定规则是否触发"
                                    .to_string(),
                            ));
                        }
                        std_deduce_kernel::check::check(
                            &next.env,
                            &elab::ctx_of(&binds),
                            &e,
                            &Expr::Sort(0),
                        )
                        .map_err(|e| at(format!("守卫不是命题：{e}")))?;
                        rule_guards.push(e);
                    }

                    let rdecl = std_deduce_kernel::RuleDecl {
                        params: rule_params,
                        premises: rule_premises,
                        conclusion: concl,
                        unlesses,
                        guards: rule_guards,
                        exceptions,
                        prefers,
                        revision: revision_group,
                        sources: sources.iter().map(|s| to_source((*s).clone())).collect(),
                        declared_in: namespace.as_ref().map(std_deduce_kernel::name),
                        // The pleading clauses are declaration metadata: they
                        // are stored as written (or left undeclared) and are
                        // not read by the reasoner or the certificate.
                        burden,
                        standard,
                        exception_burden,
                        exception_standard,
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
                    if let Some(rev) = revision {
                        revision_claims.push((n.clone(), rev));
                    }
                    report.declared.push(n);
                }
                Item::Interpretation {
                    name: n,
                    from,
                    to,
                    direction,
                    sources,
                } => {
                    // An interpretation is a named, sourced claim. The
                    // loader only registers it as an opaque constant of type
                    // `from → to`: whether the reasoner applies it is the
                    // query's explicit decision (`--interpret` /
                    // `:interpret enable`), never a loading side effect.
                    // The parser already requires at least one `source` line
                    // and non-empty text/locator/version, so the loader does
                    // not repeat that line-oriented check. What only the
                    // loader can decide is whether both sides are propositions.
                    let efrom = elab::elab_top(&next.env, &from).map_err(|e| {
                        LoadError::new(format!("`interpret {n}` 的 from 无法精化：{}", e.msg))
                    })?;
                    std_deduce_kernel::check::check(
                        &next.env,
                        &std_deduce_kernel::Ctx::new(),
                        &efrom,
                        &Expr::Sort(0),
                    )
                    .map_err(|e| {
                        LoadError::new(format!(
                            "`interpret {n}` 的 from 不是命题（必须是 `Sort 0`）：{e}；\
                             概念到概念的解释尚未支持"
                        ))
                    })?;
                    let eto = elab::elab_top(&next.env, &to).map_err(|e| {
                        LoadError::new(format!("`interpret {n}` 的 to 无法精化：{}", e.msg))
                    })?;
                    std_deduce_kernel::check::check(
                        &next.env,
                        &std_deduce_kernel::Ctx::new(),
                        &eto,
                        &Expr::Sort(0),
                    )
                    .map_err(|e| {
                        LoadError::new(format!(
                            "`interpret {n}` 的 to 不是命题（必须是 `Sort 0`）：{e}；\
                             概念到概念的解释尚未支持"
                        ))
                    })?;
                    let interpretation = std_deduce_kernel::env::Interpretation {
                        name: std_deduce_kernel::name(&n),
                        from: efrom.clone(),
                        to: eto.clone(),
                        direction,
                        sources: sources.iter().map(|s| to_source((*s).clone())).collect(),
                    };
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Interpretation(Box::new(interpretation)),
                        // The readable type of the opaque constant. It is a
                        // proposition (`from → to` in `Sort 0`), so the
                        // kernel's sort check accepts it; being opaque, it
                        // proves nothing on its own.
                        ty: Expr::pi(efrom, eto),
                        sources: sources.iter().map(|s| to_source((*s).clone())).collect(),
                        occurred_at: None,
                        occurred_in: None,
                        scope: Default::default(),
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError::new(format!("`interpret {n}`：{e}")))?;
                    theory.decls.push(n.clone());
                    report.declared.push(n);
                }
                Item::Check(t) => {
                    let e = elab::elab_top(&next.env, &t).map_err(|e| LoadError::new(e.msg))?;
                    let ty = std_deduce_kernel::check::infer(
                        &next.env,
                        &std_deduce_kernel::Ctx::new(),
                        &e,
                    )
                    .map_err(|e| LoadError::new(e.to_string()))?;
                    // Arithmetic is a computation, not a label: checking a term
                    // evaluates the built-in operations in it, so an i64
                    // overflow is reported here instead of surviving as an
                    // unevaluated expression that only fails later in a query.
                    let evaluated = std_deduce_kernel::norm::evaluate_arithmetic(&next.env, &e)
                        .map_err(|error| {
                            LoadError::new(format!("`#check` 的项做算术求值时出错：{error}"))
                        })?;
                    let mut line = format!(
                        "{} : {}",
                        std_deduce_kernel::pretty::print_expr(&e),
                        std_deduce_kernel::pretty::print_expr(&ty)
                    );
                    if evaluated != e {
                        line.push_str(&format!(
                            "（求值：{}）",
                            std_deduce_kernel::pretty::print_expr(&evaluated)
                        ));
                    }
                    report.checked.push(line);
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
                    // A proposition may contain a comparison or an arithmetic
                    // expression; evaluate it for the same reason as `#check`:
                    // overflow is a load error, not a neutral term.
                    let evaluated = std_deduce_kernel::norm::evaluate_arithmetic(&next.env, &e)
                        .map_err(|error| {
                            LoadError::new(format!("`#proposition` 的项做算术求值时出错：{error}"))
                        })?;
                    let mut line = format!("命题：{}", std_deduce_kernel::pretty::print_expr(&e));
                    if evaluated != e {
                        line.push_str(&format!(
                            "（求值：{}）",
                            std_deduce_kernel::pretty::print_expr(&evaluated)
                        ));
                    }
                    report.checked.push(line);
                }
                Item::Show(n) => {
                    if let Some(d) = next.env.get(&n) {
                        // A definition is a macro, so `#show` prints its body
                        // as well as its type: the expansion is never hidden.
                        let shown = match &d.kind {
                            std_deduce_kernel::DeclKind::Def { body } => format!(
                                "{} : {} := {}",
                                d.name,
                                std_deduce_kernel::pretty::print_expr(&d.ty),
                                std_deduce_kernel::pretty::print_expr(body)
                            ),
                            _ => format!(
                                "{} : {}",
                                d.name,
                                std_deduce_kernel::pretty::print_expr(&d.ty)
                            ),
                        };
                        report.shown.push(shown);
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

        // An `open` marker may name a predicate declared later in the same
        // file, so its target is checked against the completed environment.
        // The marker itself was inserted immediately (it has no term to
        // elaborate), which keeps `:inspect` in source order.
        // A predicate can be marked only once. Targets are validated first so
        // a repeated `open 不存在` reports the unknown predicate, not a
        // duplicate marker; an open concept must be one declaration a reader
        // can point at.
        let mut marked: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        for (pred, line, col) in &open_concepts {
            let p = std_deduce_kernel::name(pred);
            match next.env.get(&p) {
                Some(d) if matches!(d.kind, std_deduce_kernel::DeclKind::Pred) => {}
                Some(_) => {
                    return Err(LoadError::at(
                        format!("`open {pred}`：`{p}` 不是谓词（pred）"),
                        *line,
                        *col,
                    ))
                }
                None => {
                    return Err(LoadError::at(
                        format!("`open {pred}`：未知谓词 `{p}`"),
                        *line,
                        *col,
                    ))
                }
            }
            if next.env.open_predicates().iter().any(|open| open == &p) {
                return Err(LoadError::at(
                    format!(
                        "`open {pred}`：谓词 `{p}` 已经标记为开放概念（重复）；\
                         一个谓词只能声明一次 open"
                    ),
                    *line,
                    *col,
                ));
            }
            if !marked.insert(p.to_string()) {
                return Err(LoadError::at(
                    format!(
                        "`open {pred}`：谓词 `{p}` 已经标记为开放概念（重复）；\
                         一个谓词只能声明一次 open"
                    ),
                    *line,
                    *col,
                ));
            }
        }
        for (pred, line, col) in &open_concepts {
            let p = std_deduce_kernel::name(pred);
            let decl = Decl {
                name: std_deduce_kernel::name(format!("open:{pred}")),
                kind: std_deduce_kernel::DeclKind::OpenConcept { pred: p },
                // The marker is metadata, not a claim: its constant has type
                // `Type`, so the kernel never treats it as a proposition.
                ty: Expr::Sort(1),
                sources: Vec::new(),
                scope: Scope::default(),
                occurred_at: None,
                occurred_in: None,
                index: 0,
            };
            next.env
                .insert(decl, &std_deduce_kernel::Ctx::new())
                .map_err(|e| LoadError::at(format!("`open {pred}`：{e}"), *line, *col))?;
            theory.decls.push(format!("open:{pred}"));
            report.declared.push(format!("open {pred}"));
        }
        // A `risk` marker names a theme its predicate belongs to. One predicate
        // carries at most one theme, so a reader can point at exactly one
        // declaration; the target is validated first so `risk 刑事 不存在`
        // reports the unknown predicate, and an unknown theme keyword is an
        // error rather than a silently ignored marker.
        let mut marked_risk: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        let mut risk_markers: Vec<(std_deduce_kernel::RiskTheme, String, usize, usize)> =
            Vec::new();
        for (theme, pred, line, col) in &risk_themes {
            let Some(parsed) = std_deduce_kernel::RiskTheme::parse(theme) else {
                return Err(LoadError::at(
                    format!(
                        "`risk {theme} {pred}`：未知风险类别 `{theme}`；可选：{}",
                        std_deduce_kernel::RiskTheme::keywords().join(" / ")
                    ),
                    *line,
                    *col,
                ));
            };
            let p = std_deduce_kernel::name(pred);
            match next.env.get(&p) {
                Some(d) if matches!(d.kind, std_deduce_kernel::DeclKind::Pred) => {}
                Some(_) => {
                    return Err(LoadError::at(
                        format!("`risk {theme} {pred}`：`{p}` 不是谓词（pred）"),
                        *line,
                        *col,
                    ))
                }
                None => {
                    return Err(LoadError::at(
                        format!("`risk {theme} {pred}`：未知谓词 `{p}`"),
                        *line,
                        *col,
                    ))
                }
            }
            if next
                .env
                .risk_markers()
                .iter()
                .any(|(marked, _)| marked == &p)
            {
                return Err(LoadError::at(
                    format!(
                        "`risk {theme} {pred}`：谓词 `{p}` 已经标记了风险题材（重复）；\
                         一个谓词只能声明一次 risk"
                    ),
                    *line,
                    *col,
                ));
            }
            if !marked_risk.insert(p.to_string()) {
                return Err(LoadError::at(
                    format!(
                        "`risk {theme} {pred}`：谓词 `{p}` 已经标记了风险题材（重复）；\
                         一个谓词只能声明一次 risk"
                    ),
                    *line,
                    *col,
                ));
            }
            risk_markers.push((parsed, pred.clone(), *line, *col));
        }
        for (theme, pred, line, col) in &risk_markers {
            let p = std_deduce_kernel::name(pred);
            let decl = Decl {
                name: std_deduce_kernel::name(format!("risk:{pred}")),
                kind: std_deduce_kernel::DeclKind::Risk {
                    theme: *theme,
                    pred: p,
                },
                // The marker is metadata, not a claim: its constant has type
                // `Type`, so the kernel never treats it as a proposition.
                ty: Expr::Sort(1),
                sources: Vec::new(),
                scope: Scope::default(),
                occurred_at: None,
                occurred_in: None,
                index: 0,
            };
            next.env
                .insert(decl, &std_deduce_kernel::Ctx::new())
                .map_err(|e| {
                    LoadError::at(
                        format!("`risk {} {pred}`：{e}", theme.keyword()),
                        *line,
                        *col,
                    )
                })?;
            theory.decls.push(format!("risk:{pred}"));
            report
                .declared
                .push(format!("risk {} {pred}", theme.keyword()));
        }
        // A `defeated_by` / `prefer` name is stored as an opaque string, so a
        // typo would silently disable the intended priority. Validate the
        // targets after the whole file is in the environment, which allows a
        // rule to name a rule declared later in the same file.
        check_rule_targets(&next.env, &theory.rules).map_err(LoadError::new)?;
        // A `revision` clause groups rules that are versions of one provision.
        // The one check that belongs to a file is the declaration name space:
        // the identifier is a label and must not name an existing declaration.
        // Group completeness is not checked here — a law pack may split one
        // provision's versions across theory files, so a single file is allowed
        // to contain only some members of a group. The environment-wide check
        // runs at the end of the whole load transaction
        // ([`Library::check_revision_groups`]).
        check_revision_declarations(&next.env, &revision_claims)?;
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
            | Item::Open { .. }
            | Item::Risk { .. }
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

/// The per-file half of the `revision` checks: the group identifier is a
/// declaration label, so it must not name an existing declaration.
///
/// Grouping is a declaration, never an inference. This check runs when a file
/// has been loaded into the environment (so the identifier may name a
/// declaration made later in the same file) and reports at the `revision`
/// clause. Group *completeness* is deliberately not checked here: a law pack
/// may split one provision's versions across theory files, so a single file is
/// allowed to contain only some members of a group. Completion runs once at
/// the end of the whole load transaction
/// ([`Library::check_revision_groups`]).
fn check_revision_declarations(
    env: &Env,
    claims: &[(String, crate::ast::Revision)],
) -> Result<(), LoadError> {
    for (rule, revision) in claims {
        let rule_name = std_deduce_kernel::name(rule);
        let Some(group) = env.revision_group_of(&rule_name) else {
            return Err(LoadError::at(
                format!(
                    "`rule {rule}` 的 `revision {}`：内部状态不一致，规则声明里没有记录该组",
                    revision.id
                ),
                revision.line,
                revision.col,
            ));
        };
        if let Some(existing) = revision_name_clash(env, &group) {
            return Err(LoadError::at(
                format!(
                    "`rule {rule}` 的 `revision {}`：组标识不得与已声明规则名/谓词冲突；\
                     `{}` 已声明为 `{}`。`revision` 标识与其他声明共用一个名字空间",
                    revision.id,
                    existing.name,
                    decl_kind_label(&existing.kind)
                ),
                revision.line,
                revision.col,
            ));
        }
    }
    Ok(())
}

/// Check every `revision` group of the completed environment.
///
/// This is the transaction-level check, not a per-file one: a law pack may
/// split one provision's versions across several theory files (a file holding a
/// single version is normal), so the group's completeness can only be judged
/// once the whole load transaction is finished. `claims` are the `revision`
/// clauses written by the file just loaded; they are used only to attach source
/// positions to errors, and are empty for a check that covers other files too.
///
/// A group must have at least two members (one rule is not a set of versions),
/// must not contain two members with the same rule name, and every member must
/// declare an effective range (a pack rule may inherit it from the manifest):
/// the range is what the applicability judgement uses to tell the versions
/// apart. The identifier must not name an existing declaration; that check is
/// repeated here so a declaration loaded in a later file of the same
/// transaction cannot take the identifier's place.
///
/// Errors name the group and the rule; they carry a source position when the
/// clause was written by the file being reported.
fn check_revision_groups(
    env: &Env,
    claims: &[(String, crate::ast::Revision)],
) -> Result<(), LoadError> {
    for (group, members) in env.revision_groups() {
        if let Some(existing) = revision_name_clash(env, &group) {
            let rule = members.first().map(|member| member.as_ref()).unwrap_or("");
            let message = format!(
                "`rule {rule}` 的 `revision {}`：组标识不得与已声明规则名/谓词冲突；\
                 `{}` 已声明为 `{}`。`revision` 标识与其他声明共用一个名字空间",
                group.revision,
                existing.name,
                decl_kind_label(&existing.kind)
            );
            return Err(revision_error(claims, rule, message));
        }
        if members.len() < 2 {
            return Err(LoadError::new(format!(
                "组 `{}` 只声明了 {} 个成员，历史版本至少需要 2 个；其余版本应与本次加载一起提供",
                group.label(),
                members.len()
            )));
        }
        let mut seen: Vec<&std_deduce_kernel::Name> = Vec::new();
        for member in &members {
            if seen.iter().any(|other| other == &member) {
                return Err(revision_error(
                    claims,
                    member,
                    format!(
                        "`rule {member}` 属于组 `{}`：同一 revision 组内不能有同名规则",
                        group.label()
                    ),
                ));
            }
            seen.push(member);
            let effective_missing = env
                .get(member)
                .is_some_and(|decl| decl.scope.effective_from.is_none());
            if effective_missing {
                return Err(revision_error(
                    claims,
                    member,
                    format!(
                        "`rule {member}` 属于组 `{}`：历史版本必须声明生效区间；\
                         请写 `effective <YYYY-MM-DD>`（有失效日再写 `repealed`），\
                         包内规则也可由清单提供起点——没有生效区间就无法把两个版本放在时间轴上比较",
                        group.label()
                    ),
                ));
            }
        }
    }
    Ok(())
}

/// The load error at the `revision` clause of `rule`, when this load wrote one,
/// and without a position otherwise.
fn revision_error(
    claims: &[(String, crate::ast::Revision)],
    rule: &str,
    message: String,
) -> LoadError {
    match claims
        .iter()
        .find(|(declared, _)| declared == rule)
        .map(|(_, revision)| revision)
    {
        Some(revision) => LoadError::at(message, revision.line, revision.col),
        None => LoadError::new(message),
    }
}

/// An existing declaration whose name equals the revision identifier, in the
/// bare form or, for a module's group, in its qualified form.
fn revision_name_clash<'a>(
    env: &'a Env,
    group: &std_deduce_kernel::RevisionGroup,
) -> Option<&'a std_deduce_kernel::Decl> {
    let revision = group.revision.as_ref();
    if let Some(decl) = env.get(revision) {
        return Some(decl);
    }
    let std_deduce_kernel::RevisionScope::Namespace(namespace) = &group.scope else {
        return None;
    };
    env.get(&format!("{namespace}.{revision}"))
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
        Term::Prop | Term::Type(_) | Term::Num(_) => Ok(()),
        Term::Ident(s) => {
            // An identifier bound in the local telescope, the `_` wildcard, or
            // a kernel built-in (`Int`, `add`, …) needs no namespace prefix:
            // built-ins belong to no module.
            if s == "_"
                || locals.iter().any(|local| local == s)
                || std_deduce_kernel::builtin::type_of(s).is_some()
            {
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

/// The load error for a declaration name that is already in the ledger.
///
/// Every declaration kind shares one name space. The message names the
/// declaration that tried to reuse the name, the existing kind, and the
/// source position; it keeps the kernel's own phrase (`名称已被占用`) so the
/// ledger remains the single authority on name clashes. A duplicate that
/// reaches `Env::insert` anyway is still reported, but without this position.
fn decl_name_clash(
    env: &Env,
    written: &str,
    keyword: &str,
    line: usize,
    col: usize,
) -> Option<LoadError> {
    let existing = env.get(written)?;
    Some(LoadError::at(
        format!(
            "`{keyword} {written}`：名称已被占用：`{written}`（已声明为 `{}`）；\
             所有声明共用同一个名字空间，不能与任何已有声明重名",
            decl_kind_label(&existing.kind)
        ),
        line,
        col,
    ))
}

/// The surface keyword of a declaration kind, for a name-clash diagnostic.
fn decl_kind_label(kind: &std_deduce_kernel::DeclKind) -> &'static str {
    use std_deduce_kernel::DeclKind;
    match kind {
        DeclKind::Sort => "sort",
        DeclKind::Obj => "obj",
        DeclKind::Pred => "pred",
        DeclKind::Axiom => "axiom",
        DeclKind::Fact { .. } => "fact",
        DeclKind::Def { .. } => "def",
        DeclKind::Rule(_) => "rule",
        DeclKind::Interpretation(_) => "interpret",
        DeclKind::Contrary { .. } => "contrary",
        DeclKind::Unique { .. } => "unique",
        DeclKind::Priority { .. } => "priority",
        DeclKind::OpenConcept { .. } => "open",
        DeclKind::Risk { .. } => "risk",
    }
}

/// Every name a definition's body mentions without a local binder and without
/// an already-loaded declaration to supply it.
///
/// A `def` is a macro the kernel unfolds by delta, so the body has to be
/// closed over the ledger as it stands when the declaration is loaded. There
/// are only two fixes, and both are explicit: bind the name with a λ/∀ (a
/// parameter), or declare it first. This is why a definition cannot be
/// recursive (it is not in the ledger yet) and cannot refer forward (a
/// tempting mutual recursion, which would make delta unfolding diverge).
fn check_definition_body(name: &str, body: &Term, env: &Env) -> Result<(), String> {
    let mut free = Vec::new();
    collect_free_names(body, &mut Vec::new(), &mut free);
    if free.iter().any(|ident| ident == name) {
        return Err(format!(
            "定义不能递归：`def {name}` 的定义体引用了它自己；\
             参数请用 λ 绑定，展开由内核的 delta 规则完成"
        ));
    }
    for ident in &free {
        // A kernel built-in (`Int`, `add`, `less`, …) is part of the trusted
        // core and needs no declaration, so a definition body may mention it
        // without it being in the ledger.
        if !env.contains(ident) && std_deduce_kernel::builtin::type_of(ident).is_none() {
            return Err(format!(
                "`def {name}` 的定义体里有未绑定的名字 `{ident}`：\
                 定义体的自由变量必须被 λ/∀ 绑定，其余名字必须是已声明的项；\
                 定义不能引用自身或尚未声明的名字（递归与前向互引用都不允许）"
            ));
        }
    }
    Ok(())
}

/// Does this term mention `ident` outside its own `λ` / `∀` binders?
///
/// Used to decide whether a rule parameter that a guard reads is fixed by some
/// premise: a name bound inside the term itself does not count as the rule
/// parameter's occurrence.
fn term_mentions_ident(term: &Term, ident: &str) -> bool {
    let mut free = Vec::new();
    collect_free_names(term, &mut Vec::new(), &mut free);
    free.iter().any(|name| name == ident)
}

/// Does one premise guarantee a value for `ident` regardless of the branch or
/// witness chosen?
///
/// A plain premise mentions it; a disjunctive premise only guarantees it when
/// every branch mentions it; an existential premise mentions it through its
/// body. The witness binder itself is local to the body, so a parameter that
/// appears only in the domain of an existential premise is not constrained (a
/// domain is a type, not a proposition matched against facts).
fn premise_constrains_ident(kind: &AstPremiseKind, ident: &str) -> bool {
    match kind {
        AstPremiseKind::Plain(term) => term_mentions_ident(term, ident),
        AstPremiseKind::Or(branches) => branches
            .iter()
            .all(|branch| term_mentions_ident(branch, ident)),
        AstPremiseKind::Exists { body, .. } => term_mentions_ident(body, ident),
    }
}

fn collect_free_names(term: &Term, bound: &mut Vec<String>, out: &mut Vec<String>) {
    match term {
        Term::Prop | Term::Type(_) | Term::Num(_) => {}
        Term::Ident(name) => {
            if !bound.iter().any(|binder| binder == name) && !out.iter().any(|seen| seen == name) {
                out.push(name.clone());
            }
        }
        Term::Pi {
            name,
            domain,
            codomain,
        } => {
            collect_free_names(domain, bound, out);
            if let Some(binder) = name {
                bound.push(binder.clone());
                collect_free_names(codomain, bound, out);
                bound.pop();
            } else {
                collect_free_names(codomain, bound, out);
            }
        }
        Term::Lam { name, domain, body } => {
            collect_free_names(domain, bound, out);
            bound.push(name.clone());
            collect_free_names(body, bound, out);
            bound.pop();
        }
        Term::App(func, arg) => {
            collect_free_names(func, bound, out);
            collect_free_names(arg, bound, out);
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
    guards: &[crate::ast::Guard],
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
        match &premise.kind {
            AstPremiseKind::Plain(term) => check_term(ns, &what, &locals, term)?,
            AstPremiseKind::Or(branches) => {
                for (j, branch) in branches.iter().enumerate() {
                    let what = format!("{what} 的第 {} 个析取分支", j + 1);
                    check_term(ns, &what, &locals, branch)?;
                }
            }
            AstPremiseKind::Exists {
                binder,
                domain,
                body,
            } => {
                let what_domain = format!("{what} 的存在量词类型");
                check_term(ns, &what_domain, &locals, domain)?;
                locals.push(binder.clone());
                let what_body = format!("{what} 的存在量词体");
                let body_result = check_term(ns, &what_body, &locals, body);
                locals.pop();
                body_result?;
            }
        }
        // A named plain premise binds its name; an unnamed one is opened by the
        // elaborator as the generated local `_p{i}`. Compound premises are
        // logical side conditions, not telescope binders, and the witness
        // binder of an existential premise is local to its body.
        if matches!(premise.kind, AstPremiseKind::Plain(_)) {
            match &premise.name {
                Some(binder) => locals.push(binder.clone()),
                None => locals.push(format!("_p{i}")),
            }
        }
    }
    let what = format!("`rule {name}` 的结论");
    check_term(ns, &what, &locals, conclusion)?;
    for (i, guard) in guards.iter().enumerate() {
        let what = format!("`rule {name}` 的第 {} 条 guard 守卫", i + 1);
        check_term(ns, &what, &locals, &guard.term)?;
    }
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
                guards,
                ..
            } => {
                require_decl_name(ns, "rule", name)?;
                check_rule(ns, name, params, premises, conclusion, defeaters, guards)?;
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
            Item::Open { pred, .. } => {
                let what = format!("`open {pred}`");
                require_qualified_ref(ns, &what, pred)?;
            }
            Item::Risk { theme, pred, .. } => {
                let what = format!("`risk {theme} {pred}`");
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
/// A written `repealed` may take its start from the manifest as well, so the
/// range is validated **after** merging: it must have a start and the end must
/// be later than it. The comparison is a plain string compare, which is correct
/// for validated `YYYY-MM-DD` values.
///
/// Each present field keeps its own origin (`Rule` if the rule wrote it,
/// `PackDefault` if it came from the manifest), so `:inspect` can distinguish a
/// written value from an inherited one. The record-level [`Scope::origin`]
/// remains the summary the original scope contract asked for.
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

    let inherited = if options.case_local {
        None
    } else {
        options.pack_scope.as_ref()
    };
    let effective_from = written
        .effective_from
        .clone()
        .or_else(|| inherited.and_then(|scope| scope.effective_from.clone()));
    let effective_to = written
        .effective_to
        .clone()
        .or_else(|| inherited.and_then(|scope| scope.effective_to.clone()));
    let jurisdiction = written
        .jurisdiction
        .clone()
        .or_else(|| inherited.and_then(|scope| scope.jurisdiction.clone()));
    let territory = written
        .territory
        .clone()
        .or_else(|| inherited.and_then(|scope| scope.territory.clone()));

    // The merged range must be well formed even when one endpoint was
    // inherited: a rule's own `effective 2005` with a manifest end of 2001 is
    // not a record of any interval that can exist.
    if let Some(to) = &effective_to {
        let Some(from) = &effective_from else {
            return Err(format!(
                "`rule {name}`：失效日 `{to}` 没有生效起点；请写 `effective`，或由包清单提供 `effective_from`（案件本地规则不继承清单）"
            ));
        };
        if to <= from {
            return Err(format!(
                "`rule {name}`：合并后的生效区间无效：生效起点 `{from}` 必须早于失效日 `{to}`（`repealed` 不含当天，必须更晚）"
            ));
        }
    }

    let field_origin = |explicit: &Option<String>, merged: &Option<String>| match (explicit, merged)
    {
        (Some(_), _) => merged.as_ref().map(|_| ScopeOrigin::Rule),
        (None, Some(_)) => Some(ScopeOrigin::PackDefault),
        (None, None) => None,
    };
    let origin = if options.case_local {
        ScopeOrigin::CaseLocal
    } else if !written.is_empty() {
        ScopeOrigin::Rule
    } else if options.pack_scope.is_some() {
        ScopeOrigin::PackDefault
    } else {
        ScopeOrigin::Unspecified
    };
    Ok(Scope {
        effective_from_origin: field_origin(&written.effective_from, &effective_from),
        effective_to_origin: field_origin(&written.effective_to, &effective_to),
        jurisdiction_origin: field_origin(&written.jurisdiction, &jurisdiction),
        territory_origin: field_origin(&written.territory, &territory),
        effective_from,
        effective_to,
        jurisdiction,
        territory,
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
