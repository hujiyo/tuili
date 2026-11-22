//! Theory files: a named unit of declarations.
//!
//! A `Theory` is not a kernel object. It is a *documentation and audit*
//! device: it records that a group of declarations were formalised together,
//! from which source, and by whom. The kernel sees only the flat ledger,
//! which is what keeps the trusted core small.

use std_deduce_kernel::env::{Decl, Env, SourceRef};
use std_deduce_kernel::{Error, Expr};

use crate::ast::{Defeater, Item, Term};
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
    /// Theories this one builds on.
    pub requires: Vec<String>,
}

#[derive(Debug, Clone, Default)]
pub struct Library {
    pub theories: Vec<Theory>,
    pub env: Env,
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
        let items = parser::parse(src).map_err(|e| LoadError::at(e.msg, e.line, e.col))?;
        // The parser guarantees that a `namespace` item, when present, is the
        // first item and appears once. A namespaced file is a module: every
        // declaration name and every reference to a declaration must be
        // qualified. This is checked over the whole file before anything is
        // inserted, so a bad module cannot leave a partial theory behind.
        let namespace = match items.first() {
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
            ..Default::default()
        };
        let mut report = LoadReport::default();

        for item in items {
            match item {
                Item::Namespace(_) => {}
                Item::Sort { name: n, source } => {
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Sort,
                        ty: std_deduce_kernel::Expr::Sort(1),
                        sources: source.into_iter().map(to_source).collect(),
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
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Axiom,
                        ty: ety,
                        sources: source.into_iter().map(to_source).collect(),
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
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError::new(format!("`unique {pred} {index}`：{e}")))?;
                    theory.decls.push(format!("unique:{pred}:{index}"));
                    report.declared.push(format!("unique {pred} {index}"));
                }
                Item::Rule {
                    name: n,
                    params,
                    premises,
                    conclusion,
                    defeaters,
                    sources,
                } => {
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
                    };
                    let ty = std_deduce_kernel::env::rule_type(&rdecl);
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Rule(Box::new(rdecl)),
                        ty,
                        sources: sources.iter().map(|s| to_source((*s).clone())).collect(),
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

        // Commit only if everything above succeeded.
        if let Some(existing) = next.theories.iter_mut().find(|t| t.name == theory_name) {
            existing.decls.extend(theory.decls);
            existing.rules.extend(theory.rules);
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
    /// do not carry one.
    pub fn render(&self, path: &str) -> String {
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
            Item::Namespace(_)
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
                match env.get(target) {
                    Some(target_decl)
                        if matches!(target_decl.kind, std_deduce_kernel::DeclKind::Rule(_)) => {}
                    Some(_) => {
                        return Err(format!(
                            "`rule {rule_name}` 的 {clause} 目标 `{target}` 不是规则；\
                             defeated_by/prefer 必须指向规则"
                        ))
                    }
                    None => {
                        return Err(format!(
                            "`rule {rule_name}` 的 {clause} 目标 `{target}` 不存在；\
                             defeated_by/prefer 必须指向已加载或同文件后声明的规则"
                        ))
                    }
                }
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
            Item::Namespace(_) => {}
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
    use super::LoadError;

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
}
