//! Theory files: a named unit of declarations.
//!
//! A `Theory` is not a kernel object. It is a *documentation and audit*
//! device: it records that a group of declarations were formalised together,
//! from which source, and by whom. The kernel sees only the flat ledger,
//! which is what keeps the trusted core small.

use std_deduce_kernel::env::{Decl, Env, SourceRef};
use std_deduce_kernel::{Error, Expr};

use crate::ast::Item;
use crate::elab;
use crate::parser;

#[derive(Debug, Clone, Default)]
pub struct Theory {
    pub name: String,
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
        let items = parser::parse(src).map_err(|e| LoadError { msg: e.to_string() })?;
        let mut next = self.clone();
        let mut theory = Theory {
            name: name.to_string(),
            ..Default::default()
        };
        let mut report = LoadReport::default();

        for item in items {
            match item {
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
                        .map_err(|e| LoadError {
                            msg: format!("`sort {n}`：{e}"),
                        })?;
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
                    let ety = elab::elab_top(&next.env, &ty).map_err(|e| LoadError {
                        msg: format!("`obj {n}`：{}", e.msg),
                    })?;
                    std_deduce_kernel::check::check_is_type(
                        &next.env,
                        &std_deduce_kernel::Ctx::new(),
                        &ety,
                    )
                    .map_err(|e| LoadError {
                        msg: format!("`obj {n}` 的类型必须是类型而不是命题：{e}"),
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
                        .map_err(|e| LoadError {
                            msg: format!("`obj {n}`：{e}"),
                        })?;
                    theory.decls.push(n.clone());
                    report.declared.push(n);
                }
                Item::Pred {
                    name: n,
                    ty,
                    source,
                } => {
                    let ety = elab::elab_top(&next.env, &ty).map_err(|e| LoadError {
                        msg: format!("`pred {n}`：{}", e.msg),
                    })?;
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Pred,
                        ty: ety,
                        sources: source.into_iter().map(to_source).collect(),
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError {
                            msg: format!("`pred {n}`：{e}"),
                        })?;
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
                        return Err(LoadError {
                            msg: format!(
                                "axiom `{n}` 缺少 source 或来源为空白；断言事实必须有出处（法律名称 + 条号，或案件材料）"
                            ),
                        });
                    }
                    let ety = elab::elab_top(&next.env, &ty).map_err(|e| LoadError {
                        msg: format!("`axiom {n}`：{}", e.msg),
                    })?;
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Axiom,
                        ty: ety,
                        sources: source.into_iter().map(to_source).collect(),
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError {
                            msg: format!("`axiom {n}`：{e}"),
                        })?;
                    theory.decls.push(n.clone());
                    report.declared.push(n);
                }
                Item::Def {
                    name: n,
                    ty,
                    body,
                    source,
                } => {
                    let ety = elab::elab_top(&next.env, &ty).map_err(|e| LoadError {
                        msg: format!("`def {n}`：{}", e.msg),
                    })?;
                    let ebody = elab::elab_top(&next.env, &body).map_err(|e| LoadError {
                        msg: format!("`def {n}`：{}", e.msg),
                    })?;
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Def { body: ebody },
                        ty: ety,
                        sources: source.into_iter().map(to_source).collect(),
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError {
                            msg: format!("`def {n}`：{e}"),
                        })?;
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
                                return Err(LoadError {
                                    msg: format!(
                                        "`contrary {left} {right}`：`{p}` 不是谓词（pred）"
                                    ),
                                })
                            }
                            None => {
                                return Err(LoadError {
                                    msg: format!("`contrary {left} {right}`：未知谓词 `{p}`"),
                                })
                            }
                        }
                    }
                    let al = pred_arity(&next.env, &l).unwrap_or(0);
                    let ar = pred_arity(&next.env, &r).unwrap_or(0);
                    if al != ar {
                        return Err(LoadError {
                            msg: format!(
                                "`contrary {left} {right}`：两个谓词的参数个数不同（{al} vs {ar}）"
                            ),
                        });
                    }
                    for (a, b) in next.env.contrary_pairs() {
                        if (a == l && b == r) || (a == r && b == l) {
                            return Err(LoadError {
                                msg: format!("`contrary {left} {right}`：这一对已经声明过了"),
                            });
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
                        .map_err(|e| LoadError {
                            msg: format!("`contrary {left} {right}`：{e}"),
                        })?;
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
                            return Err(LoadError {
                                msg: format!("`unique {pred} {index}`：`{p}` 不是谓词（pred）"),
                            })
                        }
                        None => {
                            return Err(LoadError {
                                msg: format!("`unique {pred} {index}`：未知谓词 `{p}`"),
                            })
                        }
                    }
                    let arity = pred_arity(&next.env, &p).unwrap_or(0);
                    if index == 0 || index > arity {
                        return Err(LoadError {
                            msg: format!(
                                "`unique {pred} {index}`：参数位置超出范围（该谓词有 {arity} 个参数）"
                            ),
                        });
                    }
                    let pos = index - 1;
                    for (q, i) in next.env.unique_positions() {
                        if q == p && i == pos {
                            return Err(LoadError {
                                msg: format!("`unique {pred} {index}`：这一条已经声明过了"),
                            });
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
                        .map_err(|e| LoadError {
                            msg: format!("`unique {pred} {index}`：{e}"),
                        })?;
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
                        return Err(LoadError {
                            msg: format!(
                                "规则 `{n}` 缺少 source 或来源为空白；规则必须有出处（法律名称 + 条号，或案件材料）"
                            ),
                        });
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
                    std_deduce_kernel::env::check_unique_binders(&binder_names).map_err(|e| {
                        LoadError {
                            msg: format!("`rule {n}`：{e}"),
                        }
                    })?;

                    // One telescope elaboration: params and premises are
                    // elaborated in the same growing context, and the
                    // conclusion is elaborated in the full telescope. This
                    // is what lets a later premise mention an earlier one,
                    // and lets the conclusion depend on both.
                    let mut binds: Vec<(String, Expr)> = Vec::new();
                    let mut rule_params: Vec<(std_deduce_kernel::Name, Expr)> = Vec::new();
                    for (pn, pt) in &params {
                        let ty = elab::elab(&next.env, &binds, pt).map_err(|e| LoadError {
                            msg: format!("`rule {n}` 的参数 `{pn}`：{}", e.msg),
                        })?;
                        std_deduce_kernel::check::check_is_type(
                            &next.env,
                            &elab::ctx_of(&binds),
                            &ty,
                        )
                        .map_err(|e| LoadError {
                            msg: format!("`rule {n}` 的参数 `{pn}` 类型不合法：{e}"),
                        })?;
                        binds.push((pn.clone(), ty.clone()));
                        rule_params.push((std_deduce_kernel::name(pn), ty));
                    }

                    let mut rule_premises: Vec<(Option<std_deduce_kernel::Name>, Expr)> =
                        Vec::new();
                    for (i, p) in premises.iter().enumerate() {
                        let ty = elab::elab(&next.env, &binds, &p.ty).map_err(|e| LoadError {
                            msg: format!("`rule {n}` 的前提 {}：{}", i + 1, e.msg),
                        })?;
                        std_deduce_kernel::check::check(
                            &next.env,
                            &elab::ctx_of(&binds),
                            &ty,
                            &Expr::Sort(0),
                        )
                        .map_err(|e| LoadError {
                            msg: format!("`rule {n}` 的前提 {} 不是命题：{e}", i + 1),
                        })?;
                        let bind = p.name.clone().unwrap_or_else(|| format!("_p{i}"));
                        binds.push((bind.clone(), ty.clone()));
                        rule_premises.push((p.name.as_ref().map(std_deduce_kernel::name), ty));
                    }

                    let concl =
                        elab::elab(&next.env, &binds, &conclusion).map_err(|e| LoadError {
                            msg: format!("`rule {n}` 的结论：{}", e.msg),
                        })?;
                    std_deduce_kernel::check::check(
                        &next.env,
                        &elab::ctx_of(&binds),
                        &concl,
                        &Expr::Sort(0),
                    )
                    .map_err(|e| LoadError {
                        msg: format!("`rule {n}` 的结论不是命题：{e}"),
                    })?;

                    let mut unlesses = Vec::new();
                    let mut exceptions = Vec::new();
                    let mut prefers = Vec::new();
                    for d in &defeaters {
                        match d {
                            crate::ast::Defeater::Unless(t) => {
                                let e =
                                    elab::elab(&next.env, &binds, t).map_err(|e| LoadError {
                                        msg: format!("`rule {n}` 的 unless：{}", e.msg),
                                    })?;
                                std_deduce_kernel::check::check(
                                    &next.env,
                                    &elab::ctx_of(&binds),
                                    &e,
                                    &Expr::Sort(0),
                                )
                                .map_err(|e| LoadError {
                                    msg: format!("`rule {n}` 的 unless 不是命题：{e}"),
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
                        .map_err(|e| LoadError {
                            msg: format!("`rule {n}`：{e}"),
                        })?;
                    theory.decls.push(n.clone());
                    theory.rules.push(n.clone());
                    report.declared.push(n);
                }
                Item::Interpretation {
                    name: n,
                    from,
                    to,
                    sources,
                } => {
                    let ef = elab::elab_top(&next.env, &from).map_err(|e| LoadError {
                        msg: format!("`interpret {n}`：{}", e.msg),
                    })?;
                    let et = elab::elab_top(&next.env, &to).map_err(|e| LoadError {
                        msg: format!("`interpret {n}`：{}", e.msg),
                    })?;
                    std_deduce_kernel::check::check(
                        &next.env,
                        &std_deduce_kernel::Ctx::new(),
                        &ef,
                        &std_deduce_kernel::Expr::Sort(0),
                    )
                    .map_err(|e| LoadError {
                        msg: format!("`interpret {n}` 的 from 不是命题：{e}"),
                    })?;
                    std_deduce_kernel::check::check(
                        &next.env,
                        &std_deduce_kernel::Ctx::new(),
                        &et,
                        &std_deduce_kernel::Expr::Sort(0),
                    )
                    .map_err(|e| LoadError {
                        msg: format!("`interpret {n}` 的 to 不是命题：{e}"),
                    })?;
                    let decl = Decl {
                        name: std_deduce_kernel::name(&n),
                        kind: std_deduce_kernel::DeclKind::Interpretation(Box::new(
                            std_deduce_kernel::env::Interpretation {
                                name: std_deduce_kernel::name(&n),
                                from: ef,
                                to: et,
                                sources: sources.iter().map(|s| to_source(s.clone())).collect(),
                            },
                        )),
                        ty: std_deduce_kernel::Expr::Sort(0),
                        sources: sources.iter().map(|s| to_source(s.clone())).collect(),
                        index: 0,
                    };
                    next.env
                        .insert(decl, &std_deduce_kernel::Ctx::new())
                        .map_err(|e| LoadError {
                            msg: format!("`interpret {n}`：{e}"),
                        })?;
                    theory.decls.push(n.clone());
                    report.declared.push(n);
                }
                Item::Check(t) => {
                    let e = elab::elab_top(&next.env, &t).map_err(|e| LoadError { msg: e.msg })?;
                    let ty = std_deduce_kernel::check::infer(
                        &next.env,
                        &std_deduce_kernel::Ctx::new(),
                        &e,
                    )
                    .map_err(|e| LoadError { msg: e.to_string() })?;
                    report.checked.push(format!(
                        "{} : {}",
                        std_deduce_kernel::pretty::print_expr(&e),
                        std_deduce_kernel::pretty::print_expr(&ty)
                    ));
                }
                Item::Assert(t) => {
                    let e = elab::elab_top(&next.env, &t).map_err(|e| LoadError { msg: e.msg })?;
                    std_deduce_kernel::check::check(
                        &next.env,
                        &std_deduce_kernel::Ctx::new(),
                        &e,
                        &std_deduce_kernel::Expr::Sort(0),
                    )
                    .map_err(|e| LoadError {
                        msg: format!("断言不是命题：{e}"),
                    })?;
                    report.checked.push(format!(
                        "断言成立：{}",
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
                        return Err(LoadError {
                            msg: format!("`#show {n}`：未知名称"),
                        });
                    }
                }
                Item::Why(_) | Item::Gap(_) => {
                    return Err(LoadError {
                        msg: "#why / #gap 需要推理引擎，请用独立的推理命令".into(),
                    })
                }
            }
        }

        // Commit only if everything above succeeded.
        if let Some(existing) = next.theories.iter_mut().find(|t| t.name == name) {
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

#[derive(Debug, Clone)]
pub struct LoadError {
    pub msg: String,
}
impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.msg)
    }
}
impl std::error::Error for LoadError {}
impl From<Error> for LoadError {
    fn from(e: Error) -> Self {
        LoadError { msg: e.to_string() }
    }
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
