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
        let items = parser::parse(src).map_err(|e| LoadError {
            msg: e.to_string(),
        })?;
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
                Item::Obj { name: n, ty, source } => {
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
                Item::Pred { name: n, ty, source } => {
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
                Item::Axiom { name: n, ty, source } => {
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
                Item::Rule {
                    name: n,
                    params,
                    premises,
                    conclusion,
                    defeaters,
                    sources,
                } => {
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

                    let mut rule_premises: Vec<(Option<std_deduce_kernel::Name>, Expr)> = Vec::new();
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
                        rule_premises.push((
                            p.name.as_ref().map(|x| std_deduce_kernel::name(x)),
                            ty,
                        ));
                    }

                    let concl = elab::elab(&next.env, &binds, &conclusion).map_err(|e| {
                        LoadError {
                            msg: format!("`rule {n}` 的结论：{}", e.msg),
                        }
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
                                let e = elab::elab(&next.env, &binds, t).map_err(|e| LoadError {
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
                    let ty = std_deduce_kernel::env::rule_type(&rdecl, 0);
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

fn to_source(s: crate::ast::SourceSpec) -> SourceRef {
    SourceRef {
        text: s.text,
        locator: s.locator,
        version: s.version,
        effective: s.effective,
        note: s.note,
    }
}
