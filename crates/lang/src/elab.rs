//! Elaboration: surface syntax into kernel terms.
//!
//! This is the layer that is allowed to be clever. It resolves names against
//! the local context and environment, inserts nothing implicit (there are no
//! implicit arguments yet — a deliberate limit), and reports source positions
//! on failure. Every term it hands to the kernel is then *re-checked* by the
//! kernel; the elaborator's output is never trusted on its own.

use std::collections::HashMap;

use std_deduce_kernel::env::{Ctx, Env};
use std_deduce_kernel::{name, Error, Expr};

use crate::ast::Term;

#[derive(Debug, Clone)]
pub struct ElabError {
    pub msg: String,
}

impl std::fmt::Display for ElabError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.msg)
    }
}
impl std::error::Error for ElabError {}

impl From<Error> for ElabError {
    fn from(e: Error) -> Self {
        ElabError { msg: e.to_string() }
    }
}

type Result<T> = std::result::Result<T, ElabError>;

/// Names visible in the local context, innermost last.
#[derive(Debug, Clone, Default)]
pub struct Locals {
    names: Vec<String>,
}

impl Locals {
    pub fn new() -> Self {
        Locals::default()
    }
    pub fn push(&mut self, n: impl Into<String>) {
        self.names.push(n.into());
    }
    pub fn pop(&mut self) {
        self.names.pop();
    }
    pub fn len(&self) -> usize {
        self.names.len()
    }
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
    /// Resolve a name to a de Bruijn index.
    pub fn lookup(&self, n: &str) -> Option<usize> {
        self.names.iter().rev().position(|x| x == n)
    }
    /// The local names as the kernel context needs them.
    pub fn as_ctx(&self, types: &[Expr]) -> Ctx {
        let mut c = Ctx::new();
        for (i, n) in self.names.iter().enumerate() {
            c.push(Some(name(n)), types[i].clone());
        }
        c
    }
}

/// Elaborate a surface term in a local context and environment.
///
/// `locals` maps visible names to their *types*, in the same order the
/// kernel `Ctx` was built, so the two stay in lockstep.
pub fn elab(env: &Env, locals: &[(String, Expr)], t: &Term) -> Result<Expr> {
    match t {
        Term::Prop => Ok(Expr::Sort(0)),
        Term::Type(None) => Ok(Expr::Sort(1)),
        Term::Type(Some(n)) => Ok(Expr::Sort(n + 1)),
        Term::Ident(s) => {
            // Locals shadow environment constants.
            if let Some(i) = locals.iter().rposition(|(n, _)| n == s) {
                return Ok(Expr::Var(locals.len() - 1 - i));
            }
            // Built-in constants (`Int`, `add`, `less`, …) are part of the
            // kernel, not of the environment ledger, so they are resolved even
            // though no declaration names them. A theory cannot shadow them.
            if env.contains(s) || std_deduce_kernel::builtin::type_of(s).is_some() {
                return Ok(Expr::constant(s));
            }
            Err(ElabError {
                msg: format!("未知名称 `{s}`"),
            })
        }
        Term::Num(value) => Ok(Expr::Num(*value)),
        Term::Pi {
            name,
            domain,
            codomain,
        } => {
            let d = elab(env, locals, domain)?;
            let mut ext = locals.to_vec();
            let n = name.clone().unwrap_or_else(|| "_".into());
            ext.push((n.clone(), d.clone()));
            let c = elab(env, &ext, codomain)?;
            Ok(Expr::Pi {
                name: if name.is_some() {
                    Some(std_deduce_kernel::name(&n))
                } else {
                    None
                },
                domain: Box::new(d),
                codomain: Box::new(c),
            })
        }
        Term::Lam { name, domain, body } => {
            let d = elab(env, locals, domain)?;
            let mut ext = locals.to_vec();
            ext.push((name.clone(), d.clone()));
            let b = elab(env, &ext, body)?;
            Ok(Expr::Lam {
                name: Some(std_deduce_kernel::name(name)),
                domain: Box::new(d),
                body: Box::new(b),
            })
        }
        Term::App(f, a) => {
            let ef = elab(env, locals, f)?;
            let ea = elab(env, locals, a)?;
            Ok(Expr::app(ef, ea))
        }
    }
}

/// Elaborate a type in the empty context.
pub fn elab_top(env: &Env, t: &Term) -> Result<Expr> {
    elab(env, &[], t)
}

fn locals_ctx(locals: &[(String, Expr)]) -> Ctx {
    let mut c = Ctx::new();
    for (n, t) in locals {
        c.push(Some(name(n)), t.clone());
    }
    c
}

/// Build a kernel context from an elaborator telescope.
pub fn ctx_of(locals: &[(String, Expr)]) -> Ctx {
    locals_ctx(locals)
}

/// Convenience: a map from names to kernel expressions, for `#show`.
pub fn collect_locals(locals: &[(String, Expr)]) -> HashMap<String, Expr> {
    locals.iter().cloned().collect()
}
