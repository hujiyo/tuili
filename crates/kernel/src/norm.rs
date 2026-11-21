//! Normalisation.
//!
//! The kernel reduces only what it must: beta, delta for `def`, and zeta for
//! `let`. Predicates, axioms, rules and interpretations stay *opaque*.
//! A rule is not an equation, and unfolding it would be precisely the quiet
//! overreach this kernel refuses to make.

use crate::env::{Ctx, DeclKind, Env};
use crate::error::Result;
use crate::term::{instantiate, Expr};

/// Weak head normal form: reduce until the head is not a redex.
///
/// No context is needed: beta and zeta substitute immediately, and a `def`'s
/// body is closed, so unfolding never looks at the local binders.
pub fn whnf(env: &Env, e: &Expr) -> Result<Expr> {
    let mut e = e.clone();
    loop {
        match e {
            Expr::App { func, arg } => {
                let f = whnf(env, &func)?;
                match f {
                    Expr::Lam { body, .. } => {
                        e = instantiate(&body, &arg);
                    }
                    head => {
                        let rebuilt = Expr::App {
                            func: Box::new(head),
                            arg,
                        };
                        match unfold(env, &rebuilt)? {
                            Some(u) => e = u,
                            None => return Ok(rebuilt),
                        }
                    }
                }
            }
            Expr::Let { value, body, .. } => e = instantiate(&body, &value),
            Expr::Const(_) => match unfold(env, &e)? {
                Some(u) => e = u,
                None => return Ok(e),
            },
            other => return Ok(other),
        }
    }
}

/// Full normal form.
pub fn normalize(env: &Env, ctx: &Ctx, e: &Expr) -> Result<Expr> {
    let e = whnf(env, e)?;
    Ok(match e {
        Expr::App { .. } => {
            let (head, args) = spine(&e);
            let mut out = normalize(env, ctx, head)?;
            for a in args {
                out = Expr::app(out, normalize(env, ctx, a)?);
            }
            out
        }
        Expr::Pi {
            name,
            domain,
            codomain,
        } => {
            let mut inner = ctx.clone();
            inner.push(name.clone(), domain.as_ref().clone());
            Expr::Pi {
                domain: Box::new(normalize(env, ctx, &domain)?),
                codomain: Box::new(normalize(env, &inner, &codomain)?),
                name,
            }
        }
        Expr::Lam { name, domain, body } => {
            let mut inner = ctx.clone();
            inner.push(name.clone(), domain.as_ref().clone());
            Expr::Lam {
                domain: Box::new(normalize(env, ctx, &domain)?),
                body: Box::new(normalize(env, &inner, &body)?),
                name,
            }
        }
        other => other,
    })
}

/// Only `def` unfolds. Returns `None` for anything else, including a `def`
/// that is not yet applied to enough arguments.
fn unfold(env: &Env, e: &Expr) -> Result<Option<Expr>> {
    let (head, args) = spine(e);
    let Expr::Const(n) = head else {
        return Ok(None);
    };
    let Some(decl) = env.get(n) else {
        return Ok(None);
    };
    let DeclKind::Def { body } = &decl.kind else {
        return Ok(None);
    };
    Ok(Some(
        args.into_iter()
            .fold(body.clone(), |acc, a| Expr::app(acc, a.clone())),
    ))
}

/// Split `f a b` into `(f, [a, b])`.
pub fn spine(e: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut cur = e;
    while let Expr::App { func, arg } = cur {
        args.push(arg.as_ref());
        cur = func.as_ref();
    }
    args.reverse();
    (cur, args)
}
