//! Definitional equality.
//!
//! Both sides are reduced to weak head normal form, then compared
//! structurally, under binders. Function extensionality (η) is applied when
//! one side is a lambda: `f` and `fun x => f x` are the same function.

use crate::env::{Ctx, Env};
use crate::error::Result;
use crate::norm::whnf;
use crate::term::{shift, Expr};

pub fn convertible(env: &Env, ctx: &Ctx, a: &Expr, b: &Expr) -> Result<bool> {
    let a = whnf(env, a)?;
    let b = whnf(env, b)?;
    eq(env, ctx, &a, &b)
}

fn eq(env: &Env, ctx: &Ctx, a: &Expr, b: &Expr) -> Result<bool> {
    match (a, b) {
        (Expr::Sort(x), Expr::Sort(y)) => Ok(x == y),
        (Expr::Var(x), Expr::Var(y)) => Ok(x == y),
        (Expr::Const(x), Expr::Const(y)) => Ok(x == y),
        (
            Expr::Pi {
                domain: d1,
                codomain: c1,
                ..
            },
            Expr::Pi {
                domain: d2,
                codomain: c2,
                ..
            },
        ) => {
            if !convertible(env, ctx, d1, d2)? {
                return Ok(false);
            }
            let mut inner = ctx.clone();
            inner.push(None, d1.as_ref().clone());
            convertible(env, &inner, c1, c2)
        }
        (
            Expr::Lam {
                domain: d1,
                body: b1,
                ..
            },
            Expr::Lam {
                domain: d2,
                body: b2,
                ..
            },
        ) => {
            if !convertible(env, ctx, d1, d2)? {
                return Ok(false);
            }
            let mut inner = ctx.clone();
            inner.push(None, d1.as_ref().clone());
            convertible(env, &inner, b1, b2)
        }
        (Expr::App { func: f1, arg: a1 }, Expr::App { func: f2, arg: a2 }) => {
            Ok(convertible(env, ctx, f1, f2)? && convertible(env, ctx, a1, a2)?)
        }
        // η: `λ x : A. body` equals `f` iff `body` equals `f x` under the
        // binder. The lambda's own domain tells us what to bind.
        (Expr::Lam { domain, body, .. }, other) => {
            let mut inner = ctx.clone();
            inner.push(None, domain.as_ref().clone());
            let x = Expr::Var(0);
            let fx = Expr::app(shift(other, 1, 0), x);
            convertible(env, &inner, body, &fx)
        }
        (other, Expr::Lam { domain, body, .. }) => {
            let mut inner = ctx.clone();
            inner.push(None, domain.as_ref().clone());
            let x = Expr::Var(0);
            let fx = Expr::app(shift(other, 1, 0), x);
            convertible(env, &inner, body, &fx)
        }
        _ => Ok(false),
    }
}
