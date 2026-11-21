//! The typing relation.
//!
//! Bidirectional at the only place it matters: lambdas are *checked* against
//! a function type rather than inferred, because inferring them requires an
//! annotation the kernel does not accept guesses for. Everything else is
//! synthesised and compared by definitional equality.

use crate::conv::convertible;
use crate::env::{Ctx, Env};
use crate::error::{Error, Result};
use crate::norm::whnf;
use crate::term::{instantiate, Expr};

/// Infer the type of `e`.
pub fn infer(env: &Env, ctx: &Ctx, e: &Expr) -> Result<Expr> {
    match e {
        Expr::Sort(l) => Ok(Expr::Sort(l.saturating_add(1))),
        Expr::Var(i) => ctx.type_of(*i),
        Expr::Const(n) => env
            .get(n)
            .map(|d| d.ty.clone())
            .ok_or_else(|| Error::UnknownName(n.to_string())),
        Expr::Pi {
            name,
            domain,
            codomain,
        } => {
            let d = infer_sort(env, ctx, domain)?;
            let mut inner = ctx.clone();
            inner.push(name.clone(), domain.as_ref().clone());
            let c = infer_sort(env, &inner, codomain)?;
            // Prop is *impredicative*: if the codomain is a proposition, the
            // product is a proposition too, whatever universe the domain
            // lives in. That is what lets 「凡公民皆有受教育权」 — a quantifier
            // over individuals — be a proposition rather than a Type.
            //
            // Above Prop the hierarchy stays predicative: `Type n` only
            // quantifies over smaller universes, so `Sort-in-Sort` remains
            // impossible.
            Ok(Expr::Sort(if c == 0 { 0 } else { c.max(d) }))
        }
        Expr::Lam { name, domain, body } => {
            // An annotated lambda can be inferred: the annotation supplies
            // the domain, and the codomain is the body's type re-closed
            // under the same binder. Un-annotated lambdas are the only
            // case the kernel refuses, and it says so.
            check_is_type(env, ctx, domain)?;
            let mut inner = ctx.clone();
            inner.push(name.clone(), domain.as_ref().clone());
            let body_ty = infer(env, &inner, body)?;
            Ok(Expr::Pi {
                name: name.clone(),
                domain: domain.clone(),
                codomain: Box::new(body_ty),
            })
        }
        Expr::App { func, arg } => {
            let f_ty = whnf(env, &infer(env, ctx, func)?)?;
            match f_ty {
                Expr::Pi {
                    domain, codomain, ..
                } => {
                    check(env, ctx, arg, &domain)?;
                    Ok(instantiate(&codomain, arg))
                }
                other => Err(Error::NotAFunction(other)),
            }
        }
        Expr::Let { value, body, .. } => {
            let v_ty = infer(env, ctx, value)?;
            let mut inner = ctx.clone();
            inner.push(None, v_ty);
            infer(env, &inner, body)
        }
    }
}

/// Check `e : ty`.
pub fn check(env: &Env, ctx: &Ctx, e: &Expr, ty: &Expr) -> Result<()> {
    match e {
        Expr::Lam { name, domain, body } => {
            let ty = whnf(env, ty)?;
            let Expr::Pi {
                name: n,
                domain: binder_domain,
                codomain,
            } = ty
            else {
                return Err(Error::TypeMismatch {
                    expected: ty.clone(),
                    actual: infer(env, ctx, e)?,
                });
            };
            check_is_type(env, ctx, domain)?;
            if !convertible(env, ctx, domain, &binder_domain)? {
                return Err(Error::TypeMismatch {
                    expected: binder_domain.as_ref().clone(),
                    actual: domain.as_ref().clone(),
                });
            }
            let mut inner = ctx.clone();
            inner.push(n.or_else(|| name.clone()), domain.as_ref().clone());
            check(env, &inner, body, &codomain)
        }
        _ => {
            let inferred = infer(env, ctx, e)?;
            if convertible(env, ctx, &inferred, ty)? {
                Ok(())
            } else {
                Err(Error::TypeMismatch {
                    expected: ty.clone(),
                    actual: inferred,
                })
            }
        }
    }
}

pub fn check_is_type(env: &Env, ctx: &Ctx, e: &Expr) -> Result<()> {
    infer_sort(env, ctx, e).map(|_| ())
}

/// The universe `e` lives in, i.e. `e : Sort l`.
pub fn infer_sort(env: &Env, ctx: &Ctx, e: &Expr) -> Result<u32> {
    match whnf(env, &infer(env, ctx, e)?)? {
        Expr::Sort(l) => Ok(l),
        other => Err(Error::NotASort(other)),
    }
}
