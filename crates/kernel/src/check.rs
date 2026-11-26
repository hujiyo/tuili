//! The typing relation.
//!
//! Bidirectional at the only place it matters: lambdas are *checked* against
//! a function type rather than inferred, because inferring them requires an
//! annotation the kernel does not accept guesses for. Everything else is
//! synthesised and compared by definitional equality.

use crate::builtin;
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
        // Built-in constants are not declared in the ledger: their types are
        // fixed by the kernel, so a theory cannot redefine `add` or `Int`.
        Expr::Const(n) => env
            .get(n)
            .map(|d| d.ty.clone())
            .or_else(|| builtin::type_of(n))
            .ok_or_else(|| Error::UnknownName(n.to_string())),
        // A literal is exactly an `Int`. The built-in operations are typed over
        // that one type; a theory that wants a domain name for its amounts
        // writes a `def` alias of `Int`, which is definitionally equal to it.
        Expr::Num(_) => Ok(Expr::constant(builtin::INT)),
        // A date literal is exactly a Date; it is never read as a number.
        Expr::Date(_) => Ok(Expr::constant(builtin::DATE)),
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
            // `less` / `le` are the two overloaded built-ins: the same constant
            // compares two `Int`s or two `Date`s, and the operand types select
            // the scheme. The surface syntax always applies a comparison to both
            // operands, so an under-applied `less` keeps the `Int` scheme from
            // [`builtin::type_of`]. A mixed pair is refused instead of converted.
            if let Some(inferred) = infer_comparison(env, ctx, func, arg) {
                return inferred;
            }
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

/// Type a fully applied `less` / `le`, whose operands may be integers or dates.
///
/// Returns `None` when `func arg` is not a complete comparison; the ordinary
/// application rule then applies. Both operands must have the same built-in
/// literal type: two `Int`s or two `Date`s. Definitional equality decides the
/// type (so a `def 日期 : Type := Date` alias counts), and anything else — a
/// mixed pair, or an operand that is neither — is an explicit error rather than
/// an implicit conversion.
fn infer_comparison(env: &Env, ctx: &Ctx, func: &Expr, arg: &Expr) -> Option<Result<Expr>> {
    // The shape is `(less left) right`: an application whose head is `less` or
    // `le` and which already carries its first operand.
    let Expr::App {
        func: head,
        arg: left,
    } = func
    else {
        return None;
    };
    let Expr::Const(name) = head.as_ref() else {
        return None;
    };
    if !matches!(
        builtin::Op::from_name(name),
        Some(builtin::Op::Less | builtin::Op::Le)
    ) {
        return None;
    }
    Some((|| -> Result<Expr> {
        let left_ty = infer(env, ctx, left)?;
        let right_ty = infer(env, ctx, arg)?;
        let date = Expr::constant(builtin::DATE);
        let int = Expr::constant(builtin::INT);
        let both = |ty: &Expr| -> Result<(bool, bool)> {
            Ok((
                convertible(env, ctx, ty, &date)?,
                convertible(env, ctx, ty, &int)?,
            ))
        };
        let (left_date, left_int) = both(&left_ty)?;
        let (right_date, right_int) = both(&right_ty)?;
        if (left_date && right_date) || (left_int && right_int) {
            return Ok(Expr::Sort(0));
        }
        Err(Error::other(format!(
            "比较 `{}` 的两个操作数必须同为 Int 或同为 Date：左边是「{}」，右边是「{}」；\
             本系统不做隐式转换",
            name,
            crate::pretty::print_expr(&left_ty),
            crate::pretty::print_expr(&right_ty)
        )))
    })())
}

/// The universe `e` lives in, i.e. `e : Sort l`.
pub fn infer_sort(env: &Env, ctx: &Ctx, e: &Expr) -> Result<u32> {
    match whnf(env, &infer(env, ctx, e)?)? {
        Expr::Sort(l) => Ok(l),
        other => Err(Error::NotASort(other)),
    }
}
