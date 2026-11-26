//! Normalisation.
//!
//! The kernel reduces only what it must: beta, delta for `def`, and zeta for
//! `let`. Predicates, axioms, rules and interpretations stay *opaque*.
//! A rule is not an equation, and unfolding it would be precisely the quiet
//! overreach this kernel refuses to make.
//!
//! The built-in operations of [`crate::builtin`] are the one exception on the
//! term side: they are *computations*, not definitions. `add 3000 2000` reduces
//! to `5000` and `addYears d"2020-02-29" 1` to `d"2021-02-28"` in [`whnf`]; an
//! `i64` overflow or a date outside `1900-01-01..=9999-12-31` is returned as an
//! error instead of wrapping or clamping. A partially applied operation
//! (`add 3000`) is neutral: nothing is guessed about the missing argument, and
//! an operand that is not a literal of the expected kind (an integer where a
//! date operation needs a date) leaves the term neutral too — the kind mismatch
//! is reported by the type checker, not converted here.

use crate::builtin::{Op, Operand};
use crate::env::{Ctx, DeclKind, Env};
use crate::error::Result;
use crate::term::{instantiate, Expr};

/// Weak head normal form: reduce until the head is not a redex.
///
/// No context is needed: beta and zeta substitute immediately, a `def`'s body
/// is closed, so unfolding never looks at the local binders, and a built-in
/// operation is evaluated only from its literal arguments.
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
                        if let Some(reduced) = evaluate_builtin(env, &rebuilt)? {
                            e = reduced;
                            continue;
                        }
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
            // Every argument just reached its normal form, so a built-in
            // operation whose arguments are now literals can still reduce.
            // `whnf` is asked again rather than the value being assumed: only
            // it knows whether the application is a complete operation.
            if let Some(name) = out.head_const() {
                if Op::from_name(&name).is_some() {
                    let reduced = whnf(env, &out)?;
                    if reduced != out {
                        return normalize(env, ctx, &reduced);
                    }
                }
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

/// Reduce the built-in computations inside `e`, and nothing else.
///
/// This is the evaluation the reasoner records for a rule instance: a matched
/// conclusion such as `合计 甲 (add 3000 2000)` becomes `合计 甲 5000`, and
/// `截止 甲 (addYears d"2020-05-06" 3)` becomes `截止 甲 d"2023-05-06"`, while a
/// `def` alias, a predicate, a quantifier and every other opaque term are kept
/// exactly as written. Beta, zeta and `def` delta are *not* applied here, so
/// this function cannot be used to rewrite a proposition beyond computing its
/// literals.
///
/// Operands that are themselves reducible to a literal (a `def` alias of a
/// number or a date, say) are unfolded for the sake of the value; an operand
/// that is not a literal of the expected kind leaves the operation neutral. An
/// `i64` overflow or a date outside the supported range is an error.
pub fn evaluate_arithmetic(env: &Env, e: &Expr) -> Result<Expr> {
    match e {
        Expr::Sort(_) | Expr::Var(_) | Expr::Const(_) | Expr::Num(_) | Expr::Date(_) => {
            Ok(e.clone())
        }
        Expr::Pi {
            name,
            domain,
            codomain,
        } => Ok(Expr::Pi {
            name: name.clone(),
            domain: Box::new(evaluate_arithmetic(env, domain)?),
            codomain: Box::new(evaluate_arithmetic(env, codomain)?),
        }),
        Expr::Lam { name, domain, body } => Ok(Expr::Lam {
            name: name.clone(),
            domain: Box::new(evaluate_arithmetic(env, domain)?),
            body: Box::new(evaluate_arithmetic(env, body)?),
        }),
        Expr::Let { name, value, body } => Ok(Expr::Let {
            name: name.clone(),
            value: Box::new(evaluate_arithmetic(env, value)?),
            body: Box::new(evaluate_arithmetic(env, body)?),
        }),
        Expr::App { .. } => {
            let (head, args) = spine(e);
            let evaluated_head = evaluate_arithmetic(env, head)?;
            let mut evaluated_args = Vec::with_capacity(args.len());
            for arg in args {
                evaluated_args.push(evaluate_arithmetic(env, arg)?);
            }
            // The head may be a `def` alias of an operation; it counts as the
            // operation only when the whole application then reduces to a
            // value, so a neutral alias is left in place.
            if let Expr::Const(name) = whnf(env, &evaluated_head)? {
                if let Some(op) = Op::from_name(&name) {
                    if evaluated_args.len() == op.arity() {
                        let mut values = Vec::with_capacity(evaluated_args.len());
                        let mut all_literals = true;
                        for arg in &evaluated_args {
                            match literal_operand(env, arg)? {
                                Some(value) => values.push(value),
                                None => {
                                    all_literals = false;
                                    break;
                                }
                            }
                        }
                        if all_literals {
                            return op.apply(&values);
                        }
                    }
                }
            }
            Ok(evaluated_args.into_iter().fold(evaluated_head, Expr::app))
        }
    }
}

/// Evaluate one comparison to its truth value.
///
/// The term is first evaluated with [`evaluate_arithmetic`] (which already
/// folds the built-in operations), and the result must be the built-in
/// proposition `True` or `False`. Everything else is an error, never a guess:
/// an overflow keeps its own diagnostic, and a term whose operands are not
/// integer literals stays neutral — the guard cannot be decided, so the caller
/// reports that instead of silently treating it as `false`.
///
/// This is the function the reasoner and the certificate checker share to
/// judge a `guard`; there is no second interpretation of a comparison.
pub fn evaluate_comparison(env: &Env, e: &Expr) -> Result<bool> {
    let evaluated = evaluate_arithmetic(env, e)?;
    if let Some(value) = crate::builtin::truth_value(&evaluated) {
        return Ok(value);
    }
    Err(crate::Error::other(format!(
        "比较「{}」未能求值成布尔：求值结果是「{}」，只有两个操作数都是同类字面量（Int 或 Date）时比较才能判定",
        crate::pretty::print_expr(e),
        crate::pretty::print_expr(&evaluated)
    )))
}

/// The literal value an operand reduces to, or `None` when it is not a literal.
///
/// An integer and a date are different literal kinds: the operand keeps its
/// kind, and an operation that receives the wrong kind refuses it (see
/// [`crate::builtin::Op::apply`]) instead of converting.
fn literal_operand(env: &Env, e: &Expr) -> Result<Option<Operand>> {
    // An argument is inspected in weak head normal form: `add (add 1 2) 3`
    // must see the inner `3` without normalizing the whole term.
    Ok(match whnf(env, e)? {
        Expr::Num(value) => Some(Operand::Int(value)),
        Expr::Date(value) => Some(Operand::Date(value)),
        _ => None,
    })
}

/// Evaluate one application whose head is a built-in operation and whose
/// arguments are all literals; `None` when either condition does not hold.
fn evaluate_builtin(env: &Env, e: &Expr) -> Result<Option<Expr>> {
    let (head, args) = spine(e);
    let Expr::Const(name) = head else {
        return Ok(None);
    };
    let Some(op) = Op::from_name(name) else {
        return Ok(None);
    };
    if args.len() != op.arity() {
        return Ok(None);
    }
    let mut values = Vec::with_capacity(args.len());
    for arg in args {
        match literal_operand(env, arg)? {
            Some(value) => values.push(value),
            None => return Ok(None),
        }
    }
    Ok(Some(op.apply(&values)?))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin;
    use crate::term::name;

    #[test]
    fn a_partially_applied_operation_stays_neutral() {
        let env = Env::new();
        let partial = Expr::app(Expr::constant(builtin::ADD), Expr::Num(3));
        assert_eq!(whnf(&env, &partial).expect("whnf"), partial);
    }

    #[test]
    fn arithmetic_does_not_unfold_a_predicate_head() {
        let env = Env::new();
        let term = Expr::app(Expr::constant("合计"), Expr::Num(3));
        assert_eq!(whnf(&env, &term).expect("whnf"), term);
        let _ = name("合计");
    }
}
