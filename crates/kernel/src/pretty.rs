//! Pretty printing, mirroring the surface syntax.

use crate::env::escape_control;
use crate::term::{Expr, Name};

pub fn print_expr(e: &Expr) -> String {
    let mut out = String::new();
    let mut names = Vec::new();
    go(e, 0, &mut out, &mut names);
    out
}

/// Print one expression in its parenthesized surface form, `(le 5000 3000)`.
///
/// Used where the reader must see the whole expression as one unit and not
/// confuse an application with a list of words — a rule guard's judgement is
/// such a place.
pub fn print_parenthesized(e: &Expr) -> String {
    format!("({})", print_expr(e))
}

fn go(e: &Expr, prec: u8, out: &mut String, names: &mut Vec<String>) {
    match e {
        Expr::Sort(0) => out.push_str("Prop"),
        Expr::Sort(1) => out.push_str("Type"),
        Expr::Sort(n) => out.push_str(&format!("Type {n}")),
        Expr::Var(i) => {
            let n = names.len();
            if *i < n {
                out.push_str(&names[n - 1 - *i]);
            } else {
                out.push_str(&format!("?{i}"));
            }
        }
        Expr::Const(n) => out.push_str(&escape_control(n)),
        // A date literal is an atom, printed in the surface syntax
        // `d"2020-05-06"`, so it reads back as the same date.
        Expr::Date(value) => {
            out.push_str("d\"");
            out.push_str(&value.to_iso());
            out.push('"');
        }
        // A negative literal is an atom on its own (`-3000`), but the surface
        // grammar does not read a leading `-` as the start of an application
        // argument: `add -3000 2000` would reparse as a subtraction or fail. In
        // operand position it is therefore printed in parentheses, which the
        // parser reads back as the same literal.
        Expr::Num(value) => {
            if *value < 0 && prec >= 2 {
                out.push('(');
                out.push_str(&value.to_string());
                out.push(')');
            } else {
                out.push_str(&value.to_string());
            }
        }
        Expr::Pi {
            name,
            domain,
            codomain,
        } => {
            if name.is_none() && !mentions_var0(codomain) {
                if prec > 1 {
                    out.push('(');
                }
                go(domain, 2, out, names);
                out.push_str(" → ");
                go(codomain, 1, out, names);
                if prec > 1 {
                    out.push(')');
                }
            } else {
                let n = label(name, names.len());
                if prec > 0 {
                    out.push('(');
                }
                out.push_str("∀ (");
                out.push_str(&n);
                out.push_str(" : ");
                go(domain, 0, out, names);
                out.push_str("), ");
                names.push(n);
                go(codomain, 0, out, names);
                names.pop();
                if prec > 0 {
                    out.push(')');
                }
            }
        }
        Expr::Lam { name, domain, body } => {
            let n = label(name, names.len());
            if prec > 0 {
                out.push('(');
            }
            out.push_str("λ (");
            out.push_str(&n);
            out.push_str(" : ");
            go(domain, 0, out, names);
            out.push_str("), ");
            names.push(n);
            go(body, 0, out, names);
            names.pop();
            if prec > 0 {
                out.push(')');
            }
        }
        Expr::App { func, arg } => {
            if prec > 2 {
                out.push('(');
            }
            go(func, 2, out, names);
            out.push(' ');
            go(arg, 3, out, names);
            if prec > 2 {
                out.push(')');
            }
        }
        Expr::Let { name, value, body } => {
            let n = label(name, names.len());
            if prec > 0 {
                out.push('(');
            }
            out.push_str("let ");
            out.push_str(&n);
            out.push_str(" := ");
            go(value, 0, out, names);
            out.push_str("; ");
            names.push(n);
            go(body, 0, out, names);
            names.pop();
            if prec > 0 {
                out.push(')');
            }
        }
    }
}

fn label(n: &Option<Name>, depth: usize) -> String {
    match n {
        Some(n) => escape_control(n),
        None => format!("x{depth}"),
    }
}

fn mentions_var0(e: &Expr) -> bool {
    !crate::term::free_vars(e, 0).is_empty()
}

pub fn size(e: &Expr) -> usize {
    match e {
        Expr::Sort(_) | Expr::Var(_) | Expr::Const(_) | Expr::Num(_) | Expr::Date(_) => 1,
        Expr::Pi {
            domain, codomain, ..
        } => 1 + size(domain) + size(codomain),
        Expr::Lam { domain, body, .. } => 1 + size(domain) + size(body),
        Expr::App { func, arg } => 1 + size(func) + size(arg),
        Expr::Let { value, body, .. } => 1 + size(value) + size(body),
    }
}

pub fn print_normalized(env: &crate::env::Env, ctx: &crate::env::Ctx, e: &Expr) -> String {
    match crate::norm::normalize(env, ctx, e) {
        Ok(n) => print_expr(&n),
        Err(_) => print_expr(e),
    }
}
