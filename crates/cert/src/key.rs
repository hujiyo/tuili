//! Structural identity for kernel expressions.
//!
//! Printed forms are not identities: an anonymous binder is printed as `x0`,
//! which can equal a real constant named `x0`, and a bound variable and a
//! constant with that name would then share a map key. The key below tags the
//! expression kind and length-prefixes constant names, so two different
//! expressions cannot collide. Binder names are omitted and de Bruijn indices
//! are kept, so alpha-equivalent expressions share a key.

use std_deduce_kernel::Expr;

/// A collision-free key for structural equality, ignoring binder names.
///
/// The reasoner reuses this encoding for its gap-tree keys, so "the same
/// proposition" never has to be decided by comparing printed text.
pub fn expression_key(expression: &Expr) -> String {
    let mut out = String::new();
    write_expression(expression, &mut out);
    out
}

fn write_expression(expression: &Expr, out: &mut String) {
    match expression {
        Expr::Sort(level) => {
            out.push('s');
            out.push_str(&level.to_string());
            out.push(';');
        }
        Expr::Var(index) => {
            out.push('v');
            out.push_str(&index.to_string());
            out.push(';');
        }
        // An integer literal gets its own tag. The `n` prefix cannot collide
        // with `s` (sort), `v` (variable), `c` (constant) or the structural
        // tags, so `3` and a constant named `3` stay different propositions.
        // The value is written in full including the sign, so no two different
        // literals share a key.
        Expr::Num(value) => {
            out.push('n');
            out.push_str(&value.to_string());
            out.push(';');
        }
        // A calendar day gets its own tag, spelled in the canonical form. Like
        // an integer literal it cannot collide with a constant's key: the `d`
        // tag is not one of `s`/`v`/`c`/`n` or the structural tags, and the
        // value is fixed-width so no two days share a key.
        Expr::Date(value) => {
            out.push('d');
            out.push_str(&value.to_iso());
            out.push(';');
        }
        Expr::Const(name) => {
            out.push('c');
            out.push_str(&name.len().to_string());
            out.push(':');
            out.push_str(name);
            out.push(';');
        }
        Expr::Pi {
            domain, codomain, ..
        } => {
            out.push('p');
            out.push('(');
            write_expression(domain, out);
            out.push('|');
            write_expression(codomain, out);
            out.push(')');
        }
        Expr::Lam { domain, body, .. } => {
            out.push('l');
            out.push('(');
            write_expression(domain, out);
            out.push('|');
            write_expression(body, out);
            out.push(')');
        }
        Expr::App { func, arg } => {
            out.push('a');
            out.push('(');
            write_expression(func, out);
            out.push('@');
            write_expression(arg, out);
            out.push(')');
        }
        Expr::Let { value, body, .. } => {
            out.push('t');
            out.push('(');
            write_expression(value, out);
            out.push('|');
            write_expression(body, out);
            out.push(')');
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std_deduce_kernel::name;

    #[test]
    fn a_bound_variable_and_a_same_named_constant_have_different_keys() {
        assert_ne!(
            expression_key(&Expr::Var(0)),
            expression_key(&Expr::constant("x0"))
        );
    }

    #[test]
    fn binder_names_do_not_change_the_key() {
        let left = Expr::Pi {
            name: Some(name("x")),
            domain: Box::new(Expr::constant("人")),
            codomain: Box::new(Expr::Var(0)),
        };
        let right = Expr::Pi {
            name: Some(name("y")),
            domain: Box::new(Expr::constant("人")),
            codomain: Box::new(Expr::Var(0)),
        };
        assert_eq!(expression_key(&left), expression_key(&right));
    }
}
