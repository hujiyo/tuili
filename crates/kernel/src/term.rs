//! Terms and types.
//!
//! Representation: locally nameless. Bound variables are de Bruijn indices
//! counting binders outward; every free name is a constant resolved through
//! `Env`. Indices make weakening and substitution correct by construction,
//! and they keep this file small enough to audit in one sitting.

use std::fmt;
use std::rc::Rc;

pub type Name = Rc<str>;
pub type Level = u32;

/// Convenience constructors for names, so call sites stay readable.
pub fn name(s: impl AsRef<str>) -> Name {
    Rc::from(s.as_ref())
}

/// An expression (or type; the kernel draws no distinction).
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// A universe. `Sort 0` is `Prop`, `Sort 1` is `Type`, `Sort 2` is `Type 1`...
    Sort(Level),
    /// A bound variable, by de Bruijn index counting binders outward.
    Var(usize),
    /// A constant, resolved from the environment.
    Const(Name),
    /// `Pi (x : A) B` — dependent function space. `name = None` means the
    /// binder is anonymous, which is what `A → B` elaborates to.
    Pi {
        name: Option<Name>,
        domain: Box<Expr>,
        codomain: Box<Expr>,
    },
    /// `fun x : A => body`
    Lam {
        name: Option<Name>,
        domain: Box<Expr>,
        body: Box<Expr>,
    },
    /// `f a`
    App { func: Box<Expr>, arg: Box<Expr> },
    /// `let x := v; body` — kept for printing, zeta-reduced by the kernel.
    Let {
        name: Option<Name>,
        value: Box<Expr>,
        body: Box<Expr>,
    },
}

impl Expr {
    pub fn sort(l: Level) -> Expr {
        Expr::Sort(l)
    }
    pub fn var(i: usize) -> Expr {
        Expr::Var(i)
    }
    pub fn constant(n: impl AsRef<str>) -> Expr {
        Expr::Const(name(n))
    }
    pub fn app(f: Expr, a: Expr) -> Expr {
        Expr::App {
            func: Box::new(f),
            arg: Box::new(a),
        }
    }
    pub fn apps(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
        args.into_iter().fold(f, Expr::app)
    }
    pub fn pi(domain: Expr, codomain: Expr) -> Expr {
        Expr::Pi {
            name: None,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }
    pub fn forall(n: impl AsRef<str>, domain: Expr, codomain: Expr) -> Expr {
        Expr::Pi {
            name: Some(name(n)),
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }
    pub fn lam(n: impl AsRef<str>, domain: Expr, body: Expr) -> Expr {
        Expr::Lam {
            name: Some(name(n)),
            domain: Box::new(domain),
            body: Box::new(body),
        }
    }

    /// The head constant of an atom such as `侵害 张三 建房`, if any.
    pub fn head_const(&self) -> Option<Name> {
        match self {
            Expr::Const(n) => Some(n.clone()),
            Expr::App { func, .. } => func.head_const(),
            _ => None,
        }
    }
}

/// Lift every free variable at depth `cutoff` or deeper by `d`.
///
/// `cutoff` is the number of binders crossed. A variable with index below the
/// cutoff is bound and must not move.
pub fn shift(e: &Expr, d: isize, cutoff: usize) -> Expr {
    match e {
        Expr::Sort(_) | Expr::Const(_) => e.clone(),
        Expr::Var(i) => {
            if *i < cutoff {
                e.clone()
            } else {
                let n = (*i as isize + d) as usize;
                Expr::Var(n)
            }
        }
        Expr::Pi {
            name,
            domain,
            codomain,
        } => Expr::Pi {
            name: name.clone(),
            domain: Box::new(shift(domain, d, cutoff)),
            codomain: Box::new(shift(codomain, d, cutoff + 1)),
        },
        Expr::Lam {
            name,
            domain,
            body,
        } => Expr::Lam {
            name: name.clone(),
            domain: Box::new(shift(domain, d, cutoff)),
            body: Box::new(shift(body, d, cutoff + 1)),
        },
        Expr::App { func, arg } => Expr::App {
            func: Box::new(shift(func, d, cutoff)),
            arg: Box::new(shift(arg, d, cutoff)),
        },
        Expr::Let { name, value, body } => Expr::Let {
            name: name.clone(),
            value: Box::new(shift(value, d, cutoff)),
            body: Box::new(shift(body, d, cutoff + 1)),
        },
    }
}

/// Replace `Var j` in `e` by `s`, decrementing indices above `j`.
///
/// `s` is taken to live in the same context as `e` at the point of
/// replacement; entering a binder shifts it by one and raises the target.
pub fn subst(e: &Expr, j: usize, s: &Expr) -> Expr {
    match e {
        Expr::Sort(_) | Expr::Const(_) => e.clone(),
        Expr::Var(i) => {
            if *i == j {
                s.clone()
            } else if *i > j {
                Expr::Var(*i - 1)
            } else {
                Expr::Var(*i)
            }
        }
        Expr::Pi {
            name,
            domain,
            codomain,
        } => Expr::Pi {
            name: name.clone(),
            domain: Box::new(subst(domain, j, s)),
            codomain: Box::new(subst(codomain, j + 1, &shift(s, 1, 0))),
        },
        Expr::Lam {
            name,
            domain,
            body,
        } => Expr::Lam {
            name: name.clone(),
            domain: Box::new(subst(domain, j, s)),
            body: Box::new(subst(body, j + 1, &shift(s, 1, 0))),
        },
        Expr::App { func, arg } => Expr::App {
            func: Box::new(subst(func, j, s)),
            arg: Box::new(subst(arg, j, s)),
        },
        Expr::Let { name, value, body } => Expr::Let {
            name: name.clone(),
            value: Box::new(subst(value, j, s)),
            body: Box::new(subst(body, j + 1, &shift(s, 1, 0))),
        },
    }
}

/// Beta: put `arg` in for the outermost binder of `body`.
pub fn instantiate(body: &Expr, arg: &Expr) -> Expr {
    subst(body, 0, arg)
}

/// True when no variable is free at the top level.
pub fn is_closed(e: &Expr) -> bool {
    free_vars(e, 0).is_empty()
}

/// Indices that are free at depth `depth`.
pub fn free_vars(e: &Expr, depth: usize) -> Vec<usize> {
    fn go(e: &Expr, depth: usize, out: &mut Vec<usize>) {
        match e {
            Expr::Sort(_) | Expr::Const(_) => {}
            Expr::Var(i) => {
                if *i >= depth {
                    out.push(*i - depth);
                }
            }
            Expr::Pi {
                domain, codomain, ..
            } => {
                go(domain, depth, out);
                go(codomain, depth + 1, out);
            }
            Expr::Lam { domain, body, .. } => {
                go(domain, depth, out);
                go(body, depth + 1, out);
            }
            Expr::App { func, arg } => {
                go(func, depth, out);
                go(arg, depth, out);
            }
            Expr::Let { value, body, .. } => {
                go(value, depth, out);
                go(body, depth + 1, out);
            }
        }
    }
    let mut out = Vec::new();
    go(e, depth, &mut out);
    out
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", crate::pretty::print_expr(self))
    }
}
