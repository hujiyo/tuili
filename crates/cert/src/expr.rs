//! Certificate expressions.
//!
//! [`CertExpr`] is the serialized form of a kernel expression. Its JSON shape
//! is part of the certificate format version: `kind` tags and field names are
//! frozen for the version in which they were introduced.

use std::fmt;

use serde::{Deserialize, Serialize};

use std_deduce_kernel::Expr;

/// A certificate expression.
///
/// Semantics match [`Expr`]: `Var` is a de Bruijn index counting binders
/// outward, and binder names are presentational metadata. The conversion is
/// structural; it neither normalizes nor type-checks.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CertExpr {
    /// A universe. `Sort 0` is `Prop`.
    Sort { level: u32 },
    /// A bound variable, by de Bruijn index counting binders outward.
    Var { index: u32 },
    /// A constant resolved through the environment.
    Const { name: String },
    /// An exact integer literal, written as `{"kind": "num", "value": <i64>}`.
    /// The field is a signed 64-bit integer: the certificate format has no
    /// floating point and no rounding, and a value outside the `i64` range is
    /// refused by the kernel before a certificate can be written.
    Num { value: i64 },
    /// A dependent function space.
    Pi {
        binder: Option<String>,
        domain: Box<CertExpr>,
        codomain: Box<CertExpr>,
    },
    /// A lambda abstraction.
    Lam {
        binder: Option<String>,
        domain: Box<CertExpr>,
        body: Box<CertExpr>,
    },
    /// Function application.
    App {
        func: Box<CertExpr>,
        arg: Box<CertExpr>,
    },
    /// A let binding. The kernel zeta-reduces these; they are kept for
    /// faithful round-trip of elaborated terms.
    Let {
        binder: Option<String>,
        value: Box<CertExpr>,
        body: Box<CertExpr>,
    },
}

/// A kernel expression cannot be represented in the certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExprEncodeError {
    /// The de Bruijn index that does not fit in the certificate's `u32` field.
    pub index: usize,
}

impl fmt::Display for ExprEncodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "de Bruijn index {} does not fit in the certificate's 32-bit index field",
            self.index
        )
    }
}

impl std::error::Error for ExprEncodeError {}

impl TryFrom<&Expr> for CertExpr {
    type Error = ExprEncodeError;

    fn try_from(expr: &Expr) -> Result<Self, Self::Error> {
        Ok(match expr {
            Expr::Sort(level) => CertExpr::Sort { level: *level },
            Expr::Var(index) => CertExpr::Var {
                index: u32::try_from(*index).map_err(|_| ExprEncodeError { index: *index })?,
            },
            Expr::Const(name) => CertExpr::Const {
                name: name.to_string(),
            },
            Expr::Num(value) => CertExpr::Num { value: *value },
            Expr::Pi {
                name,
                domain,
                codomain,
            } => CertExpr::Pi {
                binder: name.as_deref().map(str::to_owned),
                domain: Box::new(CertExpr::try_from(domain.as_ref())?),
                codomain: Box::new(CertExpr::try_from(codomain.as_ref())?),
            },
            Expr::Lam { name, domain, body } => CertExpr::Lam {
                binder: name.as_deref().map(str::to_owned),
                domain: Box::new(CertExpr::try_from(domain.as_ref())?),
                body: Box::new(CertExpr::try_from(body.as_ref())?),
            },
            Expr::App { func, arg } => CertExpr::App {
                func: Box::new(CertExpr::try_from(func.as_ref())?),
                arg: Box::new(CertExpr::try_from(arg.as_ref())?),
            },
            Expr::Let { name, value, body } => CertExpr::Let {
                binder: name.as_deref().map(str::to_owned),
                value: Box::new(CertExpr::try_from(value.as_ref())?),
                body: Box::new(CertExpr::try_from(body.as_ref())?),
            },
        })
    }
}

impl TryFrom<Expr> for CertExpr {
    type Error = ExprEncodeError;

    fn try_from(expr: Expr) -> Result<Self, Self::Error> {
        CertExpr::try_from(&expr)
    }
}

impl From<&CertExpr> for Expr {
    fn from(expr: &CertExpr) -> Self {
        match expr {
            CertExpr::Sort { level } => Expr::Sort(*level),
            CertExpr::Var { index } => Expr::Var(*index as usize),
            CertExpr::Const { name } => Expr::constant(name),
            CertExpr::Num { value } => Expr::Num(*value),
            CertExpr::Pi {
                binder,
                domain,
                codomain,
            } => Expr::Pi {
                name: binder.as_deref().map(std_deduce_kernel::name),
                domain: Box::new(Expr::from(domain.as_ref())),
                codomain: Box::new(Expr::from(codomain.as_ref())),
            },
            CertExpr::Lam {
                binder,
                domain,
                body,
            } => Expr::Lam {
                name: binder.as_deref().map(std_deduce_kernel::name),
                domain: Box::new(Expr::from(domain.as_ref())),
                body: Box::new(Expr::from(body.as_ref())),
            },
            CertExpr::App { func, arg } => Expr::App {
                func: Box::new(Expr::from(func.as_ref())),
                arg: Box::new(Expr::from(arg.as_ref())),
            },
            CertExpr::Let {
                binder,
                value,
                body,
            } => Expr::Let {
                name: binder.as_deref().map(std_deduce_kernel::name),
                value: Box::new(Expr::from(value.as_ref())),
                body: Box::new(Expr::from(body.as_ref())),
            },
        }
    }
}

impl From<CertExpr> for Expr {
    fn from(expr: CertExpr) -> Self {
        Expr::from(&expr)
    }
}
