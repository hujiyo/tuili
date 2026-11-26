//! Certificate expressions.
//!
//! [`CertExpr`] is the serialized form of a kernel expression. Its JSON shape
//! is part of the certificate format version: `kind` tags and field names are
//! frozen for the version in which they were introduced.

use std::fmt;

use serde::{Deserialize, Serialize};

use std_deduce_kernel::{Date, Expr};

/// A calendar-day value in a certificate expression.
///
/// The wire form is the canonical `YYYY-MM-DD` string, and it is validated on
/// the way in: a certificate that writes an impossible day (`2020-02-30`), a
/// loose shape (`2020-5-6`) or a day outside `1900-01-01..=9999-12-31` is
/// refused at parse time. Reading a certificate can therefore never invent a
/// date the kernel would have to refuse later, and there is no conversion from
/// a string or a number into a date anywhere in the format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CertDate(Date);

impl CertDate {
    /// Wrap a date the kernel already validated.
    pub fn new(date: Date) -> Self {
        CertDate(date)
    }

    /// Parse one `YYYY-MM-DD` day, refusing an invalid or out-of-range value.
    pub fn parse(value: &str) -> std::result::Result<Self, String> {
        Date::parse(value).map(CertDate)
    }

    /// The kernel value.
    pub fn date(self) -> Date {
        self.0
    }
}

impl fmt::Display for CertDate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.to_iso())
    }
}

impl Serialize for CertDate {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.0.to_iso())
    }
}

impl<'de> Deserialize<'de> for CertDate {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = String::deserialize(deserializer)?;
        CertDate::parse(&value).map_err(serde::de::Error::custom)
    }
}

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
    /// A calendar-day literal, written as
    /// `{"kind": "date", "value": "2020-05-06"}`. The value is one canonical
    /// `YYYY-MM-DD` string inside `1900-01-01..=9999-12-31`; anything else is
    /// refused when the certificate is parsed (see [`CertDate`]).
    Date { value: CertDate },
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
            Expr::Date(value) => CertExpr::Date {
                value: CertDate::new(*value),
            },
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
            CertExpr::Date { value } => Expr::Date(value.date()),
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
