//! The kernel: the single trusted component.
//!
//! Contract, kept deliberately small so it can be audited and, if necessary,
//! replaced:
//!
//! * Terms use locally nameless (de Bruijn) indices.
//! * Sorts form a predicate chain `Sort 0 : Sort 1 : Sort 2 : ...`
//!   with no `Sort-in-Sort`. `Sort 0` is the sort of propositions.
//! * The kernel never guesses: no unification, no metavariables, no instance
//!   search, no implicit arguments. Those live in the elaborator (`lang`).
//!   This boundary matters: the trusted core only ever answers yes or no.
//! * The kernel is a checker, not a prover. Given a term and a claimed type
//!   it accepts or rejects. It has no way to "just trust" a step.
//! * Integers are exact `i64` values ([`Expr::Num`]) typed by the built-in
//!   `Int`, and a small set of built-in operations ([`builtin`]) is *evaluated*
//!   by normalisation. Overflow is an error, never a wraparound, and there is
//!   no floating point.

pub mod builtin;
pub mod check;
pub mod conv;
pub mod env;
pub mod error;
pub mod meta;
pub mod norm;
pub mod pretty;
pub mod term;

pub use env::{
    Burden, Ctx, Decl, DeclKind, Env, FactIdentity, InterpretationDirection, ProofBurden,
    RiskTheme, RuleDecl, RulePleading, Standard,
};
pub use error::{Error, Result};
pub use meta::{Scope, ScopeOrigin};
pub use term::{name, Expr, Level, Name};

pub const PROP: u32 = 0;
pub const TYPE: u32 = 1;
