//! Proof certificates: the versioned interchange format intended to be shared
//! by the CLI, the API and the AI front end.
//!
//! ## Design: certificate-owned DTOs
//!
//! The certificate expression type is [`CertExpr`], defined here rather than
//! reusing [`std_deduce_kernel::Expr`] directly. Kernel expressions and
//! [`SourceRef`](std_deduce_kernel::env::SourceRef) values are converted at the
//! boundary with [`CertExpr::try_from`] and [`Source::from`].
//!
//! This keeps the kernel free of serialization dependencies and keeps the wire
//! format independent of the kernel's internal representation: changing
//! `Expr` cannot silently change JSON that external readers already consume.
//! The price is an explicit conversion layer, which is small and tested.
//!
//! ## De Bruijn indices
//!
//! [`CertExpr::Var`] stores a de Bruijn index. That convention is part of the
//! format version, not a kernel implementation detail that happens to leak
//! out. [`FormatVersion`] is checked while deserializing, so a reader that
//! does not know the version refuses the certificate instead of guessing at
//! the index convention.
//!
//! ## Version policy
//!
//! [`FORMAT_VERSION`] is 1. `format_version` is a [`FormatVersion`], whose
//! deserializer accepts only the version this build implements. Unknown or
//! missing versions are rejected; there is no repair, migration or fallback.
//! Adding, removing or reinterpreting a field requires a new format version.
//! Unknown fields are also rejected, so a typo cannot be silently ignored.
//!
//! ## Checking
//!
//! [`check`] validates a certificate against an environment without using the
//! reasoner: it rebuilds each rule application from the rule declaration, the
//! recorded bindings and the cited premises, and rejects a step whose
//! `unless` condition is proved anywhere in the certificate or asserted by an
//! environment axiom. Rules that depend on a premise binder are rejected
//! rather than checked with an open `?name`. [`kernel_proof`] turns the
//! monotone skeleton into kernel terms and has the kernel check each rule
//! step; it does not inspect `unless`. The crate depends on the kernel only;
//! it never depends on the reasoner. Sources and priorities are data this
//! layer preserves, not conditions it adjudicates; conflicts are only
//! adjudicated for the root, and open obligations are reported through
//! [`CheckReport::requires_human`] without failing the check.

pub mod check;
pub mod expr;
pub mod model;
pub mod proof;
pub mod source;
pub mod version;

pub use check::{check, CheckError, CheckReport};
pub use expr::{CertExpr, ExprEncodeError};
pub use model::{
    Assumption, Binding, Certificate, Conflict, GapCandidate, Metadata, Node, NodeId,
    ObligationKind, OpenObligation, Provenance, Resolution, Side,
};
pub use proof::{kernel_proof, KernelProofError, KernelProofReport, KernelStep};
pub use source::Source;
pub use version::{FormatVersion, FORMAT_VERSION};
