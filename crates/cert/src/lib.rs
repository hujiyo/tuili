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
//! ## Environment identity
//!
//! Version 3 makes [`Certificate::environment`] mandatory: the certificate
//! records the profile, pack versions and hashes, trust levels and corpus file
//! hashes of the environment it was produced in. The reasoner fills
//! [`EnvironmentIdentity::Unrecorded`], which cannot be serialized, and the CLI
//! stamps a real identity before exporting.
//! `:verify-cert` compares the recorded identity with the current environment
//! before running either proof layer, so a certificate does not silently cross
//! a pack or corpus change. `as_of` and `jurisdiction` are explicit `null` when
//! unspecified; the CLI's `--as-of` and `--jurisdiction` options record
//! non-null values for them.
//!
//! ## Version policy
//!
//! [`FORMAT_VERSION`] is 3. `format_version` is a [`FormatVersion`], whose
//! deserializer accepts only the version this build implements. Unknown or
//! missing versions are rejected; there is no repair, migration or fallback.
//! Adding, removing or reinterpreting a field requires a new format version.
//! Unknown fields are also rejected, so a typo cannot be silently ignored.
//! Version 2 certificates predate the environment identity and are refused
//! with a version error before any missing-field error is reported.
//!
//! ## Checking
//!
//! [`check`] validates a certificate against an environment without using the
//! reasoner: it rebuilds each rule application from the rule declaration, the
//! recorded bindings and the cited premises, and rejects a step whose
//! `unless` condition is proved anywhere in the certificate, asserted by an
//! environment axiom, or derivable from the environment's rules under a
//! conservative fixed-point superset that ignores `unless`, conflicts and
//! priorities. Proved and derivable blockers are compared up to kernel
//! conversion, so alpha- and eta-variants count. Every listed assumption
//! counts, whether or not a node cites it, and each must be a proposition.
//! The closure is computed only when a rule step has an `unless`. Rules that
//! depend on a premise binder
//! are rejected rather than checked with an open `?name`; a rule that cannot
//! be evaluated statically contributes its opened conclusion as a pattern,
//! and patterns propagate through the statically evaluable rules whose
//! premises can consume them, so a matching unproved blocker is rejected as
//! unconfirmable. A blocker with no extractable
//! predicate head is rejected as well. [`kernel_proof`] turns the
//! monotone skeleton into kernel terms and has the kernel check each rule
//! step; it does not inspect `unless`. The crate depends on the kernel only;
//! it never depends on the reasoner. Sources and priorities are data this
//! layer preserves, not conditions it adjudicates; conflicts are only
//! adjudicated for the root, and open obligations are reported through
//! [`CheckReport::requires_human`] without failing the check.
//!
//! ## Rendering
//!
//! [`render`] prints the user-facing derivation tree from the certificate
//! alone, so what a user sees is the object that [`check`] and
//! [`kernel_proof`] inspect. It rejects an out-of-range node reference or a
//! cyclic node graph with an error naming the node; it never falls back to a
//! placeholder.

mod closure;
mod key;

pub mod check;
pub mod environment;
pub mod expr;
pub mod model;
pub mod proof;
pub mod render;
pub mod source;
pub mod version;

pub use check::{check, CheckError, CheckReport};
pub use environment::{
    CorpusRecord, EnvironmentDifference, EnvironmentIdentity, EnvironmentRecord, ExplicitText,
    PackRecord, TrustLevel, UnrecordedEnvironment,
};
pub use expr::{CertExpr, ExprEncodeError};
pub use model::{
    Assumption, Binding, Certificate, Conflict, GapCandidate, Metadata, Node, NodeId,
    ObligationKind, OpenObligation, Provenance, Resolution, Side,
};
pub use proof::{kernel_proof, KernelProofError, KernelProofReport, KernelStep};
pub use render::render;
pub use source::Source;
pub use version::{FormatVersion, FORMAT_VERSION};
