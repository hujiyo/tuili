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
//! [`FORMAT_VERSION`] is 7. `format_version` is a [`FormatVersion`], whose
//! deserializer accepts only the version this build implements. Unknown or
//! missing versions are rejected; there is no repair, migration or fallback.
//! Adding, removing or reinterpreting a field requires a new format version.
//! Unknown fields are also rejected, so a typo cannot be silently ignored.
//! Version 7 records the temporal/spatial applicability of every rule
//! application and gap candidate (verdict, reference dates and places, rule
//! scope, session fallback values, reason code and explanation) and each
//! assumption's recorded `occurred_at` / `occurred_in`; version 6 records the
//! enabled interpretations: a mandatory `interpretations` table, the
//! `interpretation_application` node and the interpretation witness of a
//! conflict; version 5 records the fact identity
//! of every assumption and the reason for an unresolved claim that met a rule
//! conclusion; version 4 adds the conflict-resolution basis and the unresolved
//! reason; version 3 makes the environment identity mandatory; version 2 adds
//! the source fields; version 1 predates them. All older versions are refused
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
//! counts, whether or not a node cites it, and each must be a proposition
//! carrying a fact identity: a disputed proposition cannot be listed as an
//! assumption, and one proposition cannot appear under two identities.
//! Version 6 also lists the enabled interpretations the proof cites: each entry
//! must name an environment `interpret` declaration with kernel-equivalent
//! `from`/`to`, identical direction and sources, and the table must be sorted
//! by id; every entry must be referenced, and an `interpretation_application`
//! node must cite an earlier node proving `from` and conclude the declared
//! `to`. A conflict witness may be an interpretation index; it is validated
//! against the declaration and is never treated as a lost rule witness.
//! An interpretation is one explicit step: neither an `interpretation_application`
//! premise nor a `rule_application` premise may be interpretation-derived, so a
//! certificate can express neither an interpretation chain nor a rule that
//! consumes an interpretation conclusion.
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
//! it never depends on the reasoner.
//!
//! Version 7's applicability records are recomputed, never trusted. For a
//! rule application the checker rebuilds the anchor from the cited nodes:
//! a cited assumption contributes the `occurred_at` / `occurred_in` its
//! environment fact registers (aggregated over assumptions of the same
//! proposition), and a cited rule or interpretation conclusion contributes no
//! occurrence. The session `:asof` and jurisdiction come from the recorded
//! environment identity, not from the record, so a certificate cannot invent a
//! fallback date. The rule's declared range, jurisdiction and territory, and
//! each field's origin, are compared with the loaded rule declaration. The
//! checker then computes the verdict, basis and reason and compares every
//! field with the record, naming the node and field on any difference. A rule
//! application whose verdict does not allow firing is rejected. A gap
//! candidate's record is recomputed from its declared basis, and every
//! recorded event time/place must be one the environment's facts register.
//! Assumption occurrences are compared as sets with the environment's fact
//! registrations, so a certificate cannot drop or edit them. Missing
//! applicability fields are a format error, never a defaulted `unchecked`.
//!
//! Every recorded conflict resolution is checked too. A priority-based defeat
//! must cite edges the environment really declares, in the direction of the
//! win, with the same origin and sources, and no cited edge may lie on a
//! priority cycle; the checker also recomputes that the winning side covers
//! every cross pair and the losing side does not. An unusable priority must
//! list exactly the environment's declared edges between the two sides, and
//! no full coverage may exist. An assumption-based defeat must name a strict
//! fact (`verified` or `stipulated`) as the winner; a claim never defeats a
//! rule conclusion or another fact, and a strict fact may defeat a claim. An
//! unresolved reason must match the provenances and the recorded identities:
//! two facts must be either both strict or both claims, and the
//! non-strict-fact reason may name only `user_asserted` or `assumed`, exactly
//! as the assumption table records it. Open obligations are reported through
//! [`CheckReport::requires_human`] without failing the check, with one
//! exception: the `open_concept` obligation is recomputed from the environment's
//! `open` markers and the proof graph, and a certificate that dropped, invented
//! or edited it is rejected. A root derivation that turns an open concept
//! (`重大`, `情节严重`) into a proved proposition is never presented as
//! unconditional. The checker does
//! not re-derive the rule instances named by `left_by` / `right_by`, does not
//! judge conflicts a certificate omits, and does not judge the legal effect of
//! a citation.
//!
//! ## Rendering
//!
//! [`render`] prints the user-facing derivation tree from the certificate
//! alone, so what a user sees is the object that [`check`] and
//! [`kernel_proof`] inspect. An interpretation application is printed as a
//! separate `〈解释 …〉` step with its premise; it is never rendered as a rule.
//! It rejects an out-of-range node reference or a
//! cyclic node graph with an error naming the node; it never falls back to a
//! placeholder. [`render_narrative`] renders the same certificate as a Chinese
//! because-so explanation. It attributes every fact to its recorded identity,
//! keeps the recorded sources, bindings, conflicts, gaps and obligations, and
//! reports a missing source or an unresolved conflict instead of filling it in.

mod closure;
mod key;

pub mod applicability;
pub mod check;
pub mod environment;
pub mod expr;
pub mod model;
pub mod narrative;
pub mod open;
pub mod proof;
pub mod render;
pub mod source;
pub mod version;

pub use applicability::{
    judge as judge_applicability, ApplicabilityAnchor, ApplicabilityBasis, ApplicabilityReason,
    ApplicabilityReasonKind, ApplicabilityVerdict, CodeDimension, DateField, DatedEvidence,
    PlaceEvidence, RuleApplicability, ScopeEvidence, ScopeOriginRecord, SessionEvidence,
};
pub use check::{check, CheckError, CheckReport};
pub use environment::{
    CorpusRecord, EnvironmentDifference, EnvironmentIdentity, EnvironmentRecord, ExplicitText,
    PackRecord, TrustLevel, UnrecordedEnvironment,
};
pub use expr::{CertExpr, ExprEncodeError};
pub use key::expression_key;
pub use model::{
    Assumption, Binding, Certificate, Conflict, Explicit, FactIdentity, GapCandidate,
    Interpretation, InterpretationDirection, Metadata, Node, NodeId, ObligationKind,
    OpenObligation, PriorityClause, PriorityEdge, PriorityOrigin, Provenance, Resolution,
    ResolutionBasis, Side, UnresolvedReason, MAX_CERT_ASSUMPTIONS, MAX_CERT_EXPR_NODES,
    MAX_CERT_JSON_BYTES, MAX_CERT_NODES,
};
pub use narrative::{render_narrative, render_narrative_with_context};
pub use open::{
    dependency as open_concept_dependency, OpenConceptDependency, OPEN_CONCEPT_OBLIGATION_ID,
};
pub use proof::{kernel_proof, KernelProofError, KernelProofReport, KernelStep};
pub use render::{render, render_with_annotations};
pub use source::Source;
pub use version::{FormatVersion, FORMAT_VERSION};
