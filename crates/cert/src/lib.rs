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
//! [`FORMAT_VERSION`] is 10. `format_version` is a [`FormatVersion`], whose
//! deserializer accepts only the version this build implements. Unknown or
//! missing versions are rejected; there is no repair, migration or fallback.
//! Adding, removing or reinterpreting a field requires a new format version.
//! Unknown fields are also rejected, so a typo cannot be silently ignored.
//! Version 10 records exact integers: a certificate expression may carry a
//! `num` literal (`{"kind": "num", "value": …}`), and a rule application step
//! may carry the `computed` form of its conclusion — the rule's own conclusion
//! with the recorded bindings substituted, before the kernel evaluated the
//! built-in arithmetic — while the recorded `conclusion` is that expression's
//! evaluated value. The checker requires `computed` to be exactly the instance
//! the environment's rule and the recorded bindings determine, and the
//! conclusion to be its kernel value, so a changed number or a swapped
//! operation is rejected. There is no floating point in the format.
//! Version 9 records every independent witness of each derived conclusion: the
//! mandatory `alternatives` table names a proposition, the nodes that derive
//! it, and whether the per-conclusion bound truncated the list. The checker
//! verifies every listed witness against the environment, rejects duplicate
//! arguments and requires the root to be listed under its own conclusion.
//! Version 8 records universal elimination: an `axiom_instance` node naming the
//! universal fact, the identity it is asserted under, the closed value of each
//! binding variable, the substituted conclusion and the declaration's sources,
//! and each gap node's universal candidates with their bindings and refusal
//! reasons. The checker recomputes the identity, the binder types, the
//! substituted conclusion and the sources of every instance: a node whose
//! citation differs from the environment declaration in any field — or adds or
//! drops a source — is rejected. Version 7
//! records the temporal/spatial applicability of every rule application and
//! gap candidate (verdict, reference dates and places, rule scope, session
//! fallback values, reason code and explanation) and each assumption's
//! recorded `occurred_at` / `occurred_in`; version 6 records the
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
//! The applicability records are recomputed, never trusted. For a
//! rule application the checker looks up the environment's registered
//! `occurred_at` / `occurred_in` by each cited premise **proposition's** key —
//! a premise proved by a derived conclusion therefore still reads the
//! registered occurrence, and only a proposition with no registration is
//! missing input. The session `:asof` and jurisdiction come from the recorded
//! environment identity, not from the record, so a certificate cannot invent a
//! fallback date. The rule's declared range, jurisdiction and territory, and
//! each field's origin, are compared with the loaded rule declaration. The
//! checker then computes the verdict, basis and reason and compares every
//! field with the record, naming the node and field on any difference. A rule
//! application whose verdict does not allow firing is rejected. A gap
//! candidate's record is recomputed from its recorded bindings and held
//! premises: the checker re-instantiates the rule premises, requires the held
//! and missing lists to partition them in order, checks the instantiated
//! conclusion is the gap proposition, and rebuilds the anchor from the held
//! propositions' environment occurrences. Assumption occurrences are compared
//! as sets with the environment's fact registrations, so a certificate cannot
//! drop or edit them. Missing applicability fields are a format error, never a
//! defaulted `unchecked`.
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
//! as the assumption table records it.
//!
//! ## Conflicts the certificate omits
//!
//! A certificate is user-supplied, so the checker cannot assume the producer
//! recorded every conflict. Every conclusion on the root's proof graph — a
//! rule application, an interpretation application, a universal instance, and
//! an assumption when the root is one — is compared, through the same
//! [`conflict::in_conflict`] judgement the reasoner uses, with every
//! environment fact that seeds a derivation (`verified`, `stipulated`,
//! `user_asserted`, `assumed`; a `disputed` fact takes part in no
//! derivation). A conflict found this way must already be recorded with the
//! resolution the conflict model gives it: a strict fact wins against a rule
//! conclusion, an interpretation conclusion, a universal instance and a
//! claim; two strict facts have no order, so a conclusion that is itself a
//! strict fact cannot stand; a claim never wins, so a claim facing a
//! conclusion must be recorded as `non_strict_fact` and two claims as
//! `conflicting_assumptions`. A missing record, or a record whose resolution
//! contradicts that matrix, fails the check with the node, the opposing
//! proposition and its identity named. A fact a recorded conflict already
//! removed from the fact base does not take part, mirroring the reasoner's
//! accumulate-only removals. The scan compares every pair and is bounded by
//! `MAX_CONFLICT_COMPARISONS`; exceeding the bound is an error, never a
//! partial check. Conflicts between two conclusions with no environment fact
//! involved are not reconstructed: only a recorded one is validated. Open
//! obligations are reported through
//! [`CheckReport::requires_human`] without failing the check, with one
//! exception: the `open_concept` obligation is recomputed from the environment's
//! `open` markers and the proof graph, and a certificate that dropped, invented
//! or edited it is rejected. A root derivation that turns an open concept
//! (`重大`, `情节严重`) into a proved proposition is never presented as
//! unconditional. The checker does
//! not re-derive the rule instances named by `left_by` / `right_by` and does
//! not judge the legal effect of a citation.
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
//!
//! ## Trust labels
//!
//! [`derive_trust`] computes a [`TrustReport`] from the certificate's own
//! fields: the root and its reachable proof graph, each assumption's fact
//! identity, interpretation applications, conflicts and open obligations. The
//! five labels are `已验证`, `依赖假设`, `事实待举证`, `争点未决` and
//! `需律师判断`; [`trust`](mod@trust) documents the exact field-to-label
//! mapping. The labels are a derived view: they are never serialized into the
//! certificate, and the v10 witness table does not change them. `:why`,
//! `:explain` and `:labels` all print the same [`TrustReport::summary`] and the
//! same evidence, so a conclusion cannot be labelled differently by different
//! renderers. A label never asserts legal correctness: `已验证` means the
//! certificate proves the root under strict facts only and leaves nothing open.
//!
//! ## Risk themes
//!
//! [`derive_risk`] computes a [`RiskReport`] from the environment's declared
//! `risk` markers and the propositions on the certificate's root proof graph.
//! It is a second, separate derived view: a themed predicate (criminal law,
//! personal safety, major property, an approaching deadline, foreign or
//! immigration matters) makes the conclusion high-risk, so the CLI prints one
//! explicit warning and `:labels` names the theme as a second label. A theme is
//! never merged into `需律师判断`: the trust label says why the model cannot
//! decide, the risk theme says what the case is about, and both can hold at
//! once. The report is never written into the certificate either, so `:cert`
//! JSON, certificate v8 and `:verify-cert` are unchanged.
//!
//! Because a declared `risk` is the only grading input, a case whose theory
//! declares none would stay silent even when it plainly talks about an offence
//! or bodily harm. [`risk`](mod@risk) therefore adds one non-judgment hint when
//! no declaration matched: it names a term from a small documented word list in
//! the root's printed propositions, says the case declares no `risk`, and says
//! it changes no label and no exit code. The hint is not a grading, `:labels`
//! does not print it, and it is suppressed whenever a declaration matches.

mod closure;
mod key;

pub mod applicability;
pub mod check;
pub mod conflict;
pub mod environment;
pub mod expr;
pub mod model;
pub mod narrative;
pub mod open;
pub mod proof;
pub mod render;
pub mod risk;
pub mod source;
pub mod trust;
pub mod version;

pub use applicability::{
    judge as judge_applicability, ApplicabilityAnchor, ApplicabilityBasis, ApplicabilityReason,
    ApplicabilityReasonKind, ApplicabilityVerdict, CodeDimension, DateField, DatedEvidence,
    PlaceEvidence, RuleApplicability, ScopeEvidence, ScopeOriginRecord, SessionEvidence,
};
pub use check::{check, check_display_projection, CheckError, CheckReport};
pub use environment::{
    CorpusRecord, EnvironmentDifference, EnvironmentIdentity, EnvironmentRecord, ExplicitText,
    PackRecord, TrustLevel, UnrecordedEnvironment,
};
pub use expr::{CertExpr, ExprEncodeError};
pub use key::expression_key;
pub use model::{
    Alternative, Assumption, Binding, Certificate, Conflict, Explicit, FactIdentity,
    GapAxiomCandidate, GapCandidate, Interpretation, InterpretationDirection, Metadata, Node,
    NodeId, ObligationKind, OpenObligation, PriorityClause, PriorityEdge, PriorityOrigin,
    Provenance, Resolution, ResolutionBasis, Side, UnresolvedReason, MAX_CERT_ASSUMPTIONS,
    MAX_CERT_EXPR_NODES, MAX_CERT_JSON_BYTES, MAX_CERT_NODES, MAX_CERT_WITNESSES_PER_CONCLUSION,
};
pub use narrative::{render_narrative, render_narrative_with_context};
pub use open::{
    dependency as open_concept_dependency, OpenConceptDependency, OPEN_CONCEPT_OBLIGATION_ID,
};
pub use proof::{kernel_proof, KernelProofError, KernelProofReport, KernelStep};
pub use render::{render, render_with_annotations};
pub use risk::{derive_risk, RiskReport};
pub use source::Source;
pub use trust::{derive_trust, TrustLabel, TrustReport, LOCAL_EXTENSION_OBLIGATION_ID};
pub use version::{FormatVersion, FORMAT_VERSION};
