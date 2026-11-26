//! The certificate data model.
//!
//! Node references are zero-based indices into [`Certificate::nodes`]. The
//! same convention is used by [`Certificate::root`] and
//! [`OpenObligation::nodes`]. The data model does not validate any index;
//! [`crate::check`] validates the proof's node references.

use serde::de::Error as _;
use serde::{Deserialize, Serialize};

use std_deduce_kernel::env::escape_control;

use crate::applicability::RuleApplicability;
use crate::environment::EnvironmentIdentity;
use crate::expr::CertExpr;
use crate::source::Source;
use crate::version::FormatVersion;

/// A zero-based index into [`Certificate::nodes`].
pub type NodeId = usize;

/// The largest certificate JSON document accepted from, or written to, disk.
///
/// Serialization and deserialization both enforce this bound. A certificate is
/// a per-query proof, not a corpus: several megabytes is already far more than
/// any real derivation. The bound is checked before parsing, so an oversized
/// file is rejected without allocating its JSON value first.
pub const MAX_CERT_JSON_BYTES: usize = 8 * 1024 * 1024;

/// The largest number of proof nodes in one certificate.
///
/// This mirrors the environment closure's fact bound: a proof that needs more
/// than this many steps is not useful to a human checker. Exceeding it is an
/// error with a named bound, not a silent truncation.
pub const MAX_CERT_NODES: usize = 10_000;

/// The largest number of assumptions in one certificate.
pub const MAX_CERT_ASSUMPTIONS: usize = 10_000;

/// The largest number of independent witnesses recorded for one conclusion.
///
/// A conclusion can be derived by several rules (or by a rule instance with
/// different bindings). The reasoner keeps every distinct witness up to this
/// fixed bound and marks truncation beyond it; the certificate format cannot
/// carry more than this per conclusion. The bound is intentionally a constant,
/// not a caller option: the checker's auditable boundary must not drift with
/// the caller. It keeps the proof graph finite and readable: a legal rule chain
/// rarely has more than a handful of independent arguments, while a
/// pathological rule set must not grow without limit.
pub const MAX_CERT_WITNESSES_PER_CONCLUSION: usize = 8;

/// The largest number of expression nodes in one certificate term.
///
/// One proposition, binding value, gap candidate or conflict side may not
/// exceed this. It matches the environment closure's single-term bound
/// (`MAX_TERM_NODES` there), so a certificate cannot smuggle in a term the
/// checker's own closure would refuse to normalize.
pub const MAX_CERT_EXPR_NODES: usize = 10_000;

/// A value that is always present in JSON but may be `null`.
///
/// `Option<T>` cannot express that: serde's derive reads a missing `Option`
/// field as `None`, silently turning an absent key into a statement ("no
/// value"). This wrapper deserializes the field with `serde_json::Value`, so a
/// missing key reaches serde's missing-field error while an explicit `null`
/// is accepted as `None`. It is the certificate model's counterpart of
/// [`crate::environment::ExplicitText`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Explicit<T>(Option<T>);

impl<T> Explicit<T> {
    /// The explicit `null` value.
    pub const fn none() -> Self {
        Explicit(None)
    }

    /// A present value.
    pub fn some(value: T) -> Self {
        Explicit(Some(value))
    }

    /// The value, if present.
    pub fn as_ref(&self) -> Option<&T> {
        self.0.as_ref()
    }

    /// Whether the value is the explicit `null`.
    pub fn is_none(&self) -> bool {
        self.0.is_none()
    }

    /// The underlying option.
    pub fn into_option(self) -> Option<T> {
        self.0
    }
}

impl<T> Default for Explicit<T> {
    fn default() -> Self {
        Explicit(None)
    }
}

impl<T: Serialize> Serialize for Explicit<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match &self.0 {
            Some(value) => serializer.serialize_some(value),
            None => serializer.serialize_none(),
        }
    }
}

impl<'de, T: Deserialize<'de>> Deserialize<'de> for Explicit<T> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Parsing through `Value` keeps the strictness: a missing struct field
        // calls this function with serde's missing-field deserializer, whose
        // `deserialize_any` reports the missing field instead of yielding
        // `null`.
        let value = serde_json::Value::deserialize(deserializer)?;
        match value {
            serde_json::Value::Null => Ok(Explicit::none()),
            value => T::deserialize(value)
                .map(Explicit::some)
                .map_err(D::Error::custom),
        }
    }
}

/// A proof certificate.
///
/// The JSON object has exactly the fields below, in this order:
/// `format_version`, `environment`, `assumptions`, `interpretations`, `nodes`,
/// `root`, `alternatives`, `conflicts`, `open_obligations`, `metadata`. Unknown
/// fields are rejected.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Certificate {
    /// The format version. Only [`FormatVersion::CURRENT`] deserializes.
    pub format_version: FormatVersion,
    /// The environment identity the certificate was produced in. Mandatory:
    /// a certificate cannot be exported without one.
    pub environment: EnvironmentIdentity,
    /// Assumptions used by the derivation, including their provenance and
    /// label. [`Node::Assumption`] refers to entries here by index.
    #[serde(default)]
    pub assumptions: Vec<Assumption>,
    /// The interpretations enabled for this certificate, sorted by `id` and
    /// limited to those the derivation actually cites (an application node or
    /// a conflict witness). Mandatory: an empty array means the derivation
    /// used no interpretation, not that the writer forgot to say.
    /// [`Node::InterpretationApplication`] and
    /// [`Provenance::Interpretation`] refer to entries here by index.
    pub interpretations: Vec<Interpretation>,
    /// The proof graph, in dependency order.
    pub nodes: Vec<Node>,
    /// The node that proves the requested conclusion. `null` means the
    /// certificate has no single root (for example a gap-only certificate).
    pub root: Option<NodeId>,
    /// Every conclusion the derivation established by rules or universal
    /// elimination, with all of its independent witness nodes. The main proof
    /// tree is still followed through [`Certificate::root`]; this table says
    /// which other nodes prove the same proposition. Entries are ordered by
    /// proposition key and witnesses by rule name and binding structure, so
    /// repeated generation of the same case is byte-identical.
    pub alternatives: Vec<Alternative>,
    /// Conflicts found while deriving, including defeated ones.
    #[serde(default)]
    pub conflicts: Vec<Conflict>,
    /// Items that are unresolved or require human judgement.
    #[serde(default)]
    pub open_obligations: Vec<OpenObligation>,
    /// Generation information. Optional; all of its fields are optional.
    #[serde(default)]
    pub metadata: Metadata,
}

impl Certificate {
    /// Serialize as compact JSON.
    ///
    /// The certificate's own structural bounds are checked first, so the JSON
    /// it produces stays within the node, assumption and expression limits that
    /// [`Certificate::from_json`] enforces. Environment identity checks are not
    /// repeated here: they run on the way in, and an in-memory environment
    /// record can be built by hand through the public fields.
    pub fn to_json(&self) -> serde_json::Result<String> {
        self.check_limits().map_err(serde_json::Error::custom)?;
        let json = serde_json::to_string(self)?;
        check_json_size(json.len())?;
        Ok(json)
    }

    /// Serialize as indented JSON.
    ///
    /// The same bounds as [`Certificate::to_json`] apply; the pretty-printed
    /// form is slightly larger, which is why the size check runs on the actual
    /// output.
    pub fn to_json_pretty(&self) -> serde_json::Result<String> {
        self.check_limits().map_err(serde_json::Error::custom)?;
        let json = serde_json::to_string_pretty(self)?;
        check_json_size(json.len())?;
        Ok(json)
    }

    /// Stamp the environment identity, replacing whatever the reasoner left.
    ///
    /// The reasoner produces an [`EnvironmentIdentity::Unrecorded`] certificate
    /// because it has no access to the pack registry or corpus; the CLI calls
    /// this before exporting so an unrecorded certificate can never reach disk.
    pub fn with_environment(mut self, environment: EnvironmentIdentity) -> Self {
        self.environment = environment;
        self
    }

    /// The proposition a node states, read through its own variant.
    ///
    /// One mapping is shared by every renderer and every derived view: an
    /// assumption node resolves through the assumption table, a gap node
    /// through its recorded proposition, and a rule, interpretation or
    /// universal-elimination step through its conclusion. An out-of-range
    /// node or a missing table entry is an error naming the reference; a
    /// renderer never substitutes an empty placeholder.
    pub fn node_proposition(&self, node: NodeId) -> Result<&CertExpr, String> {
        let Some(entry) = self.nodes.get(node) else {
            return Err(format!(
                "节点 {node}：节点索引越界：证书只有 {} 个节点",
                self.nodes.len()
            ));
        };
        match entry {
            Node::Assumption { assumption } => self
                .assumptions
                .get(*assumption)
                .map(|entry| &entry.proposition)
                .ok_or_else(|| {
                    format!(
                        "节点 {node}：引用了不存在的假设 {assumption}：证书只有 {} 条假设",
                        self.assumptions.len()
                    )
                }),
            Node::RuleApplication { conclusion, .. } => Ok(conclusion),
            Node::InterpretationApplication { conclusion, .. } => Ok(conclusion),
            Node::AxiomInstance { conclusion, .. } => Ok(conclusion),
            Node::Gap { proposition, .. } => Ok(proposition),
        }
    }

    /// Parse JSON, rejecting an unknown or missing `format_version`.
    ///
    /// The version is probed first, using only the `format_version` field, so a
    /// version 2 certificate reports the version error rather than the
    /// `environment` field it could not have written. A fully parsed
    /// certificate's environment record is then validated, so an exporter
    /// cannot hand out duplicate pack names or a malformed corpus hash.
    pub fn from_json(text: &str) -> serde_json::Result<Self> {
        check_json_size(text.len())?;

        #[derive(Deserialize)]
        struct FormatProbe {
            #[serde(rename = "format_version")]
            _format_version: FormatVersion,
        }

        let _: FormatProbe = serde_json::from_str(text)?;
        let certificate: Self = serde_json::from_str(text)?;
        certificate
            .environment
            .validate()
            .map_err(serde_json::Error::custom)?;
        certificate
            .check_limits()
            .map_err(serde_json::Error::custom)?;
        Ok(certificate)
    }

    /// Check the certificate's own node, assumption and expression bounds.
    ///
    /// The error names the bound and the offending entry. The traversal is
    /// iterative, so it cannot recurse to death on an expression that was
    /// built in memory rather than parsed from JSON.
    fn check_limits(&self) -> Result<(), String> {
        if self.nodes.len() > MAX_CERT_NODES {
            return Err(format!(
                "证书节点数量超过上限 {MAX_CERT_NODES}：实际 {} 个",
                self.nodes.len()
            ));
        }
        if self.assumptions.len() > MAX_CERT_ASSUMPTIONS {
            return Err(format!(
                "证书假设数量超过上限 {MAX_CERT_ASSUMPTIONS}：实际 {} 条",
                self.assumptions.len()
            ));
        }
        for (index, assumption) in self.assumptions.iter().enumerate() {
            check_expression(
                &assumption.proposition,
                &format!("第 {} 条假设的命题", index + 1),
            )?;
        }
        for (index, interpretation) in self.interpretations.iter().enumerate() {
            let place = format!("第 {} 条解释 `{}`", index + 1, interpretation.id);
            check_expression(&interpretation.from, &format!("{place} 的 from"))?;
            check_expression(&interpretation.to, &format!("{place} 的 to"))?;
        }
        // One applicability record per rule application and per gap candidate.
        // The node bound is the certificate's own bound, so the record count
        // is limited with the same named constant instead of an extra budget.
        let mut applicability_records = 0usize;
        for (index, node) in self.nodes.iter().enumerate() {
            match node {
                Node::RuleApplication { .. } => applicability_records += 1,
                Node::Gap { candidates, .. } => applicability_records += candidates.len(),
                _ => {}
            }
            if applicability_records > MAX_CERT_NODES {
                return Err(format!(
                    "证书适用性记录数量超过上限 {MAX_CERT_NODES}：\n\
                     第 {} 个证书节点处已达 {applicability_records} 条",
                    index + 1
                ));
            }
        }
        if self.alternatives.len() > MAX_CERT_NODES {
            return Err(format!(
                "证书结论见证表数量超过上限 {MAX_CERT_NODES}：实际 {} 条",
                self.alternatives.len()
            ));
        }
        for (index, alternative) in self.alternatives.iter().enumerate() {
            let place = format!("第 {} 条结论见证", index + 1);
            check_expression(&alternative.proposition, &format!("{place}的命题"))?;
            if alternative.witnesses.len() > MAX_CERT_WITNESSES_PER_CONCLUSION {
                return Err(format!(
                    "{place}的见证数量超过每个结论 {MAX_CERT_WITNESSES_PER_CONCLUSION} 条上限：\
                     实际 {} 条",
                    alternative.witnesses.len()
                ));
            }
        }
        for (index, node) in self.nodes.iter().enumerate() {
            let place = format!("第 {} 个证书节点", index + 1);
            match node {
                Node::Assumption { .. } => {}
                Node::RuleApplication {
                    conclusion,
                    computed,
                    bindings,
                    guards,
                    choices,
                    ..
                } => {
                    check_expression(conclusion, &format!("{place}的结论"))?;
                    if let Some(computed) = computed {
                        check_expression(computed, &format!("{place}计算前的结论"))?;
                    }
                    for binding in bindings {
                        check_expression(
                            &binding.value,
                            &format!(
                                "{place}的参数 `{}` 绑定",
                                escape_control(&binding.parameter)
                            ),
                        )?;
                    }
                    for guard in guards {
                        check_guard_expression(guard, &place)?;
                    }
                    for choice in choices {
                        check_choice_expression(choice, &place)?;
                    }
                }
                Node::InterpretationApplication { conclusion, .. } => {
                    check_expression(conclusion, &format!("{place}的结论"))?;
                }
                Node::AxiomInstance {
                    conclusion,
                    bindings,
                    ..
                } => {
                    check_expression(conclusion, &format!("{place}的结论"))?;
                    for binding in bindings {
                        check_expression(
                            &binding.value,
                            &format!(
                                "{place}的绑定变量 `{}` 取值",
                                escape_control(&binding.parameter)
                            ),
                        )?;
                    }
                }
                Node::Gap {
                    proposition,
                    candidates,
                    axiom_candidates,
                    ..
                } => {
                    check_expression(proposition, &format!("{place}的缺口命题"))?;
                    for candidate in axiom_candidates {
                        for binding in &candidate.bindings {
                            check_expression(
                                &binding.value,
                                &format!(
                                    "{place}的缺口公理候选 `{}` 的绑定变量 `{}` 取值",
                                    escape_control(&candidate.axiom),
                                    escape_control(&binding.parameter)
                                ),
                            )?;
                        }
                    }
                    for candidate in candidates {
                        for binding in &candidate.bindings {
                            check_expression(
                                &binding.value,
                                &format!(
                                    "{place}的缺口候选 `{}` 的参数 `{}` 绑定",
                                    escape_control(&candidate.rule),
                                    escape_control(&binding.parameter)
                                ),
                            )?;
                        }
                        for expression in &candidate.held {
                            check_expression(
                                expression,
                                &format!(
                                    "{place}的缺口候选 `{}` 已持有前提",
                                    escape_control(&candidate.rule)
                                ),
                            )?;
                        }
                        for expression in &candidate.missing {
                            check_expression(
                                expression,
                                &format!(
                                    "{place}的缺口候选 `{}` 缺失前提",
                                    escape_control(&candidate.rule)
                                ),
                            )?;
                        }
                        for expression in &candidate.blocked_by {
                            check_expression(
                                expression,
                                &format!(
                                    "{place}的缺口候选 `{}` 阻断条件",
                                    escape_control(&candidate.rule)
                                ),
                            )?;
                        }
                        for guard in &candidate.guards {
                            check_guard_expression(
                                guard,
                                &format!("{place}的缺口候选 `{}`", escape_control(&candidate.rule)),
                            )?;
                        }
                        for choice in &candidate.choices {
                            check_choice_expression(
                                choice,
                                &format!(
                                    "{place}的缺口候选 `{}` 的前提选择",
                                    escape_control(&candidate.rule)
                                ),
                            )?;
                        }
                    }
                }
            }
        }
        for (index, conflict) in self.conflicts.iter().enumerate() {
            check_expression(
                &conflict.left,
                &format!("第 {} 条冲突的左侧命题", index + 1),
            )?;
            check_expression(
                &conflict.right,
                &format!("第 {} 条冲突的右侧命题", index + 1),
            )?;
        }
        Ok(())
    }
}

/// Every independent witness of one derived conclusion.
///
/// The conclusion is a proposition, the witnesses are nodes that each derive
/// it. Two witnesses are independent when they are not the same rule instance:
/// the same rule with the same binding values is one witness, however many
/// premise nodes could have been cited for it; a different rule, or the same
/// rule with different binding values, is another. The main proof tree still
/// follows [`Certificate::root`]; this group records the arguments the tree
/// does not show, so a reader can see that a conclusion has more than one
/// reason and deleting the shown path does not remove the conclusion itself.
///
/// A universal elimination is an independent step too: it is recorded as an
/// `axiom_instance` witness. An interpretation application is not a witness:
/// it is a one-step licence and only applies when its conclusion was not
/// already established, so it never competes with a rule or a universal
/// instance for the same conclusion.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Alternative {
    /// The conclusion this group is about.
    pub proposition: CertExpr,
    /// The nodes that derive it, ordered by the deriving rule's name and the
    /// binding structure of the instance (a universal instance sorts by axiom
    /// name and binding structure after the rule witnesses). The order is the
    /// same on every run of the same case.
    pub witnesses: Vec<NodeId>,
    /// Whether more independent witnesses exist than the record can carry.
    /// A truncated group has exactly [`MAX_CERT_WITNESSES_PER_CONCLUSION`]
    /// witnesses; the flag says that at least one more argument exists, never
    /// a silent cut. The exact number of omitted arguments is not recorded:
    /// the checker does not re-run the reasoner, so an omitted count could not
    /// be verified and is deliberately left out.
    pub truncated: bool,
}

/// Who asserts an assumption's proposition.
///
/// The identity is part of the evidence: `verified` and `stipulated` are
/// strict facts, `user_asserted` and `assumed` are claims, and `disputed`
/// records only what the other side asserts. A strict fact outranks a
/// defeasible conclusion; a claim never automatically does. The wire form is
/// the same keyword the fact ledger uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FactIdentity {
    /// Found by a court or stated in an official document.
    Verified,
    /// Stated by the user.
    UserAsserted,
    /// Assumed for the sake of the analysis.
    Assumed,
    /// Disputed by the other side.
    Disputed,
    /// Agreed by both sides.
    Stipulated,
}

impl FactIdentity {
    /// The Chinese label shown in a rendered assumption and in an obligation
    /// description.
    pub fn label_zh(self) -> &'static str {
        match self {
            FactIdentity::Verified => "法院查明",
            FactIdentity::UserAsserted => "用户陈述",
            FactIdentity::Assumed => "分析假设",
            FactIdentity::Disputed => "对方争议",
            FactIdentity::Stipulated => "双方无争议",
        }
    }
}

impl From<&std_deduce_kernel::FactIdentity> for FactIdentity {
    fn from(identity: &std_deduce_kernel::FactIdentity) -> Self {
        match identity {
            std_deduce_kernel::FactIdentity::Verified => FactIdentity::Verified,
            std_deduce_kernel::FactIdentity::UserAsserted => FactIdentity::UserAsserted,
            std_deduce_kernel::FactIdentity::Assumed => FactIdentity::Assumed,
            std_deduce_kernel::FactIdentity::Disputed => FactIdentity::Disputed,
            std_deduce_kernel::FactIdentity::Stipulated => FactIdentity::Stipulated,
        }
    }
}

impl From<&FactIdentity> for std_deduce_kernel::FactIdentity {
    fn from(identity: &FactIdentity) -> Self {
        match identity {
            FactIdentity::Verified => std_deduce_kernel::FactIdentity::Verified,
            FactIdentity::UserAsserted => std_deduce_kernel::FactIdentity::UserAsserted,
            FactIdentity::Assumed => std_deduce_kernel::FactIdentity::Assumed,
            FactIdentity::Disputed => std_deduce_kernel::FactIdentity::Disputed,
            FactIdentity::Stipulated => std_deduce_kernel::FactIdentity::Stipulated,
        }
    }
}

/// An assumption the derivation relies on.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Assumption {
    /// The assumed proposition.
    pub proposition: CertExpr,
    /// Who asserts it. Mandatory: an assumption whose evidence is unknown
    /// cannot be audited. A disputed proposition is not an assumption.
    pub identity: FactIdentity,
    /// Where the assumption comes from. An empty list means the certificate
    /// records no source; it does not mean the assumption is self-evident.
    #[serde(default)]
    pub sources: Vec<Source>,
    /// A human-readable label, for example a fact-ledger identifier.
    #[serde(default)]
    pub label: Option<String>,
    /// The `occurred_at` the environment fact records, or an explicit `null`
    /// when the fact records no occurrence. This is an input of the
    /// applicability judgement: the checker aligns a rule application's
    /// reference dates with the assumptions it consumes. A session fact
    /// (`:given`) records no occurrence, and the query date is never used
    /// to fill it in.
    pub occurred_at: Explicit<String>,
    /// The `occurred_in` the environment fact records, or an explicit `null`
    /// when the fact records no place. A missing place is missing input, never
    /// inferred from the rule's territory.
    pub occurred_in: Explicit<String>,
}

/// How an interpretation moves between the two propositions it relates.
///
/// The direction is declared data, not an inferred property: a legal
/// interpretation is a choice someone makes and must be able to audit. It is
/// recorded verbatim and never applied as a rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum InterpretationDirection {
    /// The words are applied as written.
    Literal,
    /// The proposition is read more broadly than its wording.
    Expand,
    /// The proposition is read more narrowly than its wording.
    Narrow,
    /// The proposition is carried over to a similar case.
    Analogy,
}

impl InterpretationDirection {
    /// The surface keyword, as the ledger writes it.
    pub fn keyword(self) -> &'static str {
        match self {
            InterpretationDirection::Literal => "literal",
            InterpretationDirection::Expand => "expand",
            InterpretationDirection::Narrow => "narrow",
            InterpretationDirection::Analogy => "analogy",
        }
    }
}

impl From<&std_deduce_kernel::InterpretationDirection> for InterpretationDirection {
    fn from(direction: &std_deduce_kernel::InterpretationDirection) -> Self {
        match direction {
            std_deduce_kernel::InterpretationDirection::Literal => InterpretationDirection::Literal,
            std_deduce_kernel::InterpretationDirection::Expand => InterpretationDirection::Expand,
            std_deduce_kernel::InterpretationDirection::Narrow => InterpretationDirection::Narrow,
            std_deduce_kernel::InterpretationDirection::Analogy => InterpretationDirection::Analogy,
        }
    }
}

/// One interpretation enabled for this derivation.
///
/// The entry is an environment declaration, not a proof step: it records an
/// explicit, auditable permission to move from `from` to `to`. The derivation
/// cites it through a [`Node::InterpretationApplication`] or as a conflict
/// witness ([`Provenance::Interpretation`]). Kernel definitional equality,
/// not the printed form, decides whether a certificate's `from`/`to` still
/// match the environment.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Interpretation {
    /// The declaration's name in the environment.
    pub id: String,
    /// The declared direction.
    pub direction: InterpretationDirection,
    /// The proposition the interpretation consumes.
    pub from: CertExpr,
    /// The proposition it licenses.
    pub to: CertExpr,
    /// Where the interpretation comes from.
    #[serde(default)]
    pub sources: Vec<Source>,
}

/// One node of the proof graph.
///
/// The `kind` tag is stable: `assumption`, `rule_application`,
/// `interpretation_application`, `axiom_instance`, `gap`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Node {
    /// A use of [`Assumption`] at the given index.
    Assumption {
        /// Zero-based index into [`Certificate::assumptions`].
        assumption: usize,
    },
    /// One instantiation of a rule.
    RuleApplication {
        /// The rule constant's name in the environment.
        rule: String,
        /// The instantiated conclusion, as the kernel evaluates it: the built-in
        /// arithmetic of `computed` is applied, so a rule that concludes
        /// `合计 甲 (add a b)` records `合计 甲 5000` when the bindings are
        /// `a = 3000`, `b = 2000`.
        conclusion: CertExpr,
        /// The rule's conclusion with the parameter values substituted, before
        /// the kernel evaluated the built-in arithmetic, recorded only when
        /// evaluation changed it. It is the arithmetic step itself: the checker
        /// requires it to be exactly the rule's own conclusion under the
        /// recorded bindings (structural comparison), and the recorded
        /// `conclusion` to be the kernel's value of that expression. Editing
        /// a number or swapping `add` for `mul` breaks one of the two
        /// comparisons. The field is **required** when the instance really
        /// computes something: the checker recomputes the instance from the
        /// environment rule and the recorded bindings, and a step whose
        /// instance evaluates differently must record the pre-evaluation form.
        /// A step without arithmetic may omit it; the checker then derives the
        /// instance from the rule and the bindings itself. The absence is
        /// therefore readable: an arithmetic step that forgot its record is
        /// rejected instead of being taken on trust.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        computed: Option<CertExpr>,
        /// The nodes proving the rule's premises, in the rule's premise order.
        ///
        /// One node per premise. For a plain premise the node proves the
        /// premise itself; for a disjunctive premise it proves the selected
        /// branch; for an existential premise it proves the selected witness'
        /// body instance `P w`. The selection itself is recorded in `choices`
        /// — the premises list alone cannot say which branch or witness was
        /// used, and the checker refuses to guess.
        premises: Vec<NodeId>,
        /// The explicit branch/witness selections of this instance.
        ///
        /// Exactly one entry is required for every compound premise of the
        /// rule (disjunction or existence), and no entry is allowed for a
        /// plain premise. The field is omitted when the rule has only plain
        /// premises, so an ordinary step's JSON is unchanged apart from the
        /// version number. Unselected branches are deliberately not recorded
        /// and not required to be proven: this step establishes that one branch
        /// holds, not that every branch does.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        choices: Vec<PremiseChoice>,
        /// The parameter bindings that produced this instance, available to a
        /// checker without parsing the rendering of the instance.
        bindings: Vec<Binding>,
        /// The guard judgements of this instance: one record per `guard` clause
        /// of the environment's rule declaration, in declaration order. A rule
        /// without guards records nothing (the field is omitted, so an
        /// unguarded step's JSON is unchanged). A guarded step must record every
        /// one of its guards: the checker recomputes each record from the
        /// declaration and the recorded bindings, and an omitted, reordered,
        /// added or edited record is a logical failure, never a default.
        /// Every record of a step that fired must say `true`.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        guards: Vec<GuardRecord>,
        /// Where the applied rule comes from.
        #[serde(default)]
        sources: Vec<Source>,
        /// The temporal/spatial judgement this instance fired under: the
        /// verdict, the event times/places it relied on, the rule's declared
        /// scope and the session fallback values. The checker recomputes it
        /// from the rule's environment declaration and the recorded inputs;
        /// a missing record is a format error, not a default. Boxed because
        /// the record is much larger than the other node variants; the JSON
        /// shape is unchanged.
        applicability: Box<RuleApplicability>,
    },
    /// One application of an enabled interpretation: its `from` is proved by
    /// `premise`, its `to` is the recorded conclusion.
    InterpretationApplication {
        /// Zero-based index into [`Certificate::interpretations`].
        interpretation: usize,
        /// The node that proves the interpretation's `from`.
        premise: NodeId,
        /// The instantiated conclusion, which must be the entry's `to`.
        conclusion: CertExpr,
    },
    /// One universal elimination: the universal fact `axiom` is instantiated
    /// with the recorded closed values of its binding variables.
    ///
    /// The step has no premise node; the universal statement is the axiom
    /// declaration itself. `identity` records who asserts that declaration, so
    /// the derivation cannot hide whether it rests on a court finding, a
    /// stipulation or a mere claim. The conclusion is derived, not assumed:
    /// it is not an [`Assumption`] and carries no identity of its own.
    AxiomInstance {
        /// The universal fact declaration's name in the environment.
        axiom: String,
        /// The identity the universal fact is registered under.
        identity: FactIdentity,
        /// The binding variable's name and the closed value substituted for
        /// it, in the declaration's binder order (outermost first).
        bindings: Vec<Binding>,
        /// The instantiated conclusion, which must be the universal
        /// declaration's body with the bindings substituted.
        conclusion: CertExpr,
        /// Where the universal declaration comes from. The checker compares
        /// every field (count and order included) with the environment
        /// declaration's sources; the reasoner copies them verbatim, so a
        /// reader can audit which article the instance cites.
        #[serde(default)]
        sources: Vec<Source>,
    },
    /// An unclosed goal: the explicit replacement for `sorry`.
    Gap {
        /// The proposition that could not be proved.
        proposition: CertExpr,
        /// Rules that could have concluded it, with what they lack.
        #[serde(default)]
        candidates: Vec<GapCandidate>,
        /// Universal facts whose body unifies with the proposition, with the
        /// binding values an instance would need and, for a refused instance,
        /// why it was refused. They are diagnostics; an instance that
        /// succeeds closes the goal and leaves no gap.
        #[serde(default)]
        axiom_candidates: Vec<GapAxiomCandidate>,
        /// A human-readable explanation of the gap.
        #[serde(default)]
        note: Option<String>,
    },
}

/// One parameter binding of a rule instance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Binding {
    /// The rule parameter's name.
    pub parameter: String,
    /// The value the parameter was bound to.
    pub value: CertExpr,
}

/// Which branch or witness a compound rule premise used.
///
/// The certificate records the choice next to the premise it belongs to; the
/// checker validates three things and refuses the step if any fails:
///
/// * the rule declaration really has a premise at `premise`, and that premise
///   is the kind this choice speaks about (a branch choice only for a
///   disjunction, a witness only for an existence);
/// * the cited premise node proves exactly the selected branch (or the body
///   instance with the selected witness);
/// * the selection exists: `branch` is a written branch, and `witness` is a
///   declared individual (or an integer literal) of the premise's domain type.
///
/// An unselected branch never has to be proven. The certificate therefore
/// proves "one branch holds", not "all branches hold", exactly like the
/// reasoner's semantics.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum PremiseChoice {
    /// Zero-based index of the selected branch of a disjunctive premise.
    Branch {
        /// Zero-based index of the premise in the rule's premise order.
        premise: usize,
        /// Zero-based index of the selected branch in the written order.
        branch: usize,
    },
    /// The concrete witness of an existential premise.
    Witness {
        /// Zero-based index of the premise in the rule's premise order.
        premise: usize,
        /// The closed individual that satisfies the body. It must be a
        /// declared `obj` constant (or an integer literal for an `Int`
        /// domain), never an invented or open term.
        witness: CertExpr,
    },
}

/// One `guard` judgement of a rule instance.
///
/// A guard is an *instance condition*: a comparison over the rule's parameter
/// values that must hold for the rule to fire. The record carries the evidence
/// the verdict was built from, not just the verdict:
///
/// * `expression` — the rule's declared guard with its parameters opened as
///   `?<name>` placeholders, i.e. the template that was judged;
/// * `instance` — the same guard after substituting the recorded bindings, the
///   form the kernel evaluated (for example `(le 5000 3000)`);
/// * `holds` — the evaluated truth value.
///
/// The checker rebuilds `expression` from the environment's rule declaration
/// and `instance` from that declaration plus the recorded `bindings`, then
/// evaluates the comparison itself and compares the result. A recorded `true`
/// changed to `false`, an edited expression, a dropped record or an invented
/// one therefore fails the logical check; the recorded boolean is never
/// trusted on its own.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GuardRecord {
    /// Zero-based index of the guard in the rule's `guard` clauses, in
    /// declaration order.
    pub index: usize,
    /// The declared guard with the rule's parameters opened as `?<name>`.
    pub expression: CertExpr,
    /// The guard after substituting the recorded bindings, before evaluation.
    pub instance: CertExpr,
    /// The evaluated truth value. `null` only for a gap candidate whose
    /// bindings leave a parameter of the guard open: that guard was not
    /// decided, which is not the same as `false`, and the checker requires the
    /// undecided state to be recorded as such.
    pub holds: Explicit<bool>,
}

/// A rule that could have proved a gap, and why it did not.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GapCandidate {
    /// The candidate rule constant.
    pub rule: String,
    /// The parameter bindings that produced this candidate instance, so a
    /// checker can re-instantiate the rule's premises without parsing the
    /// rendering.
    pub bindings: Vec<Binding>,
    /// The rule premises that already hold, in the rule's premise order, each
    /// an instantiated proposition. The checker looks these propositions up in
    /// the environment's fact occurrence registry to rebuild the applicability
    /// anchor; it does not trust the recorded dates directly.
    pub held: Vec<CertExpr>,
    /// Premises that are not known.
    #[serde(default)]
    pub missing: Vec<CertExpr>,
    /// Optional branch labels parallel to `missing`: `Some(k)` marks the
    /// entry as the k-th written branch of one failing disjunctive premise;
    /// `null` marks a plain or existential missing proposition. The reasoner
    /// fills this for disjunctive gaps so `:why` can label each branch instead
    /// of presenting them as unrelated missing premises. The field is omitted
    /// when no entry is a branch, so existing gap certificates keep their JSON.
    /// Hand-written certificates may omit it; the checker validates it when
    /// present.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub missing_branches: Vec<Option<usize>>,
    /// `unless` conditions that already hold, blocking this rule.
    #[serde(default)]
    pub blocked_by: Vec<CertExpr>,
    /// The guard judgements of this candidate instance, one per `guard` clause
    /// of the rule, in declaration order. An excluded candidate is listed with
    /// the guards that did not hold instead of disappearing silently. A
    /// candidate whose bindings leave a guard's parameter open records `holds`
    /// as `null` (the guard could not be decided), never as `false`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub guards: Vec<GuardRecord>,
    /// The branch/witness selections of the compound premises this candidate
    /// already holds, in the same form as a rule application. A disjunctive
    /// premise with a held branch records the selected branch; an existential
    /// premise with a found witness records that witness. A compound premise
    /// that holds no branch/witness has no entry here, and its branches appear
    /// in `missing` (one entry per branch, in written order) instead of a
    /// single lump-sum proposition.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub choices: Vec<PremiseChoice>,
    /// Where the candidate rule comes from.
    #[serde(default)]
    pub sources: Vec<Source>,
    /// The rule's temporal/spatial judgement for this case, recorded so a
    /// reader and the checker know why this candidate was excluded instead of
    /// only what it lacks. The checker recomputes it from the candidate's
    /// bindings and held premises against the rule's environment declaration.
    pub applicability: RuleApplicability,
}

/// A universal fact that could instantiate a gap proposition.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GapAxiomCandidate {
    /// The universal fact declaration's name in the environment.
    pub axiom: String,
    /// The binding variables the unified instance would use, in the
    /// declaration's binder order.
    pub bindings: Vec<Binding>,
    /// Why the instance was not produced, or `None` when it was legal but the
    /// current derivation did not trigger it.
    pub problem: Option<String>,
}

/// Where a conflicting conclusion came from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Provenance {
    /// The conclusion is an assumption; its identity is recorded in the
    /// matching [`Assumption`] entry.
    Assumption,
    /// The conclusion was derived by these rules. An empty list means it was
    /// derived but its witnesses can no longer be rebuilt.
    Rules { rules: Vec<String> },
    /// The conclusion was derived by instantiating the named universal fact.
    /// A universal fact is not a rule: no priority orders it, and it never
    /// counts as a lost rule witness.
    Axiom { axiom: String },
    /// The conclusion was licensed by an enabled interpretation. The index
    /// names the entry in [`Certificate::interpretations`]; the witness is a
    /// declared permission, not an inferred fact.
    Interpretation { interpretation: usize },
}

/// How a conflict was adjudicated.
///
/// A defeated conflict records its basis: a strict fact outranking a
/// defeasible conclusion or a claim, or the declared priority edges that
/// decided it. An unresolved conflict records why nobody won.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Resolution {
    /// One side wins.
    Defeated {
        /// The winning side.
        winner: Side,
        /// Why that side wins.
        basis: ResolutionBasis,
    },
    /// No side wins; neither conclusion is asserted.
    Unresolved {
        /// Why the conflict could not be decided.
        reason: UnresolvedReason,
    },
}

/// Why the winning side of a defeated conflict wins.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ResolutionBasis {
    /// A strict fact (an assumption recorded as `verified` or `stipulated`)
    /// outranks a defeasible conclusion or a claim.
    Assumption,
    /// Declared priority edges decide the conflict.
    Priority {
        /// The edges that establish the win, in the reasoner's certificate
        /// order.
        edges: Vec<PriorityEdge>,
    },
}

/// One declared priority edge: `winner` outranks `loser`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PriorityEdge {
    /// The rule that outranks the other.
    pub winner: String,
    /// The rule that is outranked.
    pub loser: String,
    /// Where the declaration comes from.
    pub origin: PriorityOrigin,
}

impl PriorityEdge {
    /// A stable sort key: `(winner, loser, origin_kind,
    /// declared_in_or_rule, clause)`, with a top-level declaration before a
    /// rule-internal clause and `prefer` before `defeated_by`.
    pub fn sort_key(&self) -> (String, String, u8, String, u8) {
        match &self.origin {
            PriorityOrigin::PriorityDeclaration { declared_in, .. } => (
                self.winner.clone(),
                self.loser.clone(),
                0,
                declared_in.clone(),
                0,
            ),
            PriorityOrigin::RuleClause {
                declaring_rule,
                clause,
                ..
            } => (
                self.winner.clone(),
                self.loser.clone(),
                1,
                declaring_rule.clone(),
                match clause {
                    PriorityClause::Prefer => 0,
                    PriorityClause::DefeatedBy => 1,
                },
            ),
        }
    }
}

/// Where a [`PriorityEdge`] comes from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum PriorityOrigin {
    /// A top-level `priority … over …` declaration of a module.
    PriorityDeclaration {
        /// The namespace that asserted the priority.
        declared_in: String,
        /// The declaration's sources, in declaration order.
        sources: Vec<Source>,
    },
    /// A rule-internal `defeated_by` / `prefer` clause.
    RuleClause {
        /// The rule whose declaration carries the clause.
        declaring_rule: String,
        /// Which clause produced the edge.
        clause: PriorityClause,
        /// The declaring rule's sources, in declaration order.
        rule_sources: Vec<Source>,
    },
}

/// Which rule-internal clause produced a [`PriorityEdge`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PriorityClause {
    /// `prefer X`: the declaring rule beats `X`.
    Prefer,
    /// `defeated_by X`: `X` beats the declaring rule.
    DefeatedBy,
}

/// Why a conflict has no winner.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum UnresolvedReason {
    /// Both sides are facts; neither outranks the other. Two strict facts have
    /// no order between them, and two claims are both unproved.
    ConflictingAssumptions,
    /// A claim met a rule conclusion. The claim is not proof, so it cannot
    /// automatically beat the rule conclusion; the rule conclusion does not
    /// refute the claim either. Neither side wins.
    NonStrictFact {
        /// The identity the claim is recorded under: `user_asserted` or
        /// `assumed`.
        identity: FactIdentity,
    },
    /// One side was derived but its witnesses can no longer be rebuilt, so no
    /// priority can be checked for it. Neither side wins.
    UnknownWitnesses,
    /// The rules of the two sides have no declared priority between them.
    NoPriority,
    /// Priorities are declared between the two sides, but they do not decide
    /// the conflict: coverage is incomplete, both directions are covered, or
    /// the edges lie on a priority cycle.
    PriorityUnusable {
        /// Every declared edge between the two sides, in both directions.
        declared: Vec<PriorityEdge>,
    },
}

/// Which side of a conflict a proposition sits on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Side {
    Left,
    Right,
}

/// A recorded conflict between two conclusions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Conflict {
    pub left: CertExpr,
    pub right: CertExpr,
    pub left_by: Provenance,
    pub right_by: Provenance,
    pub resolution: Resolution,
}

/// An item the certificate does not settle.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OpenObligation {
    /// A stable identifier for the obligation.
    pub id: String,
    pub kind: ObligationKind,
    /// What is unresolved or needs a decision.
    pub description: String,
    /// Nodes this obligation relates to, if any.
    #[serde(default)]
    pub nodes: Vec<NodeId>,
}

/// Why an obligation is open.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObligationKind {
    /// A premise could not be proved.
    MissingPremise,
    /// A declaration lacks a citation.
    MissingSource,
    /// An open legal concept needs an interpretation (`合理`, `重大`, ...).
    /// One obligation is recorded per certificate root derivation whose proof
    /// graph states such a concept; it is recomputed from the environment's
    /// `open` markers and the proof nodes, never taken on trust.
    OpenConcept,
    /// A conflict has no winner.
    UnresolvedConflict,
    /// A human must decide something the logic cannot.
    NeedsHumanDetermination,
    /// Anything else; `description` carries the detail.
    Other,
}

/// Generation information attached to a certificate.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Metadata {
    /// When the certificate was generated, ideally RFC 3339.
    #[serde(default)]
    pub generated_at: Option<String>,
    /// Name of the generating tool.
    #[serde(default)]
    pub tool: Option<String>,
    /// Version of the generating tool.
    #[serde(default)]
    pub tool_version: Option<String>,
}

fn check_json_size(bytes: usize) -> serde_json::Result<()> {
    if bytes > MAX_CERT_JSON_BYTES {
        return Err(serde_json::Error::custom(format!(
            "证书 JSON 超过 {MAX_CERT_JSON_BYTES} 字节上限：实际 {bytes} 字节"
        )));
    }
    Ok(())
}

/// Reject a guard record whose expressions exceed the certificate's term bound.
///
/// Both recorded forms are checked: the opened declaration pattern and the
/// substituted instance.
fn check_guard_expression(guard: &GuardRecord, place: &str) -> Result<(), String> {
    let at = format!("{place}的第 {} 条守卫", guard.index + 1);
    check_expression(&guard.expression, &format!("{at}的声明形式"))?;
    check_expression(&guard.instance, &format!("{at}的求值形态"))
}

/// Reject a premise choice whose witness term exceeds the certificate's
/// expression bound. Branch indices are plain integers and carry no term.
fn check_choice_expression(choice: &PremiseChoice, place: &str) -> Result<(), String> {
    if let PremiseChoice::Witness { premise, witness } = choice {
        check_expression(
            witness,
            &format!("{place}的第 {} 个前提的存在见证", premise + 1),
        )?;
    }
    Ok(())
}

/// Reject an expression with more than [`MAX_CERT_EXPR_NODES`] nodes.
///
/// The explicit stack keeps this check itself off the call stack, so an
/// in-memory expression that was never parsed from JSON cannot overflow it.
fn check_expression(expression: &CertExpr, place: &str) -> Result<(), String> {
    let mut nodes = 0usize;
    let mut pending: Vec<&CertExpr> = vec![expression];
    while let Some(expression) = pending.pop() {
        nodes += 1;
        if nodes > MAX_CERT_EXPR_NODES {
            return Err(format!(
                "{place}的表达式超过 {MAX_CERT_EXPR_NODES} 个节点上限"
            ));
        }
        match expression {
            CertExpr::Sort { .. }
            | CertExpr::Var { .. }
            | CertExpr::Const { .. }
            | CertExpr::Num { .. } => {}
            CertExpr::Pi {
                domain, codomain, ..
            } => {
                pending.push(domain);
                pending.push(codomain);
            }
            CertExpr::Lam { domain, body, .. } => {
                pending.push(domain);
                pending.push(body);
            }
            CertExpr::App { func, arg } => {
                pending.push(func);
                pending.push(arg);
            }
            CertExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
        }
    }
    Ok(())
}
