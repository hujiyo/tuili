//! The temporal and spatial applicability judgement, in the display form.
//!
//! The judgement is data in, data out: a rule's recorded [`Scope`], the
//! occurrence records of the premise facts a rule instance references, and
//! the session's legal as-of date and jurisdiction. The pure function lives in
//! the certificate crate ([`std_deduce_cert::judge_applicability`]), where the
//! independent checker can recompute it from a certificate; this module builds
//! the anchor and converts the result into the types the reasoner, `:gap`,
//! `:why` and `:applicability` print. It does not read the environment, the
//! derivation or the CLI, so it can be tested on its own, and the same
//! judgement is recorded in a version 7 certificate.
//!
//! ## The reference point is the event, not the query date
//!
//! A rule instance is judged against the facts it consumes: every `occurred_at`
//! recorded by a premise fact is a reference time, and the rule's effective
//! range must cover all of them. A rule that was in force when the contract
//! was signed governs it even when the query is made after the rule was
//! repealed; a later rule does not reach back to an earlier event. The
//! session's `:asof` date is only a fallback when the instance references no
//! fact that records an occurrence time; the result then says explicitly that
//! the query date stood in for the event time.
//!
//! The same rule applies to places: every `occurred_in` the premise facts
//! record must be covered by the rule's `territory`. A fact without a recorded
//! place is missing input, never filled in from the rule itself.
//!
//! ## Partial coverage is never silently rounded
//!
//! One event time inside the range and another outside is not "pick the
//! applicable one": it is [`Applicability::Undecidable`], and the reason lists
//! both sides. The same holds for places. Only all-inside is applicable, and
//! only all-outside is inapplicable; a comparison that cannot be made (a code
//! hierarchy nobody declared) is also undecidable.
//!
//! ## Two failures that must not be confused
//!
//! * [`Applicability::Inapplicable`] means enough input was present and the
//!   rule does not cover the events.
//! * [`Applicability::Unchecked`] means an input is missing: a referenced fact
//!   records no occurrence, no `:asof` fallback exists, or the session sets no
//!   jurisdiction.
//! * [`Applicability::Undecidable`] means the input is there but cannot decide:
//!   partial coverage, a malformed date, an interval with its start at or
//!   after its end, or two codes whose containment is undeclared.
//!
//! A missing input outranks an undecidable one, and a clear non-application
//! outranks both. Every verdict carries a [`Basis`] naming the dates and places
//! it looked at, the occurrence gaps and the session values actually used, so
//! the display can be checked against the facts and a certificate can record
//! the same evidence.
//!
//! ## Which verdicts may fire
//!
//! Only [`Applicability::Applicable`] and [`Applicability::Unchecked`] may
//! fire. An unchecked verdict is "we have no evidence at all", and excluding a
//! rule without evidence would itself be a guess. [`Applicability::Inapplicable`]
//! and [`Applicability::Undecidable`] must not fire: the latter already has
//! evidence that the rule covers only part of the instance's events, and using
//! it would turn a contradiction into a premise. Both are listed by `:gap` and
//! `:issues` with their reason; an undecidable one also says that the dispute
//! needs an explicit reference time, which is not implemented yet.

use std_deduce_kernel::env::escape_control;
use std_deduce_kernel::meta::Scope;

/// The outcome of judging one rule instance against its event time and place.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Applicability {
    /// Every referenced event time/place was checked and is covered.
    Applicable {
        /// The dates and places the judgement relied on.
        basis: Basis,
    },
    /// The rule certainly does not cover the events, with the concrete reason.
    Inapplicable {
        /// Which events were outside the range/territory.
        reason: InapplicableReason,
        /// The dates and places the judgement relied on.
        basis: Basis,
    },
    /// A needed input is missing. The rule may still fire, but the caller must
    /// report the state; it is never treated as `Applicable` or as
    /// `Inapplicable`.
    Unchecked {
        /// The missing input.
        missing: MissingInput,
        /// The dates and places that were available, if any.
        basis: Basis,
    },
    /// Every needed input is present but the data itself cannot decide.
    Undecidable {
        /// Why the comparison cannot conclude.
        reason: UndecidableReason,
        /// The dates and places the judgement relied on.
        basis: Basis,
    },
}

/// The dates and places a judgement looked at, with their coverage.
///
/// This is part of the result, not a diagnostic: `:applicability`, `:why` and
/// `:gap` print it next to the verdict, so a reader can match every date to a
/// fact. Dates from a fact are labelled as event times; a date taken from
/// `:asof` says so.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Basis {
    /// Reference dates, in premise order; duplicates are not repeated.
    pub dates: Vec<DatedEvidence>,
    /// Event places, in premise order; duplicates are not repeated.
    pub places: Vec<PlaceEvidence>,
    /// Whether some referenced premise fact recorded no event time.
    pub missing_event_date: bool,
    /// Whether some referenced premise fact recorded no event place.
    pub missing_event_place: bool,
    /// The session `:asof` date that stood in for an event time, if it did.
    pub session_as_of: Option<String>,
    /// The session jurisdiction the judgement compared, if it did.
    pub session_jurisdiction: Option<String>,
}

/// One reference date and whether the rule's range covers it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DatedEvidence {
    /// The date, `YYYY-MM-DD`.
    pub date: String,
    /// `true` when the date came from the session's `:asof` because the
    /// instance referenced no event time; `false` for a fact's `occurred_at`.
    pub query_date_fallback: bool,
    /// `true` when the effective range contains the date.
    pub covered: bool,
}

/// One event place and whether the rule's territory covers it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PlaceEvidence {
    /// The `occurred_in` code.
    pub place: String,
    /// `Some(true)` covered, `Some(false)` not covered, `None` when the two
    /// codes are in a containment relation whose direction is not declared.
    pub covered: Option<bool>,
}

/// The concrete restriction that excluded a rule.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InapplicableReason {
    /// Every reference date is earlier than the rule's first day in force.
    NotYetInForce {
        /// The reference dates that are too early.
        dates: Vec<String>,
        /// The rule's first day in force (inclusive).
        effective_from: String,
    },
    /// Every reference date reached the rule's first day out of force.
    Repealed {
        /// The reference dates that are too late.
        dates: Vec<String>,
        /// The first day the rule is no longer in force (exclusive).
        repealed: String,
    },
    /// The dates are outside the range but not all on the same side of it
    /// (some before the start, some after the end).
    OutsideRange {
        /// The reference dates that are outside.
        dates: Vec<String>,
        /// The declared start, if any.
        effective_from: Option<String>,
        /// The declared end, if any.
        effective_to: Option<String>,
    },
    /// The rule's legal system differs from the case's jurisdiction.
    JurisdictionMismatch {
        /// The rule's `jurisdiction` code.
        rule: String,
        /// The session's `:jurisdiction` code.
        case: String,
    },
    /// The rule's territory covers none of the event places.
    TerritoryMismatch {
        /// The rule's `territory` code.
        rule: String,
        /// The event places that are not covered.
        places: Vec<String>,
    },
}

/// An input the judgement needs but the session or the instance did not
/// provide.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MissingInput {
    /// The rule declares no scope field at all, so there is nothing to judge.
    RuleHasNoScope,
    /// The rule declares an effective range, the instance references no
    /// occurrence date, and the session has no `:asof`.
    NoCaseDate,
    /// Some premise facts record no `occurred_at`, while others do. The known
    /// event times cannot stand in for the unknown ones.
    PartialCaseDate,
    /// The rule declares a territory but no premise fact records
    /// `occurred_in`.
    NoCasePlace,
    /// Some premise facts record no `occurred_in`, while others do. The known
    /// places cannot stand in for the unknown ones.
    PartialCasePlace,
    /// The rule declares a jurisdiction but the session sets no
    /// `:jurisdiction`.
    NoQueryJurisdiction,
}

/// Why complete input still does not decide the judgement.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UndecidableReason {
    /// A stored date is not a `YYYY-MM-DD` calendar day. The loader refuses
    /// such a value, so this can only come from a directly built environment;
    /// it is reported instead of comparing the malformed string.
    InvalidDate {
        /// Which field holds the value.
        field: DateField,
        /// The malformed value.
        value: String,
    },
    /// The range's start is not earlier than its end, so the interval is
    /// empty. The loader refuses such a pair.
    InvertedInterval {
        /// The declared start.
        from: String,
        /// The declared end.
        to: String,
    },
    /// Some reference dates are inside the range and some are outside. The
    /// rule applies to part of the instance's events and not to the rest;
    /// picking one side would be a silent choice.
    PartialDateCoverage {
        /// Dates inside the range.
        covered: Vec<String>,
        /// Dates outside the range.
        outside: Vec<String>,
        /// The declared start, if any.
        effective_from: Option<String>,
        /// The declared end, if any.
        effective_to: Option<String>,
    },
    /// The two codes are in a containment relation (one is a `-`-separated
    /// prefix of the other), so whether the rule covers the event depends on a
    /// hierarchy nobody declared.
    IncomparableCode {
        /// Whether the codes are jurisdictions or territories.
        dimension: CodeDimension,
        /// The rule's code.
        rule: String,
        /// The event's code.
        case: String,
    },
    /// Some event places are covered by the rule's territory and some are not.
    PartialPlaceCoverage {
        /// Places covered by the rule.
        covered: Vec<String>,
        /// Places not covered by the rule.
        uncovered: Vec<String>,
        /// The rule's territory code.
        rule: String,
    },
}

/// A date field whose stored value is malformed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DateField {
    /// The rule's `effective` start.
    EffectiveFrom,
    /// The rule's `repealed` end.
    EffectiveTo,
    /// The session's `:asof`.
    AsOf,
    /// A fact's `occurred_at`.
    OccurredAt,
}

impl DateField {
    /// The Chinese label used in a diagnostic.
    pub fn label_zh(self) -> &'static str {
        match self {
            DateField::EffectiveFrom => "生效起点",
            DateField::EffectiveTo => "废止日",
            DateField::AsOf => "会话基准日",
            DateField::OccurredAt => "事实发生时间",
        }
    }
}

/// Which kind of code could not be compared.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CodeDimension {
    /// Rule `jurisdiction` against session `:jurisdiction`.
    Jurisdiction,
    /// Rule `territory` against a fact's `occurred_in`.
    Territory,
}

impl CodeDimension {
    /// The Chinese label used in a diagnostic.
    pub fn label_zh(self) -> &'static str {
        match self {
            CodeDimension::Jurisdiction => "管辖",
            CodeDimension::Territory => "地域",
        }
    }
}

/// The occurrence records a rule instance references.
///
/// `event_dates` and `event_places` are the records of the premise facts
/// actually bound by the instance. The `missing_*` flags say whether some
/// referenced fact did not record one; a fact that records no occurrence never
/// gets a guessed value. The fields are owned so an anchor can be built from a
/// cached occurrence index without borrowing the reasoner.
#[derive(Debug, Clone, Default)]
pub struct InstanceAnchor {
    /// The session's legal as-of date, used only when no event time exists.
    pub as_of: Option<String>,
    /// The session's jurisdiction code, when set.
    pub jurisdiction: Option<String>,
    /// `occurred_at` values of the referenced premise facts.
    pub event_dates: Vec<String>,
    /// Whether some referenced premise fact records no `occurred_at`.
    pub missing_event_date: bool,
    /// `occurred_in` values of the referenced premise facts.
    pub event_places: Vec<String>,
    /// Whether some referenced premise fact records no `occurred_in`.
    pub missing_event_place: bool,
}

impl Applicability {
    /// Whether the rule instance may fire under this judgement.
    ///
    /// Only `未判定` (no evidence at all) keeps the old firing behaviour: with
    /// no evidence, excluding the rule would be a guess. `不适用` and
    /// `无法判定` both block the instance — an undecidable partial coverage has
    /// already shown that the rule does not wholly govern the referenced
    /// events, so using it would turn a contradiction into a premise. Every
    /// blocked instance is still listed by `:gap` / `:issues`.
    pub fn allows_firing(&self) -> bool {
        matches!(
            self,
            Applicability::Applicable { .. } | Applicability::Unchecked { .. }
        )
    }

    /// Whether this is the positive decision.
    pub fn is_applicable(&self) -> bool {
        matches!(self, Applicability::Applicable { .. })
    }

    /// The short Chinese label: `适用` / `不适用` / `未判定` / `无法判定`.
    pub fn label_zh(&self) -> &'static str {
        match self {
            Applicability::Applicable { .. } => "适用",
            Applicability::Inapplicable { .. } => "不适用",
            Applicability::Unchecked { .. } => "未判定",
            Applicability::Undecidable { .. } => "无法判定",
        }
    }

    /// The evidence this judgement relied on.
    pub fn basis(&self) -> &Basis {
        match self {
            Applicability::Applicable { basis }
            | Applicability::Inapplicable { basis, .. }
            | Applicability::Unchecked { basis, .. }
            | Applicability::Undecidable { basis, .. } => basis,
        }
    }

    /// The one-line Chinese summary used by `:applicability`, `:why`,
    /// `:explain` and `:gap`, with the concrete reason and the evidence.
    pub fn summary_zh(&self) -> String {
        match self {
            Applicability::Applicable { basis } => {
                let evidence = basis.text_zh();
                if evidence.is_empty() {
                    "适用".to_owned()
                } else {
                    format!("适用（{evidence}）")
                }
            }
            Applicability::Inapplicable { reason, basis } => {
                let mut summary = format!("不适用（{}）", reason.text_zh());
                if basis.dates.iter().any(|dated| dated.query_date_fallback) {
                    summary.push_str(&format!("；依据：{}", basis.text_zh()));
                }
                summary
            }
            Applicability::Unchecked { missing, basis } => {
                let evidence = basis.text_zh();
                if evidence.is_empty() {
                    format!("适用性未判定（{}）", missing.text_zh())
                } else {
                    format!("适用性未判定（{}；已记录：{evidence}）", missing.text_zh())
                }
            }
            Applicability::Undecidable { reason, .. } => {
                format!("适用性无法判定（{}）", reason.text_zh())
            }
        }
    }
}

impl Basis {
    /// The evidence in one Chinese clause: `事件时间 …；事件地点 …`.
    ///
    /// A query date that stood in for an event time says so explicitly
    /// (`以查询基准日 … 代替行为时`); it is never presented as a fact's
    /// occurrence.
    pub fn text_zh(&self) -> String {
        let mut parts = Vec::new();
        if !self.dates.is_empty() {
            let mut items = Vec::new();
            for dated in &self.dates {
                let coverage = if dated.covered {
                    "区间内"
                } else {
                    "区间外"
                };
                if dated.query_date_fallback {
                    items.push(format!(
                        "以查询基准日 {} 代替行为时（{coverage}）",
                        escape_control(&dated.date)
                    ));
                } else {
                    items.push(format!(
                        "事件时间 {}（{coverage}）",
                        escape_control(&dated.date)
                    ));
                }
            }
            parts.push(items.join("、"));
        }
        if !self.places.is_empty() {
            let mut items = Vec::new();
            for place in &self.places {
                let coverage = match place.covered {
                    Some(true) => "覆盖",
                    Some(false) => "不覆盖",
                    None => "层级未声明",
                };
                items.push(format!("{}（{coverage}）", escape_control(&place.place)));
            }
            parts.push(format!("事件地点 {}", items.join("、")));
        }
        parts.join("；")
    }
}

impl MissingInput {
    /// Why the judgement is unchecked, in one Chinese sentence.
    pub fn text_zh(self) -> &'static str {
        match self {
            MissingInput::RuleHasNoScope => "规则没有声明任何范围",
            MissingInput::NoCaseDate => {
                "规则声明了生效区间，但实例引用的前提事实没有发生时间，会话也未设置 :asof"
            }
            MissingInput::PartialCaseDate => "部分前提事实没有发生时间，已知事件时间不能代表它们",
            MissingInput::NoCasePlace => "规则声明了地域，但实例引用的前提事实都没有记录发生地点",
            MissingInput::PartialCasePlace => "部分前提事实没有记录发生地点，已知地点不能代表它们",
            MissingInput::NoQueryJurisdiction => "规则声明了管辖，但会话未设置 :jurisdiction",
        }
    }
}

impl InapplicableReason {
    /// The concrete reason in one Chinese sentence.
    pub fn text_zh(&self) -> String {
        match self {
            InapplicableReason::NotYetInForce {
                dates,
                effective_from,
            } => format!(
                "事件时间 {} 早于规则生效日 {}，规则当时尚未生效",
                escape_dates(dates),
                escape_control(effective_from)
            ),
            InapplicableReason::Repealed { dates, repealed } => format!(
                "事件时间 {} 已达到规则废止日 {}，规则已经失效",
                escape_dates(dates),
                escape_control(repealed)
            ),
            InapplicableReason::OutsideRange {
                dates,
                effective_from,
                effective_to,
            } => format!(
                "事件时间 {} 全部落在规则生效区间 {} 之外",
                escape_dates(dates),
                range_text(effective_from.as_deref(), effective_to.as_deref())
            ),
            InapplicableReason::JurisdictionMismatch { rule, case } => format!(
                "规则管辖 {} 与案件管辖 {} 不同",
                escape_control(rule),
                escape_control(case)
            ),
            InapplicableReason::TerritoryMismatch { rule, places } => format!(
                "规则地域 {} 不覆盖事件地点 {}",
                escape_control(rule),
                escape_dates(places)
            ),
        }
    }
}

impl UndecidableReason {
    /// Why the complete input cannot decide, in one Chinese sentence.
    pub fn text_zh(&self) -> String {
        match self {
            UndecidableReason::InvalidDate { field, value } => format!(
                "{}「{}」不是 YYYY-MM-DD 日期，无法比较",
                field.label_zh(),
                escape_control(value)
            ),
            UndecidableReason::InvertedInterval { from, to } => format!(
                "生效起点 {} 不早于废止日 {}，区间为空或倒置",
                escape_control(from),
                escape_control(to)
            ),
            UndecidableReason::PartialDateCoverage {
                covered,
                outside,
                effective_from,
                effective_to,
            } => format!(
                "事件时间 {} 在生效区间 {} 内，{} 不在其中；部分覆盖不能当作适用",
                escape_dates(covered),
                range_text(effective_from.as_deref(), effective_to.as_deref()),
                escape_dates(outside)
            ),
            UndecidableReason::IncomparableCode {
                dimension,
                rule,
                case,
            } => {
                let other = match dimension {
                    CodeDimension::Jurisdiction => "案件管辖",
                    CodeDimension::Territory => "事件地域",
                };
                format!(
                    "规则{} {} 与{} {} 是上下位关系但未声明层级，无法比较",
                    dimension.label_zh(),
                    escape_control(rule),
                    other,
                    escape_control(case)
                )
            }
            UndecidableReason::PartialPlaceCoverage {
                covered,
                uncovered,
                rule,
            } => format!(
                "事件地点 {} 在规则地域 {} 内，{} 不在其中；部分覆盖不能当作适用",
                escape_dates(covered),
                escape_control(rule),
                escape_dates(uncovered)
            ),
        }
    }
}

/// Judge one rule instance's recorded scope against its event time and place.
///
/// The judgement itself lives in the certificate crate
/// ([`std_deduce_cert::judge_applicability`]), because the certificate checker
/// must recompute it from the certificate's own inputs without calling the
/// reasoner. This function only supplies the anchor built from the premise
/// facts' occurrence records and converts the result into the display type the
/// reasoner, `:why`, `:gap` and `:applicability` print.
pub fn judge(scope: &Scope, case: &InstanceAnchor) -> Applicability {
    let anchor = std_deduce_cert::ApplicabilityAnchor {
        as_of: case.as_of.clone(),
        jurisdiction: case.jurisdiction.clone(),
        event_dates: case.event_dates.clone(),
        missing_event_date: case.missing_event_date,
        event_places: case.event_places.clone(),
        missing_event_place: case.missing_event_place,
    };
    from_certificate(std_deduce_cert::judge_applicability(scope, &anchor))
}

/// Convert the certificate-side judgement into the display type.
fn from_certificate(value: std_deduce_cert::RuleApplicability) -> Applicability {
    let basis = basis_from_certificate(&value.basis);
    match value.verdict {
        std_deduce_cert::ApplicabilityVerdict::Applicable => Applicability::Applicable { basis },
        std_deduce_cert::ApplicabilityVerdict::Inapplicable => Applicability::Inapplicable {
            reason: inapplicable_reason(value.reason(), &value.verdict),
            basis,
        },
        std_deduce_cert::ApplicabilityVerdict::Unchecked => Applicability::Unchecked {
            missing: missing_input(value.reason(), &value.verdict),
            basis,
        },
        std_deduce_cert::ApplicabilityVerdict::Undecidable => Applicability::Undecidable {
            reason: undecidable_reason(value.reason(), &value.verdict),
            basis,
        },
    }
}

/// The certificate-side basis in the display form.
fn basis_from_certificate(basis: &std_deduce_cert::ApplicabilityBasis) -> Basis {
    Basis {
        dates: basis
            .dates
            .iter()
            .map(|dated| DatedEvidence {
                date: dated.date.clone(),
                query_date_fallback: dated.query_date_fallback,
                covered: dated.covered,
            })
            .collect(),
        places: basis
            .places
            .iter()
            .map(|place| PlaceEvidence {
                place: place.place.clone(),
                covered: place.covered,
            })
            .collect(),
        missing_event_date: basis.missing_event_date,
        missing_event_place: basis.missing_event_place,
        session_as_of: basis.session.as_of.as_ref().cloned(),
        session_jurisdiction: basis.session.jurisdiction.as_ref().cloned(),
    }
}

/// The certificate-side reason, which a non-applicable verdict always carries.
fn required_reason(
    reason: Option<&std_deduce_cert::ApplicabilityReason>,
) -> &std_deduce_cert::ApplicabilityReason {
    match reason {
        Some(reason) => reason,
        None => panic!("内部状态不一致：非适用的适用性判定没有记录原因"),
    }
}

fn missing_input(
    reason: Option<&std_deduce_cert::ApplicabilityReason>,
    verdict: &std_deduce_cert::ApplicabilityVerdict,
) -> MissingInput {
    let reason = required_reason(reason);
    match &reason.detail {
        std_deduce_cert::ApplicabilityReasonKind::RuleHasNoScope => MissingInput::RuleHasNoScope,
        std_deduce_cert::ApplicabilityReasonKind::NoCaseDate => MissingInput::NoCaseDate,
        std_deduce_cert::ApplicabilityReasonKind::PartialCaseDate => MissingInput::PartialCaseDate,
        std_deduce_cert::ApplicabilityReasonKind::NoCasePlace => MissingInput::NoCasePlace,
        std_deduce_cert::ApplicabilityReasonKind::PartialCasePlace => {
            MissingInput::PartialCasePlace
        }
        std_deduce_cert::ApplicabilityReasonKind::NoQueryJurisdiction => {
            MissingInput::NoQueryJurisdiction
        }
        other => panic!(
            "内部状态不一致：{} 的未判定原因 `{}` 不是缺失输入",
            verdict.keyword(),
            other.code()
        ),
    }
}

fn inapplicable_reason(
    reason: Option<&std_deduce_cert::ApplicabilityReason>,
    verdict: &std_deduce_cert::ApplicabilityVerdict,
) -> InapplicableReason {
    let reason = required_reason(reason);
    match &reason.detail {
        std_deduce_cert::ApplicabilityReasonKind::NotYetInForce {
            dates,
            effective_from,
        } => InapplicableReason::NotYetInForce {
            dates: dates.clone(),
            effective_from: effective_from.clone(),
        },
        std_deduce_cert::ApplicabilityReasonKind::Repealed { dates, repealed } => {
            InapplicableReason::Repealed {
                dates: dates.clone(),
                repealed: repealed.clone(),
            }
        }
        std_deduce_cert::ApplicabilityReasonKind::OutsideRange {
            dates,
            effective_from,
            effective_to,
        } => InapplicableReason::OutsideRange {
            dates: dates.clone(),
            effective_from: effective_from.as_ref().cloned(),
            effective_to: effective_to.as_ref().cloned(),
        },
        std_deduce_cert::ApplicabilityReasonKind::JurisdictionMismatch { rule, case } => {
            InapplicableReason::JurisdictionMismatch {
                rule: rule.clone(),
                case: case.clone(),
            }
        }
        std_deduce_cert::ApplicabilityReasonKind::TerritoryMismatch { rule, places } => {
            InapplicableReason::TerritoryMismatch {
                rule: rule.clone(),
                places: places.clone(),
            }
        }
        other => panic!(
            "内部状态不一致：{} 的不适用原因 `{}` 不是排除理由",
            verdict.keyword(),
            other.code()
        ),
    }
}

fn undecidable_reason(
    reason: Option<&std_deduce_cert::ApplicabilityReason>,
    verdict: &std_deduce_cert::ApplicabilityVerdict,
) -> UndecidableReason {
    let reason = required_reason(reason);
    match &reason.detail {
        std_deduce_cert::ApplicabilityReasonKind::InvalidDate { field, value } => {
            UndecidableReason::InvalidDate {
                field: date_field(*field),
                value: value.clone(),
            }
        }
        std_deduce_cert::ApplicabilityReasonKind::InvertedInterval { from, to } => {
            UndecidableReason::InvertedInterval {
                from: from.clone(),
                to: to.clone(),
            }
        }
        std_deduce_cert::ApplicabilityReasonKind::PartialDateCoverage {
            covered,
            outside,
            effective_from,
            effective_to,
        } => UndecidableReason::PartialDateCoverage {
            covered: covered.clone(),
            outside: outside.clone(),
            effective_from: effective_from.as_ref().cloned(),
            effective_to: effective_to.as_ref().cloned(),
        },
        std_deduce_cert::ApplicabilityReasonKind::IncomparableCode {
            dimension,
            rule,
            case,
        } => UndecidableReason::IncomparableCode {
            dimension: code_dimension(*dimension),
            rule: rule.clone(),
            case: case.clone(),
        },
        std_deduce_cert::ApplicabilityReasonKind::PartialPlaceCoverage {
            covered,
            uncovered,
            rule,
        } => UndecidableReason::PartialPlaceCoverage {
            covered: covered.clone(),
            uncovered: uncovered.clone(),
            rule: rule.clone(),
        },
        other => panic!(
            "内部状态不一致：{} 的无法判定原因 `{}` 不是判定理由",
            verdict.keyword(),
            other.code()
        ),
    }
}

fn date_field(field: std_deduce_cert::DateField) -> DateField {
    match field {
        std_deduce_cert::DateField::EffectiveFrom => DateField::EffectiveFrom,
        std_deduce_cert::DateField::EffectiveTo => DateField::EffectiveTo,
        std_deduce_cert::DateField::AsOf => DateField::AsOf,
        std_deduce_cert::DateField::OccurredAt => DateField::OccurredAt,
    }
}

fn code_dimension(dimension: std_deduce_cert::CodeDimension) -> CodeDimension {
    match dimension {
        std_deduce_cert::CodeDimension::Jurisdiction => CodeDimension::Jurisdiction,
        std_deduce_cert::CodeDimension::Territory => CodeDimension::Territory,
    }
}

/// Convert the display judgement into the certificate's record for one rule
/// application or gap candidate.
///
/// `scope` is the applied rule's environment declaration; it is the only part
/// of the record the reasoner's judgement does not already carry.
pub(crate) fn certificate_applicability(
    scope: &Scope,
    value: &Applicability,
) -> std_deduce_cert::RuleApplicability {
    let basis = std_deduce_cert::ApplicabilityBasis {
        dates: value
            .basis()
            .dates
            .iter()
            .map(|dated| std_deduce_cert::DatedEvidence {
                date: dated.date.clone(),
                query_date_fallback: dated.query_date_fallback,
                covered: dated.covered,
            })
            .collect(),
        places: value
            .basis()
            .places
            .iter()
            .map(|place| std_deduce_cert::PlaceEvidence {
                place: place.place.clone(),
                covered: place.covered,
            })
            .collect(),
        missing_event_date: value.basis().missing_event_date,
        missing_event_place: value.basis().missing_event_place,
        scope: std_deduce_cert::ScopeEvidence::of(scope),
        session: std_deduce_cert::SessionEvidence {
            as_of: explicit_option(value.basis().session_as_of.clone()),
            jurisdiction: explicit_option(value.basis().session_jurisdiction.clone()),
        },
    };
    let (verdict, reason) = match value {
        Applicability::Applicable { .. } => {
            (std_deduce_cert::ApplicabilityVerdict::Applicable, None)
        }
        Applicability::Inapplicable { reason, .. } => (
            std_deduce_cert::ApplicabilityVerdict::Inapplicable,
            Some(inapplicable_kind(reason)),
        ),
        Applicability::Unchecked { missing, .. } => (
            std_deduce_cert::ApplicabilityVerdict::Unchecked,
            Some(missing_kind(*missing)),
        ),
        Applicability::Undecidable { reason, .. } => (
            std_deduce_cert::ApplicabilityVerdict::Undecidable,
            Some(undecidable_kind(reason)),
        ),
    };
    std_deduce_cert::RuleApplicability {
        verdict,
        basis,
        reason: match reason {
            Some(kind) => {
                std_deduce_cert::Explicit::some(std_deduce_cert::ApplicabilityReason::new(kind))
            }
            None => std_deduce_cert::Explicit::none(),
        },
    }
}

fn explicit_option(value: Option<String>) -> std_deduce_cert::Explicit<String> {
    match value {
        Some(value) => std_deduce_cert::Explicit::some(value),
        None => std_deduce_cert::Explicit::none(),
    }
}

fn missing_kind(missing: MissingInput) -> std_deduce_cert::ApplicabilityReasonKind {
    match missing {
        MissingInput::RuleHasNoScope => std_deduce_cert::ApplicabilityReasonKind::RuleHasNoScope,
        MissingInput::NoCaseDate => std_deduce_cert::ApplicabilityReasonKind::NoCaseDate,
        MissingInput::PartialCaseDate => std_deduce_cert::ApplicabilityReasonKind::PartialCaseDate,
        MissingInput::NoCasePlace => std_deduce_cert::ApplicabilityReasonKind::NoCasePlace,
        MissingInput::PartialCasePlace => {
            std_deduce_cert::ApplicabilityReasonKind::PartialCasePlace
        }
        MissingInput::NoQueryJurisdiction => {
            std_deduce_cert::ApplicabilityReasonKind::NoQueryJurisdiction
        }
    }
}

fn inapplicable_kind(reason: &InapplicableReason) -> std_deduce_cert::ApplicabilityReasonKind {
    match reason {
        InapplicableReason::NotYetInForce {
            dates,
            effective_from,
        } => std_deduce_cert::ApplicabilityReasonKind::NotYetInForce {
            dates: dates.clone(),
            effective_from: effective_from.clone(),
        },
        InapplicableReason::Repealed { dates, repealed } => {
            std_deduce_cert::ApplicabilityReasonKind::Repealed {
                dates: dates.clone(),
                repealed: repealed.clone(),
            }
        }
        InapplicableReason::OutsideRange {
            dates,
            effective_from,
            effective_to,
        } => std_deduce_cert::ApplicabilityReasonKind::OutsideRange {
            dates: dates.clone(),
            effective_from: explicit_option(effective_from.clone()),
            effective_to: explicit_option(effective_to.clone()),
        },
        InapplicableReason::JurisdictionMismatch { rule, case } => {
            std_deduce_cert::ApplicabilityReasonKind::JurisdictionMismatch {
                rule: rule.clone(),
                case: case.clone(),
            }
        }
        InapplicableReason::TerritoryMismatch { rule, places } => {
            std_deduce_cert::ApplicabilityReasonKind::TerritoryMismatch {
                rule: rule.clone(),
                places: places.clone(),
            }
        }
    }
}

fn undecidable_kind(reason: &UndecidableReason) -> std_deduce_cert::ApplicabilityReasonKind {
    match reason {
        UndecidableReason::InvalidDate { field, value } => {
            std_deduce_cert::ApplicabilityReasonKind::InvalidDate {
                field: cert_date_field(*field),
                value: value.clone(),
            }
        }
        UndecidableReason::InvertedInterval { from, to } => {
            std_deduce_cert::ApplicabilityReasonKind::InvertedInterval {
                from: from.clone(),
                to: to.clone(),
            }
        }
        UndecidableReason::PartialDateCoverage {
            covered,
            outside,
            effective_from,
            effective_to,
        } => std_deduce_cert::ApplicabilityReasonKind::PartialDateCoverage {
            covered: covered.clone(),
            outside: outside.clone(),
            effective_from: explicit_option(effective_from.clone()),
            effective_to: explicit_option(effective_to.clone()),
        },
        UndecidableReason::IncomparableCode {
            dimension,
            rule,
            case,
        } => std_deduce_cert::ApplicabilityReasonKind::IncomparableCode {
            dimension: cert_code_dimension(*dimension),
            rule: rule.clone(),
            case: case.clone(),
        },
        UndecidableReason::PartialPlaceCoverage {
            covered,
            uncovered,
            rule,
        } => std_deduce_cert::ApplicabilityReasonKind::PartialPlaceCoverage {
            covered: covered.clone(),
            uncovered: uncovered.clone(),
            rule: rule.clone(),
        },
    }
}

fn cert_date_field(field: DateField) -> std_deduce_cert::DateField {
    match field {
        DateField::EffectiveFrom => std_deduce_cert::DateField::EffectiveFrom,
        DateField::EffectiveTo => std_deduce_cert::DateField::EffectiveTo,
        DateField::AsOf => std_deduce_cert::DateField::AsOf,
        DateField::OccurredAt => std_deduce_cert::DateField::OccurredAt,
    }
}

fn cert_code_dimension(dimension: CodeDimension) -> std_deduce_cert::CodeDimension {
    match dimension {
        CodeDimension::Jurisdiction => std_deduce_cert::CodeDimension::Jurisdiction,
        CodeDimension::Territory => std_deduce_cert::CodeDimension::Territory,
    }
}

fn escape_dates(dates: &[String]) -> String {
    dates
        .iter()
        .map(|date| escape_control(date))
        .collect::<Vec<_>>()
        .join("、")
}

fn range_text(from: Option<&str>, to: Option<&str>) -> String {
    match (from, to) {
        (Some(from), Some(to)) => {
            format!("{}..{}", escape_control(from), escape_control(to))
        }
        (Some(from), None) => format!("{}..", escape_control(from)),
        (None, Some(to)) => format!("..{}", escape_control(to)),
        (None, None) => "（无端点）".to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scope(
        from: Option<&str>,
        to: Option<&str>,
        jurisdiction: Option<&str>,
        territory: Option<&str>,
    ) -> Scope {
        Scope {
            effective_from: from.map(ToOwned::to_owned),
            effective_to: to.map(ToOwned::to_owned),
            jurisdiction: jurisdiction.map(ToOwned::to_owned),
            territory: territory.map(ToOwned::to_owned),
            ..Scope::default()
        }
    }

    fn anchor(
        as_of: Option<&str>,
        jurisdiction: Option<&str>,
        dates: &[&str],
        places: &[&str],
    ) -> InstanceAnchor {
        InstanceAnchor {
            as_of: as_of.map(ToOwned::to_owned),
            jurisdiction: jurisdiction.map(ToOwned::to_owned),
            event_dates: dates.iter().map(|date| (*date).to_owned()).collect(),
            missing_event_date: false,
            event_places: places.iter().map(|place| (*place).to_owned()).collect(),
            missing_event_place: false,
        }
    }

    fn dated(as_of: Option<&str>, dates: &[&str]) -> InstanceAnchor {
        anchor(as_of, None, dates, &[])
    }

    fn applicable_dates(dates: &[&str]) -> InstanceAnchor {
        anchor(None, None, dates, &[])
    }

    #[test]
    fn every_event_date_inside_a_closed_range_applies_and_lists_the_dates() {
        let s = scope(Some("2019-01-01"), Some("2021-01-01"), None, None);
        let verdict = judge(&s, &applicable_dates(&["2020-06-01"]));
        let Applicability::Applicable { basis } = verdict else {
            panic!("expected applicable, got {verdict:?}");
        };
        assert_eq!(basis.dates.len(), 1);
        assert_eq!(basis.dates[0].date, "2020-06-01");
        assert!(basis.dates[0].covered);
        assert!(!basis.dates[0].query_date_fallback);
        // Both endpoints are half-open: the start is inclusive, the end is
        // the first day out of force.
        assert!(judge(&s, &applicable_dates(&["2019-01-01"])).is_applicable());
        assert!(matches!(
            judge(&s, &applicable_dates(&["2021-01-01"])),
            Applicability::Inapplicable {
                reason: InapplicableReason::Repealed { .. },
                ..
            }
        ));
        assert!(matches!(
            judge(&s, &applicable_dates(&["2018-12-31"])),
            Applicability::Inapplicable {
                reason: InapplicableReason::NotYetInForce { .. },
                ..
            }
        ));
    }

    #[test]
    fn a_query_date_never_overrides_a_recorded_event_date() {
        // The rule was in force when the contract was signed, and was repealed
        // before the query: it still governs the old event.
        let s = scope(Some("1999-01-01"), Some("2021-01-01"), None, None);
        let verdict = judge(&s, &dated(Some("2026-01-01"), &["2019-05-01"]));
        assert!(verdict.is_applicable());
        assert!(
            !verdict.basis().dates[0].query_date_fallback,
            "the event date must be the reference, not the query date"
        );
        // Conversely, a query date inside the range does not revive a rule for
        // an event that happened after its repeal.
        let verdict = judge(&s, &dated(Some("2019-06-01"), &["2022-06-01"]));
        assert!(matches!(
            verdict,
            Applicability::Inapplicable {
                reason: InapplicableReason::Repealed { .. },
                ..
            }
        ));
    }

    #[test]
    fn an_open_start_applies_from_its_first_day_onward() {
        let s = scope(Some("2021-01-01"), None, None, None);
        assert!(judge(&s, &applicable_dates(&["2021-01-01"])).is_applicable());
        assert!(judge(&s, &applicable_dates(&["2030-01-01"])).is_applicable());
        assert!(matches!(
            judge(&s, &applicable_dates(&["2020-12-31"])),
            Applicability::Inapplicable {
                reason: InapplicableReason::NotYetInForce { .. },
                ..
            }
        ));
    }

    #[test]
    fn an_open_end_applies_until_its_last_day() {
        let s = scope(None, Some("2021-01-01"), None, None);
        assert!(judge(&s, &applicable_dates(&["2000-01-01"])).is_applicable());
        assert!(judge(&s, &applicable_dates(&["2020-12-31"])).is_applicable());
        assert!(matches!(
            judge(&s, &applicable_dates(&["2021-01-01"])),
            Applicability::Inapplicable {
                reason: InapplicableReason::Repealed { .. },
                ..
            }
        ));
    }

    #[test]
    fn a_rule_that_has_no_event_time_and_only_an_open_start_still_needs_a_date() {
        let s = scope(Some("2021-01-01"), None, None, None);
        let verdict = judge(&s, &dated(None, &[]));
        assert_eq!(
            verdict,
            Applicability::Unchecked {
                missing: MissingInput::NoCaseDate,
                basis: Basis::default(),
            }
        );
    }

    #[test]
    fn partial_event_coverage_is_undecidable_and_lists_both_sides() {
        let s = scope(Some("2019-01-01"), Some("2021-01-01"), None, None);
        let verdict = judge(&s, &applicable_dates(&["2020-01-01", "2022-01-01"]));
        assert!(!verdict.allows_firing(), "partial coverage must not fire");
        let Applicability::Undecidable {
            reason:
                UndecidableReason::PartialDateCoverage {
                    covered, outside, ..
                },
            basis,
        } = verdict
        else {
            panic!("expected partial coverage");
        };
        assert_eq!(covered, ["2020-01-01"]);
        assert_eq!(outside, ["2022-01-01"]);
        assert_eq!(basis.dates.len(), 2);
        assert!(basis.dates[0].covered);
        assert!(!basis.dates[1].covered);
    }

    #[test]
    fn all_event_dates_outside_is_inapplicable_and_lists_them() {
        let s = scope(Some("2019-01-01"), Some("2021-01-01"), None, None);
        let verdict = judge(&s, &applicable_dates(&["2010-01-01", "2022-01-01"]));
        let Applicability::Inapplicable {
            reason: InapplicableReason::OutsideRange { dates, .. },
            basis,
        } = verdict
        else {
            panic!("expected outside-range, got {verdict:?}");
        };
        assert_eq!(dates, ["2010-01-01", "2022-01-01"]);
        assert_eq!(basis.dates.len(), 2);
        assert!(basis.dates.iter().all(|dated| !dated.covered));
    }

    #[test]
    fn asof_is_only_a_fallback_when_no_event_time_exists() {
        let s = scope(Some("2021-01-01"), None, None, None);
        let verdict = judge(&s, &dated(Some("2022-01-01"), &[]));
        let summary = verdict.summary_zh();
        let Applicability::Applicable { basis } = verdict else {
            panic!("expected applicable fallback");
        };
        assert_eq!(basis.dates.len(), 1);
        assert_eq!(basis.dates[0].date, "2022-01-01");
        assert!(basis.dates[0].query_date_fallback);
        assert!(summary.contains("以查询基准日 2022-01-01 代替行为时"));
    }

    #[test]
    fn no_event_time_and_no_asof_is_unchecked() {
        let s = scope(Some("2021-01-01"), Some("2025-01-01"), None, None);
        let verdict = judge(&s, &dated(None, &[]));
        assert_eq!(
            verdict,
            Applicability::Unchecked {
                missing: MissingInput::NoCaseDate,
                basis: Basis::default(),
            }
        );
        assert!(verdict.allows_firing());
    }

    #[test]
    fn a_fact_without_an_occurrence_date_is_never_covered_by_one_that_has_it() {
        let s = scope(Some("2019-01-01"), Some("2021-01-01"), None, None);
        let mut case = dated(Some("2020-01-01"), &["2020-01-01"]);
        case.missing_event_date = true;
        let verdict = judge(&s, &case);
        assert!(verdict.allows_firing());
        let Applicability::Unchecked { missing, basis } = verdict else {
            panic!("expected unchecked");
        };
        assert_eq!(missing, MissingInput::PartialCaseDate);
        assert_eq!(basis.dates.len(), 1);
    }

    #[test]
    fn a_date_the_loader_would_refuse_is_undecidable_not_a_guess() {
        let s = scope(Some("2021-01-01"), None, None, None);
        let verdict = judge(&s, &dated(Some("2021-02-30"), &[]));
        assert!(matches!(
            verdict,
            Applicability::Undecidable {
                reason: UndecidableReason::InvalidDate {
                    field: DateField::AsOf,
                    ..
                },
                ..
            }
        ));
        let s = scope(Some("2021-02-30"), None, None, None);
        assert!(matches!(
            judge(&s, &dated(Some("2021-06-01"), &[])),
            Applicability::Undecidable {
                reason: UndecidableReason::InvalidDate {
                    field: DateField::EffectiveFrom,
                    ..
                },
                ..
            }
        ));
    }

    #[test]
    fn an_inverted_or_empty_interval_is_undecidable() {
        let s = scope(Some("2021-01-01"), Some("2021-01-01"), None, None);
        assert!(matches!(
            judge(&s, &dated(Some("2020-01-01"), &[])),
            Applicability::Undecidable {
                reason: UndecidableReason::InvertedInterval { .. },
                ..
            }
        ));
    }

    #[test]
    fn equal_disjoint_and_nested_jurisdiction_codes() {
        let s = scope(None, None, Some("CN"), None);
        assert!(judge(&s, &anchor(None, Some("CN"), &[], &[])).is_applicable());
        assert!(matches!(
            judge(&s, &anchor(None, Some("JP"), &[], &[])),
            Applicability::Inapplicable {
                reason: InapplicableReason::JurisdictionMismatch { .. },
                ..
            }
        ));
        assert!(matches!(
            judge(&s, &anchor(None, Some("CN-HN"), &[], &[])),
            Applicability::Undecidable {
                reason: UndecidableReason::IncomparableCode {
                    dimension: CodeDimension::Jurisdiction,
                    ..
                },
                ..
            }
        ));
        let message = judge(&s, &anchor(None, Some("CN-HN"), &[], &[])).summary_zh();
        assert!(
            message.contains("案件管辖 CN-HN"),
            "the jurisdiction dimension names the case's jurisdiction: {message}"
        );
        assert_eq!(
            judge(&s, &anchor(None, None, &[], &[])),
            Applicability::Unchecked {
                missing: MissingInput::NoQueryJurisdiction,
                basis: Basis::default(),
            }
        );
    }

    #[test]
    fn every_event_place_must_be_covered_by_the_territory() {
        let s = scope(None, None, None, Some("CN-HN"));
        let verdict = judge(&s, &anchor(None, None, &[], &["CN-HN", "CN-HN"]));
        assert!(verdict.is_applicable());
        assert_eq!(
            verdict.basis().places,
            [PlaceEvidence {
                place: "CN-HN".into(),
                covered: Some(true),
            }]
        );
        assert!(matches!(
            judge(&s, &anchor(None, None, &[], &["CN-BJ"])),
            Applicability::Inapplicable {
                reason: InapplicableReason::TerritoryMismatch { .. },
                ..
            }
        ));
        assert_eq!(
            judge(&s, &anchor(None, None, &[], &[])),
            Applicability::Unchecked {
                missing: MissingInput::NoCasePlace,
                basis: Basis::default(),
            }
        );
        assert!(matches!(
            judge(&s, &anchor(None, None, &[], &["CN"])),
            Applicability::Undecidable {
                reason: UndecidableReason::IncomparableCode {
                    dimension: CodeDimension::Territory,
                    ..
                },
                ..
            }
        ));
        let message = judge(&s, &anchor(None, None, &[], &["CN"])).summary_zh();
        assert!(
            message.contains("事件地域 CN"),
            "the territory dimension names the event's place: {message}"
        );
    }

    #[test]
    fn partial_territory_coverage_is_undecidable_and_lists_both_sides() {
        let s = scope(None, None, None, Some("CN-HN"));
        let verdict = judge(&s, &anchor(None, None, &[], &["CN-HN", "CN-BJ"]));
        assert!(!verdict.allows_firing(), "partial coverage must not fire");
        let Applicability::Undecidable {
            reason:
                UndecidableReason::PartialPlaceCoverage {
                    covered, uncovered, ..
                },
            basis,
        } = verdict
        else {
            panic!("expected partial place coverage");
        };
        assert_eq!(covered, ["CN-HN"]);
        assert_eq!(uncovered, ["CN-BJ"]);
        assert_eq!(basis.places.len(), 2);
        assert_eq!(basis.places[0].covered, Some(true));
        assert_eq!(basis.places[1].covered, Some(false));
    }

    #[test]
    fn a_fact_without_a_place_is_not_represented_by_one_that_has_it() {
        let s = scope(None, None, None, Some("CN-HN"));
        let mut case = anchor(None, None, &[], &["CN-HN"]);
        case.missing_event_place = true;
        let verdict = judge(&s, &case);
        assert!(verdict.allows_firing());
        let Applicability::Unchecked { missing, basis } = verdict else {
            panic!("expected unchecked");
        };
        assert_eq!(missing, MissingInput::PartialCasePlace);
        assert_eq!(basis.places.len(), 1);
    }

    #[test]
    fn a_rule_without_any_scope_is_unchecked_even_when_the_case_has_values() {
        let s = scope(None, None, None, None);
        let verdict = judge(
            &s,
            &anchor(Some("2020-01-01"), Some("CN"), &["2020-01-01"], &["CN"]),
        );
        assert_eq!(
            verdict,
            Applicability::Unchecked {
                missing: MissingInput::RuleHasNoScope,
                basis: Basis::default(),
            }
        );
    }

    #[test]
    fn inapplicable_outranks_missing_and_missing_outranks_undecidable() {
        // A certain temporal exclusion wins over a missing jurisdiction.
        let s = scope(Some("2021-01-01"), None, Some("CN"), None);
        assert!(matches!(
            judge(&s, &anchor(Some("2019-01-01"), None, &[], &[])),
            Applicability::Inapplicable { .. }
        ));

        // Missing input is reported before an undecidable comparison: the user
        // can fix the missing input, while the code relation is not something
        // to act on first.
        let s = scope(None, None, Some("CN"), Some("CN-BJ"));
        let verdict = judge(&s, &anchor(None, None, &[], &["CN"]));
        let Applicability::Unchecked { missing, .. } = verdict else {
            panic!("expected unchecked, got {verdict:?}");
        };
        assert_eq!(missing, MissingInput::NoQueryJurisdiction);
    }

    #[test]
    fn only_applicable_and_unchecked_verdicts_allow_firing() {
        assert!(Applicability::Applicable {
            basis: Basis::default()
        }
        .allows_firing());
        assert!(Applicability::Unchecked {
            missing: MissingInput::NoCaseDate,
            basis: Basis::default()
        }
        .allows_firing());
        // A known partial exclusion already shows the rule does not wholly
        // govern the instance; it must not fire.
        assert!(!Applicability::Undecidable {
            reason: UndecidableReason::InvertedInterval {
                from: "2021-01-01".into(),
                to: "2020-01-01".into(),
            },
            basis: Basis::default(),
        }
        .allows_firing());
        assert!(!Applicability::Inapplicable {
            reason: InapplicableReason::JurisdictionMismatch {
                rule: "CN".into(),
                case: "JP".into(),
            },
            basis: Basis::default(),
        }
        .allows_firing());
    }
}
