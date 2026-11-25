//! The temporal/spatial applicability judgement a certificate records.
//!
//! A [`RuleApplicability`] is data, not a summary: the verdict, the reference
//! dates and places the judgement looked at, the rule's declared scope, the
//! session fallback values actually used, and the concrete reason for an
//! excluded instance. [`judge`] is the pure function that produces it from a
//! rule's [`Scope`] and an [`ApplicabilityAnchor`] (the occurrence records of
//! the referenced facts plus the session fallback values). It reads no
//! environment and runs no search, so the reasoner and the certificate checker
//! can each call it on their own inputs.
//!
//! ## The reference point is the event, not the query date
//!
//! Every `occurred_at` recorded by a premise fact is a reference time; the
//! rule's effective range must cover all of them. The session's `:asof` date
//! is used only when the instance references no event time at all, and the
//! result says so (`session.as_of` is then the date used, otherwise the
//! explicit `null`). It is never stored as a fact's occurrence.
//!
//! ## Partial coverage is never rounded
//!
//! One event time inside the range and another outside is
//! [`ApplicabilityVerdict::Undecidable`], with the reason listing both sides.
//! Only all-inside is applicable and only all-outside is inapplicable. The
//! same holds for places. A comparison that cannot be made (an undeclared
//! code hierarchy) is undecidable as well.
//!
//! ## Firing
//!
//! Only [`ApplicabilityVerdict::Applicable`] and
//! [`ApplicabilityVerdict::Unchecked`] allow an instance to fire. `unchecked`
//! means no evidence at all; excluding a rule on no evidence would be a guess.
//! `inapplicable` and `undecidable` must not fire, and the checker rejects a
//! rule application node that records either.
//!
//! ## Stable wire names
//!
//! The enum tags and field names are part of format version 7 and never hold
//! free-form conclusions: every value can be rechecked against the rule's
//! environment declaration and the fact occurrence records. A reason also
//! carries its rendered explanation, which [`ApplicabilityReason::new`]
//! derives from the structured fields, so the checker compares a
//! recomputation with the recorded reason field by field.

use serde::{Deserialize, Serialize};

use std_deduce_kernel::env::escape_control;
use std_deduce_kernel::meta::{validate_date, Scope, ScopeOrigin};

use crate::model::Explicit;

/// The outcome of judging one rule instance against its event time and place.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ApplicabilityVerdict {
    /// Every referenced event time/place was checked and is covered.
    Applicable,
    /// The rule certainly does not cover the events, with the concrete reason.
    Inapplicable,
    /// A needed input is missing; the instance may still fire.
    Unchecked,
    /// Every needed input is present but the data cannot decide.
    Undecidable,
}

impl ApplicabilityVerdict {
    /// Whether a rule instance with this verdict may fire.
    pub fn allows_firing(self) -> bool {
        matches!(
            self,
            ApplicabilityVerdict::Applicable | ApplicabilityVerdict::Unchecked
        )
    }

    /// The stable wire keyword.
    pub fn keyword(self) -> &'static str {
        match self {
            ApplicabilityVerdict::Applicable => "applicable",
            ApplicabilityVerdict::Inapplicable => "inapplicable",
            ApplicabilityVerdict::Unchecked => "unchecked",
            ApplicabilityVerdict::Undecidable => "undecidable",
        }
    }
}

/// Where a declaration's scope value came from, as the certificate records it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ScopeOriginRecord {
    /// Written on the rule declaration.
    Rule,
    /// Inherited from the containing law pack's manifest.
    PackDefault,
    /// Declared by a case-local rule.
    CaseLocal,
    /// No scope values were declared or inherited.
    Unspecified,
}

impl ScopeOriginRecord {
    /// The stable wire keyword.
    pub fn keyword(self) -> &'static str {
        match self {
            ScopeOriginRecord::Rule => "rule",
            ScopeOriginRecord::PackDefault => "pack_default",
            ScopeOriginRecord::CaseLocal => "case_local",
            ScopeOriginRecord::Unspecified => "unspecified",
        }
    }

    /// The Chinese label used in a diagnostic.
    pub fn label_zh(self) -> &'static str {
        match self {
            ScopeOriginRecord::Rule => "规则",
            ScopeOriginRecord::PackDefault => "继承",
            ScopeOriginRecord::CaseLocal => "案件",
            ScopeOriginRecord::Unspecified => "未注明",
        }
    }
}

impl From<ScopeOrigin> for ScopeOriginRecord {
    fn from(origin: ScopeOrigin) -> Self {
        match origin {
            ScopeOrigin::Rule => ScopeOriginRecord::Rule,
            ScopeOrigin::PackDefault => ScopeOriginRecord::PackDefault,
            ScopeOrigin::CaseLocal => ScopeOriginRecord::CaseLocal,
            ScopeOrigin::Unspecified => ScopeOriginRecord::Unspecified,
        }
    }
}

impl From<&ScopeOrigin> for ScopeOriginRecord {
    fn from(origin: &ScopeOrigin) -> Self {
        ScopeOriginRecord::from(*origin)
    }
}

/// The rule's declared temporal and spatial scope, with each value's origin.
///
/// Every field is written as an explicit string or `null`: an absent value is
/// a statement ("this field is not declared"), not a missing key. The checker
/// compares this record with the loaded rule declaration field by field.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ScopeEvidence {
    /// Inclusive first day in force, `YYYY-MM-DD`, or `null`.
    pub effective_from: Explicit<String>,
    /// Exclusive first day out of force, `YYYY-MM-DD`, or `null`.
    pub effective_to: Explicit<String>,
    /// The declaring legal system, or `null`.
    pub jurisdiction: Explicit<String>,
    /// The covered territory, or `null`.
    pub territory: Explicit<String>,
    /// Origin of [`ScopeEvidence::effective_from`]; `null` exactly when the
    /// value is `null`.
    pub effective_from_origin: Explicit<ScopeOriginRecord>,
    /// Origin of [`ScopeEvidence::effective_to`].
    pub effective_to_origin: Explicit<ScopeOriginRecord>,
    /// Origin of [`ScopeEvidence::jurisdiction`].
    pub jurisdiction_origin: Explicit<ScopeOriginRecord>,
    /// Origin of [`ScopeEvidence::territory`].
    pub territory_origin: Explicit<ScopeOriginRecord>,
}

impl ScopeEvidence {
    /// Copy a kernel [`Scope`] into the certificate form.
    pub fn of(scope: &Scope) -> Self {
        ScopeEvidence {
            effective_from: optional(scope.effective_from.clone()),
            effective_to: optional(scope.effective_to.clone()),
            jurisdiction: optional(scope.jurisdiction.clone()),
            territory: optional(scope.territory.clone()),
            effective_from_origin: optional(scope.effective_from_origin.map(Into::into)),
            effective_to_origin: optional(scope.effective_to_origin.map(Into::into)),
            jurisdiction_origin: optional(scope.jurisdiction_origin.map(Into::into)),
            territory_origin: optional(scope.territory_origin.map(Into::into)),
        }
    }

    /// The first field that differs from `scope`, for a diagnostic.
    pub fn difference(&self, scope: &Scope) -> Option<&'static str> {
        let expected = ScopeEvidence::of(scope);
        for (field, same) in [
            (
                "effective_from",
                self.effective_from == expected.effective_from,
            ),
            ("effective_to", self.effective_to == expected.effective_to),
            ("jurisdiction", self.jurisdiction == expected.jurisdiction),
            ("territory", self.territory == expected.territory),
            (
                "effective_from_origin",
                self.effective_from_origin == expected.effective_from_origin,
            ),
            (
                "effective_to_origin",
                self.effective_to_origin == expected.effective_to_origin,
            ),
            (
                "jurisdiction_origin",
                self.jurisdiction_origin == expected.jurisdiction_origin,
            ),
            (
                "territory_origin",
                self.territory_origin == expected.territory_origin,
            ),
        ] {
            if !same {
                return Some(field);
            }
        }
        None
    }
}

fn optional<T>(value: Option<T>) -> Explicit<T> {
    match value {
        Some(value) => Explicit::some(value),
        None => Explicit::none(),
    }
}

/// The session fallback values a judgement actually used.
///
/// `as_of` is present only when the query date stood in for an event time;
/// `null` means "the session date was not used", never "a date that happens to
/// look the same". `jurisdiction` is present only when the rule declares a
/// jurisdiction and the judgement reached that comparison; `null` means the
/// comparison did not happen.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SessionEvidence {
    /// The date used in place of an event time, or explicit `null`.
    pub as_of: Explicit<String>,
    /// The session jurisdiction code compared with the rule, or `null`.
    pub jurisdiction: Explicit<String>,
}

/// The reference dates and places a judgement looked at, with their coverage.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ApplicabilityBasis {
    /// Reference dates, in premise order; duplicates are not repeated.
    pub dates: Vec<DatedEvidence>,
    /// Event places, in premise order; duplicates are not repeated.
    pub places: Vec<PlaceEvidence>,
    /// Whether some referenced fact recorded no event time.
    pub missing_event_date: bool,
    /// Whether some referenced fact recorded no event place.
    pub missing_event_place: bool,
    /// The rule's declared scope this judgement read.
    pub scope: ScopeEvidence,
    /// The session fallback values this judgement actually used.
    pub session: SessionEvidence,
}

/// One reference date and whether the rule's range covers it.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
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
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PlaceEvidence {
    /// The `occurred_in` code.
    pub place: String,
    /// `Some(true)` covered, `Some(false)` not covered, `None` when the codes
    /// are in a containment relation whose direction is not declared.
    pub covered: Option<bool>,
}

/// Which date field holds a malformed value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
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

/// The concrete reason an instance was not judged applicable.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ApplicabilityReasonKind {
    /// The rule declares no scope field at all.
    RuleHasNoScope,
    /// The rule declares an effective range, no event time exists and the
    /// session has no `:asof`.
    NoCaseDate,
    /// Some premise facts record no `occurred_at`, while others do.
    PartialCaseDate,
    /// The rule declares a territory but no premise fact records a place.
    NoCasePlace,
    /// Some premise facts record no `occurred_in`, while others do.
    PartialCasePlace,
    /// The rule declares a jurisdiction but the session sets no
    /// `:jurisdiction`.
    NoQueryJurisdiction,
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
    /// The dates are outside the range on both sides.
    OutsideRange {
        /// The reference dates that are outside.
        dates: Vec<String>,
        /// The declared start, if any.
        effective_from: Explicit<String>,
        /// The declared end, if any.
        effective_to: Explicit<String>,
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
    /// A stored date is not a `YYYY-MM-DD` calendar day.
    InvalidDate {
        /// Which field holds the value.
        field: DateField,
        /// The malformed value.
        value: String,
    },
    /// The range's start is not earlier than its end.
    InvertedInterval {
        /// The declared start.
        from: String,
        /// The declared end.
        to: String,
    },
    /// Some reference dates are inside the range and some are outside.
    PartialDateCoverage {
        /// Dates inside the range.
        covered: Vec<String>,
        /// Dates outside the range.
        outside: Vec<String>,
        /// The declared start, if any.
        effective_from: Explicit<String>,
        /// The declared end, if any.
        effective_to: Explicit<String>,
    },
    /// The two codes are in a containment relation whose direction is not
    /// declared.
    IncomparableCode {
        /// Whether the codes are jurisdictions or territories.
        dimension: CodeDimension,
        /// The rule's code.
        rule: String,
        /// The event's or case's code.
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

impl ApplicabilityReasonKind {
    /// The stable reason code.
    pub fn code(&self) -> &'static str {
        match self {
            ApplicabilityReasonKind::RuleHasNoScope => "rule_has_no_scope",
            ApplicabilityReasonKind::NoCaseDate => "no_case_date",
            ApplicabilityReasonKind::PartialCaseDate => "partial_case_date",
            ApplicabilityReasonKind::NoCasePlace => "no_case_place",
            ApplicabilityReasonKind::PartialCasePlace => "partial_case_place",
            ApplicabilityReasonKind::NoQueryJurisdiction => "no_query_jurisdiction",
            ApplicabilityReasonKind::NotYetInForce { .. } => "not_yet_in_force",
            ApplicabilityReasonKind::Repealed { .. } => "repealed",
            ApplicabilityReasonKind::OutsideRange { .. } => "outside_range",
            ApplicabilityReasonKind::JurisdictionMismatch { .. } => "jurisdiction_mismatch",
            ApplicabilityReasonKind::TerritoryMismatch { .. } => "territory_mismatch",
            ApplicabilityReasonKind::InvalidDate { .. } => "invalid_date",
            ApplicabilityReasonKind::InvertedInterval { .. } => "inverted_interval",
            ApplicabilityReasonKind::PartialDateCoverage { .. } => "partial_date_coverage",
            ApplicabilityReasonKind::IncomparableCode { .. } => "incomparable_code",
            ApplicabilityReasonKind::PartialPlaceCoverage { .. } => "partial_place_coverage",
        }
    }

    /// The readable Chinese explanation, derived only from the structured
    /// fields.
    pub fn describe_zh(&self) -> String {
        match self {
            ApplicabilityReasonKind::RuleHasNoScope => "规则没有声明任何范围".to_owned(),
            ApplicabilityReasonKind::NoCaseDate => "规则声明了生效区间，但实例引用的前提事实\
                 没有发生时间，会话也未设置 :asof"
                .to_owned(),
            ApplicabilityReasonKind::PartialCaseDate => {
                "部分前提事实没有发生时间，已知事件时间不能代表它们".to_owned()
            }
            ApplicabilityReasonKind::NoCasePlace => {
                "规则声明了地域，但实例引用的前提事实都没有记录发生地点".to_owned()
            }
            ApplicabilityReasonKind::PartialCasePlace => {
                "部分前提事实没有记录发生地点，已知地点不能代表它们".to_owned()
            }
            ApplicabilityReasonKind::NoQueryJurisdiction => {
                "规则声明了管辖，但会话未设置 :jurisdiction".to_owned()
            }
            ApplicabilityReasonKind::NotYetInForce {
                dates,
                effective_from,
            } => format!(
                "事件时间 {} 早于规则生效日 {}，规则当时尚未生效",
                escape_dates(dates),
                escape_control(effective_from)
            ),
            ApplicabilityReasonKind::Repealed { dates, repealed } => format!(
                "事件时间 {} 已达到规则废止日 {}，规则已经失效",
                escape_dates(dates),
                escape_control(repealed)
            ),
            ApplicabilityReasonKind::OutsideRange {
                dates,
                effective_from,
                effective_to,
            } => format!(
                "事件时间 {} 全部落在规则生效区间 {} 之外",
                escape_dates(dates),
                range_text(effective_from.as_ref(), effective_to.as_ref())
            ),
            ApplicabilityReasonKind::JurisdictionMismatch { rule, case } => format!(
                "规则管辖 {} 与案件管辖 {} 不同",
                escape_control(rule),
                escape_control(case)
            ),
            ApplicabilityReasonKind::TerritoryMismatch { rule, places } => format!(
                "规则地域 {} 不覆盖事件地点 {}",
                escape_control(rule),
                escape_dates(places)
            ),
            ApplicabilityReasonKind::InvalidDate { field, value } => format!(
                "{}「{}」不是 YYYY-MM-DD 日期，无法比较",
                field.label_zh(),
                escape_control(value)
            ),
            ApplicabilityReasonKind::InvertedInterval { from, to } => format!(
                "生效起点 {} 不早于废止日 {}，区间为空或倒置",
                escape_control(from),
                escape_control(to)
            ),
            ApplicabilityReasonKind::PartialDateCoverage {
                covered,
                outside,
                effective_from,
                effective_to,
            } => format!(
                "事件时间 {} 在生效区间 {} 内，{} 不在其中；部分覆盖不能当作适用",
                escape_dates(covered),
                range_text(effective_from.as_ref(), effective_to.as_ref()),
                escape_dates(outside)
            ),
            ApplicabilityReasonKind::IncomparableCode {
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
            ApplicabilityReasonKind::PartialPlaceCoverage {
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

/// One excluded-instance reason with its code and rendered explanation.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ApplicabilityReason {
    /// The structured reason; its tag is the stable reason code.
    pub detail: ApplicabilityReasonKind,
    /// The readable Chinese explanation of `detail`.
    pub text: String,
}

impl ApplicabilityReason {
    /// Wrap a structured reason and render its explanation.
    pub fn new(detail: ApplicabilityReasonKind) -> Self {
        let text = detail.describe_zh();
        ApplicabilityReason { detail, text }
    }

    /// The stable reason code.
    pub fn code(&self) -> &'static str {
        self.detail.code()
    }
}

/// The complete applicability record of one rule instance.
///
/// `reason` is present exactly when the verdict is not `applicable`. An
/// `applicable` record carries the explicit `null`, so a writer cannot omit
/// the field and a checker cannot read a missing field as "no reason needed".
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RuleApplicability {
    /// The verdict.
    pub verdict: ApplicabilityVerdict,
    /// The evidence and declared inputs the verdict rests on.
    pub basis: ApplicabilityBasis,
    /// The reason for a non-applicable verdict, or explicit `null`.
    pub reason: Explicit<ApplicabilityReason>,
}

impl RuleApplicability {
    /// The reason, when the verdict is not applicable.
    pub fn reason(&self) -> Option<&ApplicabilityReason> {
        self.reason.as_ref()
    }
}

/// The reference inputs a judgement is computed from.
///
/// The reasoner builds this from the premise facts it consumed and the
/// session values; the checker rebuilds it from the certificate's own nodes
/// (rule applications) or from the recorded basis (gap candidates) and the
/// environment identity's session values.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct ApplicabilityAnchor {
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

/// Judge one rule instance's recorded scope against its event time and place.
pub fn judge(scope: &Scope, anchor: &ApplicabilityAnchor) -> RuleApplicability {
    if scope.is_unscoped() {
        return RuleApplicability {
            verdict: ApplicabilityVerdict::Unchecked,
            basis: ApplicabilityBasis::default(),
            reason: Explicit::some(ApplicabilityReason::new(
                ApplicabilityReasonKind::RuleHasNoScope,
            )),
        };
    }

    let mut basis = ApplicabilityBasis {
        dates: Vec::new(),
        places: Vec::new(),
        missing_event_date: anchor.missing_event_date,
        missing_event_place: anchor.missing_event_place,
        scope: ScopeEvidence::of(scope),
        session: SessionEvidence::default(),
    };
    let mut missing: Option<ApplicabilityReasonKind> = None;
    let mut undecidable: Option<ApplicabilityReasonKind> = None;

    if scope.effective_from.is_some() || scope.effective_to.is_some() {
        match judge_dates(scope, anchor, &mut basis) {
            DateVerdict::Inside => {}
            DateVerdict::Inapplicable(reason) => {
                return RuleApplicability {
                    verdict: ApplicabilityVerdict::Inapplicable,
                    basis,
                    reason: Explicit::some(ApplicabilityReason::new(reason)),
                };
            }
            DateVerdict::Unchecked(reason) => missing = Some(reason),
            DateVerdict::Undecidable(reason) => undecidable = Some(reason),
        }
    }

    if let Some(rule_code) = scope.jurisdiction.as_deref() {
        match anchor.jurisdiction.as_deref() {
            None => missing = missing.or(Some(ApplicabilityReasonKind::NoQueryJurisdiction)),
            Some(case_code) => {
                basis.session.jurisdiction = Explicit::some(case_code.to_owned());
                match compare_codes(rule_code, case_code) {
                    CodeRelation::Equal => {}
                    CodeRelation::Disjoint => {
                        return RuleApplicability {
                            verdict: ApplicabilityVerdict::Inapplicable,
                            basis,
                            reason: Explicit::some(ApplicabilityReason::new(
                                ApplicabilityReasonKind::JurisdictionMismatch {
                                    rule: rule_code.to_owned(),
                                    case: case_code.to_owned(),
                                },
                            )),
                        };
                    }
                    CodeRelation::Nested => {
                        undecidable =
                            undecidable.or(Some(ApplicabilityReasonKind::IncomparableCode {
                                dimension: CodeDimension::Jurisdiction,
                                rule: rule_code.to_owned(),
                                case: case_code.to_owned(),
                            }));
                    }
                }
            }
        }
    }

    if let Some(rule_code) = scope.territory.as_deref() {
        match judge_places(rule_code, anchor, &mut basis) {
            PlaceVerdict::Inside => {}
            PlaceVerdict::Inapplicable(reason) => {
                return RuleApplicability {
                    verdict: ApplicabilityVerdict::Inapplicable,
                    basis,
                    reason: Explicit::some(ApplicabilityReason::new(reason)),
                };
            }
            PlaceVerdict::Unchecked(reason) => missing = missing.or(Some(reason)),
            PlaceVerdict::Undecidable(reason) => undecidable = undecidable.or(Some(reason)),
        }
    }

    let (verdict, reason) = if let Some(reason) = missing {
        (ApplicabilityVerdict::Unchecked, Some(reason))
    } else if let Some(reason) = undecidable {
        (ApplicabilityVerdict::Undecidable, Some(reason))
    } else {
        (ApplicabilityVerdict::Applicable, None)
    };
    RuleApplicability {
        verdict,
        basis,
        reason: match reason {
            Some(reason) => Explicit::some(ApplicabilityReason::new(reason)),
            None => Explicit::none(),
        },
    }
}

/// The temporal verdict before the spatial dimensions are folded in.
enum DateVerdict {
    /// Every reference date lies inside the rule's range.
    Inside,
    /// Every reference date is outside the range.
    Inapplicable(ApplicabilityReasonKind),
    /// There is no reference date, or one referenced fact has none.
    Unchecked(ApplicabilityReasonKind),
    /// The stored dates cannot be compared, or coverage is partial.
    Undecidable(ApplicabilityReasonKind),
}

/// Check every reference date against the rule's effective range.
fn judge_dates(
    scope: &Scope,
    anchor: &ApplicabilityAnchor,
    basis: &mut ApplicabilityBasis,
) -> DateVerdict {
    let from = scope.effective_from.as_deref();
    let to = scope.effective_to.as_deref();

    for (field, value) in [
        (DateField::EffectiveFrom, from),
        (DateField::EffectiveTo, to),
    ] {
        if let Some(value) = value {
            if validate_date(field.label_zh(), value).is_err() {
                return DateVerdict::Undecidable(ApplicabilityReasonKind::InvalidDate {
                    field,
                    value: value.to_owned(),
                });
            }
        }
    }
    if let (Some(from), Some(to)) = (from, to) {
        if from >= to {
            return DateVerdict::Undecidable(ApplicabilityReasonKind::InvertedInterval {
                from: from.to_owned(),
                to: to.to_owned(),
            });
        }
    }

    let partial = !anchor.event_dates.is_empty() && anchor.missing_event_date;
    let mut references: Vec<(String, bool)> = Vec::new();
    if anchor.event_dates.is_empty() {
        let Some(as_of) = anchor.as_of.as_deref() else {
            return DateVerdict::Unchecked(ApplicabilityReasonKind::NoCaseDate);
        };
        basis.session.as_of = Explicit::some(as_of.to_owned());
        references.push((as_of.to_owned(), true));
    } else {
        for date in &anchor.event_dates {
            if !references.iter().any(|(known, _)| known == date) {
                references.push((date.clone(), false));
            }
        }
    }

    let mut covered = Vec::new();
    let mut outside = Vec::new();
    for (day, query_date_fallback) in &references {
        let field = if *query_date_fallback {
            DateField::AsOf
        } else {
            DateField::OccurredAt
        };
        if validate_date(field.label_zh(), day).is_err() {
            return DateVerdict::Undecidable(ApplicabilityReasonKind::InvalidDate {
                field,
                value: day.clone(),
            });
        }
        let in_range =
            from.is_none_or(|from| day.as_str() >= from) && to.is_none_or(|to| day.as_str() < to);
        basis.dates.push(DatedEvidence {
            date: day.clone(),
            query_date_fallback: *query_date_fallback,
            covered: in_range,
        });
        if in_range {
            covered.push(day.clone());
        } else {
            outside.push(day.clone());
        }
    }

    if partial {
        return DateVerdict::Unchecked(ApplicabilityReasonKind::PartialCaseDate);
    }
    if outside.is_empty() {
        return DateVerdict::Inside;
    }
    if covered.is_empty() {
        return DateVerdict::Inapplicable(outside_reason(from, to, outside));
    }
    DateVerdict::Undecidable(ApplicabilityReasonKind::PartialDateCoverage {
        covered,
        outside,
        effective_from: option_explicit(from),
        effective_to: option_explicit(to),
    })
}

fn option_explicit(value: Option<&str>) -> Explicit<String> {
    match value {
        Some(value) => Explicit::some(value.to_owned()),
        None => Explicit::none(),
    }
}

/// The concrete reason when every reference date is outside the range.
fn outside_reason(
    from: Option<&str>,
    to: Option<&str>,
    dates: Vec<String>,
) -> ApplicabilityReasonKind {
    let before_start = from.is_some_and(|from| dates.iter().all(|date| date.as_str() < from));
    let after_end = to.is_some_and(|to| dates.iter().all(|date| date.as_str() >= to));
    if before_start && !after_end {
        ApplicabilityReasonKind::NotYetInForce {
            dates,
            effective_from: from.unwrap_or_default().to_owned(),
        }
    } else if after_end && !before_start {
        ApplicabilityReasonKind::Repealed {
            dates,
            repealed: to.unwrap_or_default().to_owned(),
        }
    } else {
        ApplicabilityReasonKind::OutsideRange {
            dates,
            effective_from: option_explicit(from),
            effective_to: option_explicit(to),
        }
    }
}

/// The territorial verdict before it is folded into the overall judgement.
enum PlaceVerdict {
    /// Every event place is covered.
    Inside,
    /// Every event place is outside the rule's territory.
    Inapplicable(ApplicabilityReasonKind),
    /// No place is recorded, or some referenced fact has none.
    Unchecked(ApplicabilityReasonKind),
    /// Some places are covered and some are not, or a comparison cannot
    /// decide.
    Undecidable(ApplicabilityReasonKind),
}

/// Check every event place against the rule's territory.
fn judge_places(
    rule: &str,
    anchor: &ApplicabilityAnchor,
    basis: &mut ApplicabilityBasis,
) -> PlaceVerdict {
    let partial = !anchor.event_places.is_empty() && anchor.missing_event_place;
    let mut references: Vec<&str> = Vec::new();
    for place in &anchor.event_places {
        let place = place.as_str();
        if !references.contains(&place) {
            references.push(place);
        }
    }
    if references.is_empty() {
        return PlaceVerdict::Unchecked(ApplicabilityReasonKind::NoCasePlace);
    }

    let mut covered = Vec::new();
    let mut uncovered = Vec::new();
    let mut nested = None;
    for place in references {
        let relation = compare_codes(rule, place);
        let covered_flag = match relation {
            CodeRelation::Equal => Some(true),
            CodeRelation::Disjoint => Some(false),
            CodeRelation::Nested => None,
        };
        basis.places.push(PlaceEvidence {
            place: place.to_owned(),
            covered: covered_flag,
        });
        match covered_flag {
            Some(true) => covered.push(place.to_owned()),
            Some(false) => uncovered.push(place.to_owned()),
            None => nested = nested.or(Some(place)),
        }
    }

    if partial {
        return PlaceVerdict::Unchecked(ApplicabilityReasonKind::PartialCasePlace);
    }
    if let Some(place) = nested {
        return PlaceVerdict::Undecidable(ApplicabilityReasonKind::IncomparableCode {
            dimension: CodeDimension::Territory,
            rule: rule.to_owned(),
            case: place.to_owned(),
        });
    }
    if uncovered.is_empty() {
        return PlaceVerdict::Inside;
    }
    if covered.is_empty() {
        return PlaceVerdict::Inapplicable(ApplicabilityReasonKind::TerritoryMismatch {
            rule: rule.to_owned(),
            places: uncovered,
        });
    }
    PlaceVerdict::Undecidable(ApplicabilityReasonKind::PartialPlaceCoverage {
        covered,
        uncovered,
        rule: rule.to_owned(),
    })
}

/// How two opaque codes relate.
enum CodeRelation {
    /// The same code.
    Equal,
    /// One is a `-`-separated prefix of the other.
    Nested,
    /// Neither contains the other.
    Disjoint,
}

fn compare_codes(rule: &str, case: &str) -> CodeRelation {
    if rule == case {
        CodeRelation::Equal
    } else if is_nested(rule, case) || is_nested(case, rule) {
        CodeRelation::Nested
    } else {
        CodeRelation::Disjoint
    }
}

/// Is `prefix` a `-`-separated leading segment of `whole`?
fn is_nested(prefix: &str, whole: &str) -> bool {
    whole.len() > prefix.len()
        && whole.starts_with(prefix)
        && whole.as_bytes()[prefix.len()] == b'-'
}

fn escape_dates(dates: &[String]) -> String {
    dates
        .iter()
        .map(|date| escape_control(date))
        .collect::<Vec<_>>()
        .join("、")
}

fn range_text(from: Option<&String>, to: Option<&String>) -> String {
    match (from, to) {
        (Some(from), Some(to)) => {
            format!("{}..{}", escape_control(from), escape_control(to))
        }
        (Some(from), None) => format!("{}..", escape_control(from)),
        (None, Some(to)) => format!("..{}", escape_control(to)),
        (None, None) => "（无端点）".to_owned(),
    }
}
