//! A pure temporal and spatial applicability judgement.
//!
//! The judgement is data in, data out: a rule's recorded [`Scope`], the
//! occurrence records of the premise facts a rule instance references, and
//! the session's legal as-of date and jurisdiction. It does not read the
//! environment, the derivation or the CLI, so it can be tested on its own and
//! the same judgement is used by the reasoner, `:gap`, `:why` and
//! `:applicability`.
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
//! it looked at, so the display can be checked against the facts.
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
use std_deduce_kernel::meta::{validate_date, Scope};

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
/// gets a guessed value.
#[derive(Debug, Clone, Default)]
pub struct InstanceAnchor<'a> {
    /// The session's legal as-of date, used only when no event time exists.
    pub as_of: Option<&'a str>,
    /// The session's jurisdiction code, when set.
    pub jurisdiction: Option<&'a str>,
    /// `occurred_at` values of the referenced premise facts.
    pub event_dates: Vec<&'a str>,
    /// Whether some referenced premise fact records no `occurred_at`.
    pub missing_event_date: bool,
    /// `occurred_in` values of the referenced premise facts.
    pub event_places: Vec<&'a str>,
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
            } => format!(
                "规则{} {} 与事件{} {} 是上下位关系但未声明层级，无法比较",
                dimension.label_zh(),
                escape_control(rule),
                dimension.label_zh(),
                escape_control(case)
            ),
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
pub fn judge(scope: &Scope, case: &InstanceAnchor<'_>) -> Applicability {
    if scope.is_unscoped() {
        return Applicability::Unchecked {
            missing: MissingInput::RuleHasNoScope,
            basis: Basis::default(),
        };
    }

    let mut basis = Basis::default();
    let mut missing: Option<MissingInput> = None;
    let mut undecidable: Option<UndecidableReason> = None;

    if scope.effective_from.is_some() || scope.effective_to.is_some() {
        match judge_dates(scope, case, &mut basis) {
            DateVerdict::Inside => {}
            DateVerdict::Inapplicable(reason) => {
                return Applicability::Inapplicable { reason, basis };
            }
            DateVerdict::Unchecked(missing_input) => missing = Some(missing_input),
            DateVerdict::Undecidable(reason) => undecidable = Some(reason),
        }
    }

    if let Some(rule_code) = scope.jurisdiction.as_deref() {
        match case.jurisdiction {
            None => missing = missing.or(Some(MissingInput::NoQueryJurisdiction)),
            Some(case_code) => match compare_codes(rule_code, case_code) {
                CodeRelation::Equal => {}
                CodeRelation::Disjoint => {
                    return Applicability::Inapplicable {
                        reason: InapplicableReason::JurisdictionMismatch {
                            rule: rule_code.to_owned(),
                            case: case_code.to_owned(),
                        },
                        basis,
                    };
                }
                CodeRelation::Nested => {
                    undecidable = undecidable.or(Some(UndecidableReason::IncomparableCode {
                        dimension: CodeDimension::Jurisdiction,
                        rule: rule_code.to_owned(),
                        case: case_code.to_owned(),
                    }));
                }
            },
        }
    }

    if let Some(rule_code) = scope.territory.as_deref() {
        match judge_places(rule_code, case, &mut basis) {
            PlaceVerdict::Inside => {}
            PlaceVerdict::Inapplicable(reason) => {
                return Applicability::Inapplicable { reason, basis };
            }
            PlaceVerdict::Unchecked(missing_input) => missing = missing.or(Some(missing_input)),
            PlaceVerdict::Undecidable(reason) => undecidable = undecidable.or(Some(reason)),
        }
    }

    if let Some(missing) = missing {
        Applicability::Unchecked { missing, basis }
    } else if let Some(reason) = undecidable {
        Applicability::Undecidable { reason, basis }
    } else {
        Applicability::Applicable { basis }
    }
}

/// The temporal verdict before the spatial dimensions are folded in.
enum DateVerdict {
    /// Every reference date lies inside the rule's range.
    Inside,
    /// Every reference date is outside the range.
    Inapplicable(InapplicableReason),
    /// There is no reference date, or one referenced fact has none.
    Unchecked(MissingInput),
    /// The stored dates cannot be compared, or coverage is partial.
    Undecidable(UndecidableReason),
}

/// Check every reference date against the rule's effective range.
///
/// The reference dates are the `occurred_at` values of the premise facts the
/// instance references. The session's as-of date is used only when no such
/// event time exists; the basis records that substitution. Both endpoints may
/// be absent; the range is then open on that side.
fn judge_dates(scope: &Scope, case: &InstanceAnchor<'_>, basis: &mut Basis) -> DateVerdict {
    let from = scope.effective_from.as_deref();
    let to = scope.effective_to.as_deref();

    for (field, value) in [
        (DateField::EffectiveFrom, from),
        (DateField::EffectiveTo, to),
    ] {
        if let Some(value) = value {
            if validate_date(field.label_zh(), value).is_err() {
                return DateVerdict::Undecidable(UndecidableReason::InvalidDate {
                    field,
                    value: value.to_owned(),
                });
            }
        }
    }
    if let (Some(from), Some(to)) = (from, to) {
        if from >= to {
            return DateVerdict::Undecidable(UndecidableReason::InvertedInterval {
                from: from.to_owned(),
                to: to.to_owned(),
            });
        }
    }

    // Collect the reference dates. A fact without `occurred_at` is never
    // replaced by another fact's date; the query date only stands in when the
    // instance has no event time at all.
    let partial = !case.event_dates.is_empty() && case.missing_event_date;
    let mut references: Vec<(String, bool)> = Vec::new();
    if case.event_dates.is_empty() {
        let Some(as_of) = case.as_of else {
            return DateVerdict::Unchecked(MissingInput::NoCaseDate);
        };
        references.push((as_of.to_owned(), true));
    } else {
        for date in &case.event_dates {
            if !references.iter().any(|(known, _)| known == date) {
                references.push(((*date).to_owned(), false));
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
            return DateVerdict::Undecidable(UndecidableReason::InvalidDate {
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
        // A referenced fact has no occurrence date: the known dates cannot
        // stand in for it, whatever their own coverage is.
        return DateVerdict::Unchecked(MissingInput::PartialCaseDate);
    }
    if outside.is_empty() {
        return DateVerdict::Inside;
    }
    if covered.is_empty() {
        return DateVerdict::Inapplicable(outside_reason(from, to, outside));
    }
    DateVerdict::Undecidable(UndecidableReason::PartialDateCoverage {
        covered,
        outside,
        effective_from: from.map(ToOwned::to_owned),
        effective_to: to.map(ToOwned::to_owned),
    })
}

/// The concrete reason when every reference date is outside the range.
fn outside_reason(from: Option<&str>, to: Option<&str>, dates: Vec<String>) -> InapplicableReason {
    let before_start = from.is_some_and(|from| dates.iter().all(|date| date.as_str() < from));
    let after_end = to.is_some_and(|to| dates.iter().all(|date| date.as_str() >= to));
    if before_start && !after_end {
        InapplicableReason::NotYetInForce {
            dates,
            effective_from: from.unwrap_or_default().to_owned(),
        }
    } else if after_end && !before_start {
        InapplicableReason::Repealed {
            dates,
            repealed: to.unwrap_or_default().to_owned(),
        }
    } else {
        InapplicableReason::OutsideRange {
            dates,
            effective_from: from.map(ToOwned::to_owned),
            effective_to: to.map(ToOwned::to_owned),
        }
    }
}

/// The territorial verdict before it is folded into the overall judgement.
enum PlaceVerdict {
    /// Every event place is covered.
    Inside,
    /// Every event place is outside the rule's territory.
    Inapplicable(InapplicableReason),
    /// No place is recorded, or some referenced fact has none.
    Unchecked(MissingInput),
    /// Some places are covered and some are not, or a comparison cannot
    /// decide.
    Undecidable(UndecidableReason),
}

/// Check every event place against the rule's territory.
///
/// A fact without `occurred_in` is missing input; the rule's own territory is
/// never used to infer where the event happened. Partial coverage is
/// undecidable, never rounded to either side.
fn judge_places(rule: &str, case: &InstanceAnchor<'_>, basis: &mut Basis) -> PlaceVerdict {
    let partial = !case.event_places.is_empty() && case.missing_event_place;
    let mut references: Vec<&str> = Vec::new();
    for place in &case.event_places {
        if !references.contains(place) {
            references.push(*place);
        }
    }
    if references.is_empty() {
        return PlaceVerdict::Unchecked(MissingInput::NoCasePlace);
    }

    let mut covered = Vec::new();
    let mut uncovered = Vec::new();
    let mut nested = None;
    for place in &references {
        let relation = compare_codes(rule, place);
        let covered_flag = match relation {
            CodeRelation::Equal => Some(true),
            CodeRelation::Disjoint => Some(false),
            CodeRelation::Nested => None,
        };
        basis.places.push(PlaceEvidence {
            place: (*place).to_owned(),
            covered: covered_flag,
        });
        match covered_flag {
            Some(true) => covered.push((*place).to_owned()),
            Some(false) => uncovered.push((*place).to_owned()),
            None => nested = nested.or(Some(*place)),
        }
    }

    if partial {
        // A referenced fact has no place: the known places cannot represent it.
        return PlaceVerdict::Unchecked(MissingInput::PartialCasePlace);
    }
    if let Some(place) = nested {
        return PlaceVerdict::Undecidable(UndecidableReason::IncomparableCode {
            dimension: CodeDimension::Territory,
            rule: rule.to_owned(),
            case: place.to_owned(),
        });
    }
    if uncovered.is_empty() {
        return PlaceVerdict::Inside;
    }
    if covered.is_empty() {
        return PlaceVerdict::Inapplicable(InapplicableReason::TerritoryMismatch {
            rule: rule.to_owned(),
            places: uncovered,
        });
    }
    PlaceVerdict::Undecidable(UndecidableReason::PartialPlaceCoverage {
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

    fn anchor<'a>(
        as_of: Option<&'a str>,
        jurisdiction: Option<&'a str>,
        dates: &[&'a str],
        places: &[&'a str],
    ) -> InstanceAnchor<'a> {
        InstanceAnchor {
            as_of,
            jurisdiction,
            event_dates: dates.to_vec(),
            missing_event_date: false,
            event_places: places.to_vec(),
            missing_event_place: false,
        }
    }

    fn dated<'a>(as_of: Option<&'a str>, dates: &'a [&'a str]) -> InstanceAnchor<'a> {
        anchor(as_of, None, dates, &[])
    }

    fn applicable_dates<'a>(dates: &'a [&'a str]) -> InstanceAnchor<'a> {
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
