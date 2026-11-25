//! A pure temporal and spatial applicability judgement.
//!
//! The judgement is data in, data out: a rule's recorded [`Scope`], the
//! session's legal as-of date and jurisdiction, and the occurrence records of
//! the case's registered facts. It does not read the environment, the
//! derivation or the CLI, so it can be tested on its own and the same
//! judgement is used by the reasoner, `:gap` and `:why`.
//!
//! ## Two failures that must not be confused
//!
//! * [`Applicability::Inapplicable`] means every input needed for a declared
//!   restriction was present and the rule does not apply: the rule was not in
//!   force on the case date, or its jurisdiction/territory does not cover the
//!   case.
//! * [`Applicability::Unchecked`] means an input is missing: the rule states a
//!   restriction but the session has no as-of date, the case records no
//!   occurrence, or the session has no jurisdiction. Missing evidence never
//!   turns into a negative judgement.
//! * [`Applicability::Undecidable`] means the inputs are there but the data
//!   cannot decide: a date is not a calendar day, an interval is empty, or two
//!   codes are in a containment relation whose direction is not declared.
//!
//! A missing input outranks an undecidable one, and a clear non-application
//! outranks both: the reader should first learn that the rule certainly does
//! not apply. Only [`Applicability::Applicable`] is a positive decision.
//!
//! ## What the judgement compares
//!
//! * The effective range must contain every reference date: the session's
//!   `as_of` when one is set, and every occurrence date the case records. A
//!   rule that entered into force after the facts, or that was repealed before
//!   the facts or before the query date, does not govern the case.
//! * `jurisdiction` is compared with the session's `:jurisdiction`: they are
//!   the same kind of code (the legal system that enacts the rule).
//! * `territory` is compared with the case facts' `occurred_in`: a rule for
//!   one place does not govern facts recorded in another. A missing location
//!   is missing input, not a mismatch.
//! * A dimension the rule does not declare is not a restriction and is not
//!   checked. A rule that declares no scope at all is `Unchecked`, not
//!   silently treated as unrestricted, because there is no data at all to
//!   judge against.
//!
//! Codes are opaque strings: equal codes match, disjoint codes do not match,
//! and one being a `-`-separated prefix of the other is a containment the
//! system cannot decide without a declared hierarchy.
//!
//! An open interval endpoint (only `effective` or only `repealed`) is
//! decidable with the reference dates; a missing reference date is what makes
//! it unchecked.

use std_deduce_kernel::env::escape_control;
use std_deduce_kernel::meta::{validate_date, Scope};

/// The outcome of judging one rule against the case's time and place.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Applicability {
    /// Every declared restriction was checked and the rule applies.
    Applicable,
    /// The rule certainly does not apply, with the concrete reason.
    Inapplicable {
        /// Which restriction excluded the rule and on which date or code.
        reason: InapplicableReason,
    },
    /// A declared restriction cannot be checked because an input is missing.
    /// The rule may still fire, but the caller must report the state; it is
    /// never treated as `Applicable` or as `Inapplicable`.
    Unchecked {
        /// The missing input.
        missing: MissingInput,
    },
    /// Every needed input is present but the data itself cannot decide.
    Undecidable {
        /// Why the comparison cannot conclude.
        reason: UndecidableReason,
    },
}

/// The concrete restriction that excluded a rule.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InapplicableReason {
    /// A reference date is earlier than the rule's first day in force.
    NotYetInForce {
        /// The reference date that is too early.
        day: String,
        /// The rule's first day in force (inclusive).
        effective_from: String,
    },
    /// A reference date reached the rule's first day out of force.
    Repealed {
        /// The reference date that is too late.
        day: String,
        /// The first day the rule is no longer in force (exclusive).
        repealed: String,
    },
    /// The rule's legal system differs from the case's jurisdiction.
    JurisdictionMismatch {
        /// The rule's `jurisdiction` code.
        rule: String,
        /// The session's `:jurisdiction` code.
        case: String,
    },
    /// The rule's territory differs from a place the case facts occurred in.
    TerritoryMismatch {
        /// The rule's `territory` code.
        rule: String,
        /// One `occurred_in` code of the case.
        case: String,
    },
}

/// An input the judgement needs but the session or the case did not provide.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MissingInput {
    /// The rule declares no scope field at all, so there is nothing to judge.
    RuleHasNoScope,
    /// The rule declares an effective range but no reference date is known
    /// (no `:asof`, and no fact records `occurred_at`).
    NoCaseDate,
    /// The rule declares a territory but no case fact records `occurred_in`.
    NoCasePlace,
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
    /// The two codes are in a containment relation (one is a `-`-separated
    /// prefix of the other), so whether the rule covers the case depends on a
    /// hierarchy nobody declared.
    IncomparableCode {
        /// Whether the codes are jurisdictions or territories.
        dimension: CodeDimension,
        /// The rule's code.
        rule: String,
        /// The case's code.
        case: String,
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

/// The case's time and place, as far as the judgement may read it.
///
/// `as_of` and `jurisdiction` are the session values; `occurred_at` and
/// `occurred_in` are the distinct occurrence records of the registered case
/// facts. A rule's conclusion does not inherit an occurrence record from its
/// premises: only registered facts carry one.
#[derive(Debug, Clone, Default)]
pub struct CaseAnchor<'a> {
    /// The session's legal as-of date, when set.
    pub as_of: Option<&'a str>,
    /// The session's jurisdiction code, when set.
    pub jurisdiction: Option<&'a str>,
    /// Distinct `occurred_at` dates of the registered case facts.
    pub occurred_at: Vec<&'a str>,
    /// Distinct `occurred_in` places of the registered case facts.
    pub occurred_in: Vec<&'a str>,
}

impl Applicability {
    /// Whether the rule may fire under this judgement.
    ///
    /// Only a confident non-application blocks a rule. An unchecked or
    /// undecidable judgement keeps the old derivation behaviour and must be
    /// reported by the caller; it is not silently downgraded to either
    /// extreme.
    pub fn allows_firing(&self) -> bool {
        !matches!(self, Applicability::Inapplicable { .. })
    }

    /// Whether this is the positive decision.
    pub fn is_applicable(&self) -> bool {
        matches!(self, Applicability::Applicable)
    }

    /// The short Chinese label: `适用` / `不适用` / `未判定` / `无法判定`.
    pub fn label_zh(&self) -> &'static str {
        match self {
            Applicability::Applicable => "适用",
            Applicability::Inapplicable { .. } => "不适用",
            Applicability::Unchecked { .. } => "未判定",
            Applicability::Undecidable { .. } => "无法判定",
        }
    }

    /// The one-line Chinese summary used by `:applicability`, `:why`,
    /// `:explain` and `:gap`, with the concrete reason.
    pub fn summary_zh(&self) -> String {
        match self {
            Applicability::Applicable => "适用".to_owned(),
            Applicability::Inapplicable { reason } => {
                format!("不适用（{}）", reason.text_zh())
            }
            Applicability::Unchecked { missing } => {
                format!("适用性未判定（{}）", missing.text_zh())
            }
            Applicability::Undecidable { reason } => {
                format!("适用性无法判定（{}）", reason.text_zh())
            }
        }
    }
}

impl MissingInput {
    /// Why the judgement is unchecked, in one Chinese sentence.
    pub fn text_zh(self) -> &'static str {
        match self {
            MissingInput::RuleHasNoScope => "规则没有声明任何范围",
            MissingInput::NoCaseDate => {
                "规则声明了生效区间，但未设置 :asof，案件事实也没有记录发生时间"
            }
            MissingInput::NoCasePlace => "规则声明了地域，但案件事实没有记录发生地点",
            MissingInput::NoQueryJurisdiction => "规则声明了管辖，但会话未设置 :jurisdiction",
        }
    }
}

impl InapplicableReason {
    /// The concrete reason in one Chinese sentence.
    pub fn text_zh(&self) -> String {
        match self {
            InapplicableReason::NotYetInForce {
                day,
                effective_from,
            } => format!(
                "案件日期 {} 早于规则生效日 {}，规则当时尚未生效",
                escape_control(day),
                escape_control(effective_from)
            ),
            InapplicableReason::Repealed { day, repealed } => format!(
                "案件日期 {} 已达到规则废止日 {}，规则已经失效",
                escape_control(day),
                escape_control(repealed)
            ),
            InapplicableReason::JurisdictionMismatch { rule, case } => format!(
                "规则管辖 {} 与案件管辖 {} 不同",
                escape_control(rule),
                escape_control(case)
            ),
            InapplicableReason::TerritoryMismatch { rule, case } => format!(
                "规则地域 {} 与案件发生地 {} 不同",
                escape_control(rule),
                escape_control(case)
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
            UndecidableReason::IncomparableCode {
                dimension,
                rule,
                case,
            } => format!(
                "规则{} {} 与案件{} {} 是上下位关系但未声明层级，无法比较",
                dimension.label_zh(),
                escape_control(rule),
                dimension.label_zh(),
                escape_control(case)
            ),
        }
    }
}

/// Judge one rule's recorded scope against the case.
pub fn judge(scope: &Scope, case: &CaseAnchor<'_>) -> Applicability {
    if scope.is_unscoped() {
        return Applicability::Unchecked {
            missing: MissingInput::RuleHasNoScope,
        };
    }

    let mut missing: Option<MissingInput> = None;
    let mut undecidable: Option<UndecidableReason> = None;

    if scope.effective_from.is_some() || scope.effective_to.is_some() {
        match judge_dates(scope, case) {
            DateVerdict::Inside => {}
            DateVerdict::Inapplicable(reason) => return Applicability::Inapplicable { reason },
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
        if case.occurred_in.is_empty() {
            missing = missing.or(Some(MissingInput::NoCasePlace));
        } else {
            let mut nested = None;
            for place in &case.occurred_in {
                match compare_codes(rule_code, place) {
                    CodeRelation::Equal => {}
                    CodeRelation::Disjoint => {
                        return Applicability::Inapplicable {
                            reason: InapplicableReason::TerritoryMismatch {
                                rule: rule_code.to_owned(),
                                case: (*place).to_owned(),
                            },
                        };
                    }
                    CodeRelation::Nested => nested = nested.or(Some(*place)),
                }
            }
            if let Some(place) = nested {
                undecidable = undecidable.or(Some(UndecidableReason::IncomparableCode {
                    dimension: CodeDimension::Territory,
                    rule: rule_code.to_owned(),
                    case: place.to_owned(),
                }));
            }
        }
    }

    if let Some(missing) = missing {
        Applicability::Unchecked { missing }
    } else if let Some(reason) = undecidable {
        Applicability::Undecidable { reason }
    } else {
        Applicability::Applicable
    }
}

/// The temporal verdict before the spatial dimensions are folded in.
enum DateVerdict {
    /// Every reference date lies inside the rule's range.
    Inside,
    /// A reference date is outside the range.
    Inapplicable(InapplicableReason),
    /// There is no reference date to compare.
    Unchecked(MissingInput),
    /// The stored dates cannot be compared.
    Undecidable(UndecidableReason),
}

/// Check every reference date against the rule's effective range.
///
/// The reference dates are the session's as-of date and every registered
/// fact's occurrence date: a rule must be in force both when the facts
/// happened and, when an as-of query is made, on the query date. Either
/// endpoint may be absent; the range is then open on that side.
fn judge_dates(scope: &Scope, case: &CaseAnchor<'_>) -> DateVerdict {
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

    let mut references: Vec<(&str, DateField)> = Vec::new();
    if let Some(as_of) = case.as_of {
        references.push((as_of, DateField::AsOf));
    }
    for date in &case.occurred_at {
        references.push((*date, DateField::OccurredAt));
    }
    if references.is_empty() {
        return DateVerdict::Unchecked(MissingInput::NoCaseDate);
    }

    for (day, field) in references {
        if validate_date(field.label_zh(), day).is_err() {
            return DateVerdict::Undecidable(UndecidableReason::InvalidDate {
                field,
                value: day.to_owned(),
            });
        }
        if let Some(from) = from {
            if day < from {
                return DateVerdict::Inapplicable(InapplicableReason::NotYetInForce {
                    day: day.to_owned(),
                    effective_from: from.to_owned(),
                });
            }
        }
        if let Some(to) = to {
            if day >= to {
                return DateVerdict::Inapplicable(InapplicableReason::Repealed {
                    day: day.to_owned(),
                    repealed: to.to_owned(),
                });
            }
        }
    }
    DateVerdict::Inside
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
        occurred_at: &[&'a str],
        occurred_in: &[&'a str],
    ) -> CaseAnchor<'a> {
        CaseAnchor {
            as_of,
            jurisdiction,
            occurred_at: occurred_at.to_vec(),
            occurred_in: occurred_in.to_vec(),
        }
    }

    fn inside<'a>(as_of: Option<&'a str>, dates: &'a [&'a str]) -> CaseAnchor<'a> {
        anchor(as_of, None, dates, &[])
    }

    #[test]
    fn a_date_inside_a_closed_range_applies_and_both_endpoints_are_half_open() {
        let s = scope(Some("2019-01-01"), Some("2021-01-01"), None, None);
        assert_eq!(
            judge(&s, &inside(Some("2020-06-01"), &[])),
            Applicability::Applicable
        );
        // The start is inclusive.
        assert_eq!(
            judge(&s, &inside(Some("2019-01-01"), &[])),
            Applicability::Applicable
        );
        // The end is the first day out of force, so it is exclusive.
        let after = judge(&s, &inside(Some("2021-01-01"), &[]));
        assert!(matches!(
            after,
            Applicability::Inapplicable {
                reason: InapplicableReason::Repealed { .. }
            }
        ));
        let before = judge(&s, &inside(Some("2018-12-31"), &[]));
        assert!(matches!(
            before,
            Applicability::Inapplicable {
                reason: InapplicableReason::NotYetInForce { .. }
            }
        ));
    }

    #[test]
    fn an_open_start_applies_from_its_first_day() {
        let s = scope(Some("2021-01-01"), None, None, None);
        assert_eq!(
            judge(&s, &inside(Some("2021-01-01"), &[])),
            Applicability::Applicable
        );
        assert_eq!(
            judge(&s, &inside(Some("2030-01-01"), &[])),
            Applicability::Applicable
        );
        assert!(matches!(
            judge(&s, &inside(Some("2020-12-31"), &[])),
            Applicability::Inapplicable {
                reason: InapplicableReason::NotYetInForce { .. }
            }
        ));
    }

    #[test]
    fn an_open_end_applies_until_its_last_day() {
        let s = scope(None, Some("2021-01-01"), None, None);
        assert_eq!(
            judge(&s, &inside(Some("2000-01-01"), &[])),
            Applicability::Applicable
        );
        assert_eq!(
            judge(&s, &inside(Some("2020-12-31"), &[])),
            Applicability::Applicable
        );
        assert!(matches!(
            judge(&s, &inside(Some("2021-01-01"), &[])),
            Applicability::Inapplicable {
                reason: InapplicableReason::Repealed { .. }
            }
        ));
    }

    #[test]
    fn a_fact_occurrence_date_is_a_reference_date_too() {
        let s = scope(Some("2021-01-01"), None, None, None);
        // The session's as-of date is inside the range, but the fact happened
        // before the rule existed: the rule cannot govern it.
        let verdict = judge(&s, &inside(Some("2026-01-01"), &["2019-05-01"]));
        assert!(matches!(
            verdict,
            Applicability::Inapplicable {
                reason: InapplicableReason::NotYetInForce { .. }
            }
        ));
        // The session date is outside the range while the fact's date is
        // inside: the query date is also a reference date.
        let s = scope(None, Some("2021-01-01"), None, None);
        let verdict = judge(&s, &inside(Some("2021-06-01"), &["2020-01-01"]));
        assert!(matches!(
            verdict,
            Applicability::Inapplicable {
                reason: InapplicableReason::Repealed { .. }
            }
        ));
    }

    #[test]
    fn missing_reference_dates_are_unchecked_and_never_inapplicable() {
        let s = scope(Some("2021-01-01"), Some("2025-01-01"), None, None);
        let verdict = judge(&s, &inside(None, &[]));
        assert_eq!(
            verdict,
            Applicability::Unchecked {
                missing: MissingInput::NoCaseDate
            }
        );
        assert!(verdict.allows_firing());
    }

    #[test]
    fn a_date_the_loader_would_refuse_is_undecidable_not_a_guess() {
        let s = scope(Some("2021-01-01"), None, None, None);
        let verdict = judge(&s, &inside(Some("2021-02-30"), &[]));
        assert!(matches!(
            verdict,
            Applicability::Undecidable {
                reason: UndecidableReason::InvalidDate {
                    field: DateField::AsOf,
                    ..
                }
            }
        ));
        let s = scope(Some("2021-02-30"), None, None, None);
        assert!(matches!(
            judge(&s, &inside(Some("2021-06-01"), &[])),
            Applicability::Undecidable {
                reason: UndecidableReason::InvalidDate {
                    field: DateField::EffectiveFrom,
                    ..
                }
            }
        ));
    }

    #[test]
    fn an_inverted_or_empty_interval_is_undecidable() {
        let s = scope(Some("2021-01-01"), Some("2021-01-01"), None, None);
        assert!(matches!(
            judge(&s, &inside(Some("2020-01-01"), &[])),
            Applicability::Undecidable {
                reason: UndecidableReason::InvertedInterval { .. }
            }
        ));
    }

    #[test]
    fn equal_disjoint_and_nested_jurisdiction_codes() {
        let s = scope(None, None, Some("CN"), None);
        assert_eq!(
            judge(&s, &anchor(None, Some("CN"), &[], &[])),
            Applicability::Applicable
        );
        assert!(matches!(
            judge(&s, &anchor(None, Some("JP"), &[], &[])),
            Applicability::Inapplicable {
                reason: InapplicableReason::JurisdictionMismatch { .. }
            }
        ));
        // One code is a prefix of the other: containment is a declared fact the
        // environment does not contain, so the comparison cannot conclude.
        assert!(matches!(
            judge(&s, &anchor(None, Some("CN-HN"), &[], &[])),
            Applicability::Undecidable {
                reason: UndecidableReason::IncomparableCode {
                    dimension: CodeDimension::Jurisdiction,
                    ..
                }
            }
        ));
        // A missing session jurisdiction is missing input, not a mismatch.
        assert_eq!(
            judge(&s, &anchor(None, None, &[], &[])),
            Applicability::Unchecked {
                missing: MissingInput::NoQueryJurisdiction
            }
        );
    }

    #[test]
    fn equal_disjoint_and_nested_territory_codes() {
        let s = scope(None, None, None, Some("CN-BJ"));
        assert_eq!(
            judge(&s, &anchor(None, None, &[], &["CN-BJ"])),
            Applicability::Applicable
        );
        assert!(matches!(
            judge(&s, &anchor(None, None, &[], &["CN-HN"])),
            Applicability::Inapplicable {
                reason: InapplicableReason::TerritoryMismatch { .. }
            }
        ));
        assert_eq!(
            judge(&s, &anchor(None, None, &[], &[])),
            Applicability::Unchecked {
                missing: MissingInput::NoCasePlace
            }
        );
        assert!(matches!(
            judge(&s, &anchor(None, None, &[], &["CN"])),
            Applicability::Undecidable {
                reason: UndecidableReason::IncomparableCode {
                    dimension: CodeDimension::Territory,
                    ..
                }
            }
        ));
        // Every place the case records must be covered.
        assert!(matches!(
            judge(&s, &anchor(None, None, &[], &["CN-BJ", "CN-HN"])),
            Applicability::Inapplicable {
                reason: InapplicableReason::TerritoryMismatch { .. }
            }
        ));
    }

    #[test]
    fn a_rule_without_any_scope_is_unchecked_even_when_the_case_has_values() {
        let s = scope(None, None, None, None);
        let verdict = judge(&s, &anchor(Some("2020-01-01"), Some("CN"), &[], &["CN"]));
        assert_eq!(
            verdict,
            Applicability::Unchecked {
                missing: MissingInput::RuleHasNoScope
            }
        );
    }

    #[test]
    fn inapplicable_outranks_missing_and_undecidable_outranks_nothing_when_missing() {
        // A certain temporal exclusion wins over a missing jurisdiction: the
        // reader first learns that the rule certainly does not apply.
        let s = scope(Some("2021-01-01"), None, Some("CN"), None);
        let verdict = judge(&s, &anchor(Some("2019-01-01"), None, &[], &[]));
        assert!(matches!(verdict, Applicability::Inapplicable { .. }));

        // Missing input is reported before an undecidable comparison when both
        // occur: the user can fix the missing input, while the code relation is
        // not something to act on first.
        let s = scope(None, None, Some("CN"), Some("CN-BJ"));
        let verdict = judge(&s, &anchor(None, None, &[], &["CN"]));
        assert_eq!(
            verdict,
            Applicability::Unchecked {
                missing: MissingInput::NoQueryJurisdiction
            }
        );
    }

    #[test]
    fn every_non_inapplicable_verdict_allows_firing() {
        assert!(Applicability::Applicable.allows_firing());
        assert!(Applicability::Unchecked {
            missing: MissingInput::NoCaseDate
        }
        .allows_firing());
        assert!(Applicability::Undecidable {
            reason: UndecidableReason::InvertedInterval {
                from: "2021-01-01".into(),
                to: "2020-01-01".into(),
            }
        }
        .allows_firing());
        assert!(!Applicability::Inapplicable {
            reason: InapplicableReason::JurisdictionMismatch {
                rule: "CN".into(),
                case: "JP".into(),
            }
        }
        .allows_firing());
    }
}
