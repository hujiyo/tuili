//! Shared metadata validation and the declaration scope record.
//!
//! A rule declares when and where it is in force; a fact declares when and
//! where it occurred. The kernel stores the values, orders them for display,
//! and never uses them to decide whether a rule may fire: the judgement is the
//! reasoner's `Applicability`, computed from these records plus the session's
//! as-of date, jurisdiction and the case facts' occurrence. Keeping the
//! records in the kernel lets the language layer check a rule's scope without
//! depending on the package registry, while the judgement stays out of the
//! trusted core.
//!
//! The date and jurisdiction/code validators live here rather than in the
//! `lawpack` crate so the language layer can check a rule's scope without
//! depending on the package registry. `lawpack` re-exports them under its
//! original names, so a manifest, a `--jurisdiction` option and a rule clause
//! accept exactly the same formats.

/// Check that `value` is a real `YYYY-MM-DD` calendar day.
///
/// Only the shape and the calendar are checked; whether the date makes legal
/// sense in its context is left to the caller. `field` names the value in the
/// error.
pub fn validate_date(field: &str, value: &str) -> Result<(), String> {
    let bytes = value.as_bytes();
    let shaped = bytes.len() == 10
        && bytes[4] == b'-'
        && bytes[7] == b'-'
        && digits(&bytes[0..4])
        && digits(&bytes[5..7])
        && digits(&bytes[8..10]);
    if !shaped {
        return Err(format!("{field} `{value}` 不是 YYYY-MM-DD 日期"));
    }
    let year = decimal(&bytes[0..4]);
    let month = decimal(&bytes[5..7]);
    let max_day = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap_year(year) => 29,
        2 => 28,
        _ => {
            return Err(format!("{field} `{value}` 的月份 {month} 超出 1..12"));
        }
    };
    let day = decimal(&bytes[8..10]);
    if !(1..=max_day).contains(&day) {
        return Err(format!("{field} `{value}` 的日期 {day} 超出 1..{max_day}"));
    }
    Ok(())
}

/// Validate a jurisdiction or territory code.
///
/// The code must be non-empty and contain only ASCII letters, digits and `-`.
/// `pack.jurisdiction` / `pack.territory`, the CLI's `--jurisdiction` option,
/// a rule's `jurisdiction` / `territory` clause and a fact's `occurred_in`
/// clause all use this rule, so every surface accepts exactly the same codes.
/// `field` names the value in the error.
pub fn validate_jurisdiction_code(field: &str, value: &str) -> Result<(), String> {
    if value.is_empty() {
        return Err(format!("{field} 不能为空"));
    }
    let allowed = value
        .bytes()
        .all(|b| b.is_ascii_alphanumeric() || b == b'-');
    if !allowed {
        return Err(format!(
            "{field} `{value}` 含非法字符：只允许 ASCII 字母、数字和短横"
        ));
    }
    Ok(())
}

fn leap_year(year: u32) -> bool {
    year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400))
}

fn digits(bytes: &[u8]) -> bool {
    bytes.iter().all(|b| b.is_ascii_digit())
}

fn decimal(bytes: &[u8]) -> u32 {
    bytes
        .iter()
        .fold(0, |value, b| value * 10 + u32::from(b - b'0'))
}

/// Where a declaration's scope values came from.
///
/// The kernel does not infer or filter by scope; this field only records how
/// the values were determined, so the applicability judgement and a reader can
/// tell an explicit clause from a package default.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum ScopeOrigin {
    /// Written on the declaration itself (`effective` / `repealed` /
    /// `jurisdiction` / `territory`).
    Rule,
    /// Inherited from the containing law pack's manifest, because the rule did
    /// not write that field itself.
    PackDefault,
    /// Declared by a case-local rule in the closed environment; case rules
    /// never inherit a pack manifest.
    CaseLocal,
    /// No scope values were declared or inherited.
    #[default]
    Unspecified,
}

impl ScopeOrigin {
    /// The keyword written in a diagnostic or debug record.
    pub fn keyword(self) -> &'static str {
        match self {
            ScopeOrigin::Rule => "rule",
            ScopeOrigin::PackDefault => "pack_default",
            ScopeOrigin::CaseLocal => "case_local",
            ScopeOrigin::Unspecified => "unspecified",
        }
    }

    /// The compact Chinese label a reader sees in `:inspect`:
    /// `规则` for a value written on the rule, `继承` for a manifest default,
    /// `案件` for a case-local rule.
    pub fn label_zh(self) -> &'static str {
        match self {
            ScopeOrigin::Rule => "规则",
            ScopeOrigin::PackDefault => "继承",
            ScopeOrigin::CaseLocal => "案件",
            ScopeOrigin::Unspecified => "未注明",
        }
    }
}

/// The effective range and jurisdiction/territory a declaration records.
///
/// `effective_from` is inclusive and `effective_to` is exclusive: the date
/// written as `repealed` is the first day the rule is no longer in force. An
/// absent endpoint is an open interval. This is stored data only: the kernel
/// never decides whether a rule applies.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Scope {
    /// First day the declaration is in force (inclusive), `YYYY-MM-DD`.
    pub effective_from: Option<String>,
    /// First day it is no longer in force (exclusive), `YYYY-MM-DD`.
    pub effective_to: Option<String>,
    /// The legal system / enacting authority, not the place of the case.
    pub jurisdiction: Option<String>,
    /// The territory the declaration covers, when it differs from the
    /// jurisdiction.
    pub territory: Option<String>,
    /// How the record as a whole was determined: `Rule` when the rule wrote at
    /// least one field, `PackDefault` when every value was inherited,
    /// `CaseLocal` for a case-local rule, `Unspecified` when there is no data.
    /// This summary does not say which *field* was written; the per-field
    /// origins below do, so `:inspect` can mark each value.
    pub origin: ScopeOrigin,
    /// Provenance of [`Scope::effective_from`]; `Some` exactly when the value
    /// is present.
    pub effective_from_origin: Option<ScopeOrigin>,
    /// Provenance of [`Scope::effective_to`]; `Some` exactly when the value is
    /// present.
    pub effective_to_origin: Option<ScopeOrigin>,
    /// Provenance of [`Scope::jurisdiction`]; `Some` exactly when the value is
    /// present.
    pub jurisdiction_origin: Option<ScopeOrigin>,
    /// Provenance of [`Scope::territory`]; `Some` exactly when the value is
    /// present.
    pub territory_origin: Option<ScopeOrigin>,
}

impl Scope {
    /// Whether nothing was declared or inherited.
    pub fn is_unscoped(&self) -> bool {
        self.effective_from.is_none()
            && self.effective_to.is_none()
            && self.jurisdiction.is_none()
            && self.territory.is_none()
    }
}
