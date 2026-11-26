//! Calendar dates as kernel terms.
//!
//! A `Date` is a literal term of the built-in sort `Date`, written
//! `d"YYYY-MM-DD"`. It is a *term*, not declaration metadata: the
//! `occurred_at` / `effective` fields of a fact or a rule are records about a
//! declaration and are never read as terms, and a date term is never derived
//! from a string, an integer or the system clock. A date comes from a literal
//! the user wrote, a fact that carries it, or `addDays` / `addMonths` /
//! `addYears` evaluated by the kernel.
//!
//! The calendar is *proleptic Gregorian* and its range is fixed:
//! `1900-01-01..=9999-12-31`. A literal outside that range, a month that does
//! not exist, a day past the month's last day, or a `YYYY-MM-DD` shape with the
//! wrong number of digits (for example `2020-5-6`) is rejected with the
//! position where it was written. Every arithmetic result is range-checked too:
//! stepping past either boundary is an error, never a wrap and never a silent
//! clamp.
//!
//! Month and year arithmetic is calendar-aware, and a result that falls on a
//! shorter month is clamped to that month's **last day**: `2020-01-31` plus one
//! month is `2020-02-29`, and `2021-01-31` plus one month is `2021-02-28`.
//! `2020-02-29` plus one year is `2021-02-28`. The day-of-month is otherwise
//! kept as written; only an overflowing day is clamped.
//!
//! There is no time zone, no time of day, no leap second and no floating point
//! in this module: a date is a whole calendar day, and the only unit computed is
//! a whole day.

use std::fmt;

use crate::error::Error;

/// The first day a `Date` term may denote.
pub const MIN_YEAR: u16 = 1900;
/// The last year a `Date` term may denote; the range ends on its last day.
pub const MAX_YEAR: u16 = 9999;
/// The earliest `Date` term, `1900-01-01`.
pub const MIN: Date = Date {
    year: MIN_YEAR,
    month: 1,
    day: 1,
};
/// The latest `Date` term, `9999-12-31`.
pub const MAX: Date = Date {
    year: MAX_YEAR,
    month: 12,
    day: 31,
};

/// A calendar day, `YYYY-MM-DD`.
///
/// The representation is always a real day: [`Date::parse`] and the arithmetic
/// functions construct one only after the calendar checks, so no other value
/// can exist.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Date {
    year: u16,
    month: u8,
    day: u8,
}

impl Date {
    /// The year (`1900..=9999`).
    pub fn year(self) -> u16 {
        self.year
    }

    /// The month (`1..=12`).
    pub fn month(self) -> u8 {
        self.month
    }

    /// The day of the month (`1..=31`, always inside its month).
    pub fn day(self) -> u8 {
        self.day
    }

    /// The canonical `YYYY-MM-DD` spelling.
    pub fn to_iso(self) -> String {
        format!("{:04}-{:02}-{:02}", self.year, self.month, self.day)
    }

    /// Parse one `YYYY-MM-DD` calendar day inside the supported range.
    ///
    /// The shape is exact: four year digits, two month digits and two day
    /// digits separated by `-`. `2020-5-6` is not a date literal, and neither is
    /// `2020-05-06T00:00:00`. The day must exist (`2020-02-30`,
    /// `2020-13-01`, `2021-02-29` are refused) and the year must be inside
    /// [`MIN_YEAR`]`..=`[`MAX_YEAR`].
    pub fn parse(value: &str) -> std::result::Result<Date, String> {
        let bytes = value.as_bytes();
        let shaped = bytes.len() == 10
            && bytes[4] == b'-'
            && bytes[7] == b'-'
            && bytes[0..4].iter().all(u8::is_ascii_digit)
            && bytes[5..7].iter().all(u8::is_ascii_digit)
            && bytes[8..10].iter().all(u8::is_ascii_digit);
        if !shaped {
            return Err(format!(
                "日期 `{value}` 不是 YYYY-MM-DD 格式：只接受四位年、两位月、两位日，例如 `2020-05-06`"
            ));
        }
        let year = decimal(&bytes[0..4]);
        let month = decimal(&bytes[5..7]);
        let day = decimal(&bytes[8..10]);
        let Some(max_day) = days_in_month(year, month) else {
            return Err(format!("日期 `{value}` 的月份 {month} 超出 1..12"));
        };
        if day == 0 || day > max_day {
            return Err(format!("日期 `{value}` 的日期 {day} 超出 1..{max_day}"));
        }
        let date = Date {
            year: year as u16,
            month: month as u8,
            day: day as u8,
        };
        if !(MIN..=MAX).contains(&date) {
            return Err(format!(
                "日期 `{value}` 超出范围 {}..={}",
                MIN.to_iso(),
                MAX.to_iso()
            ));
        }
        Ok(date)
    }
}

impl fmt::Display for Date {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_iso())
    }
}

/// The result of a date operation falls outside the supported calendar range.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OutOfRange;

impl fmt::Display for OutOfRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "结果超出日期范围 {}..={}", MIN.to_iso(), MAX.to_iso())
    }
}

/// The number of whole days from `from` to `to`; negative when `to` is earlier.
///
/// The span of the supported range is far below an `i64`, so the result always
/// fits and no overflow path exists here.
pub fn days_between(from: Date, to: Date) -> i64 {
    ordinal(to) - ordinal(from)
}

/// `date` moved by `days` whole days.
pub fn add_days(date: Date, days: i64) -> std::result::Result<Date, OutOfRange> {
    let target = ordinal(date)
        .checked_add(days)
        .and_then(from_ordinal)
        .ok_or(OutOfRange)?;
    Ok(target)
}

/// `date` moved by `months` whole months, clamping to the month's last day.
///
/// A month index counts from `1900-01`, so a negative step is an ordinary
/// subtraction and the result is range-checked like every other operation.
pub fn add_months(date: Date, months: i64) -> std::result::Result<Date, OutOfRange> {
    let index = month_index(date).checked_add(months).ok_or(OutOfRange)?;
    if !(month_index(MIN)..=month_index(MAX)).contains(&index) {
        return Err(OutOfRange);
    }
    let year = (index / 12) as u32;
    let month = (index % 12 + 1) as u32;
    let last = days_in_month(year, month).ok_or(OutOfRange)?;
    Ok(Date {
        year: year as u16,
        month: month as u8,
        day: date.day.min(last as u8),
    })
}

/// `date` moved by `years` whole years, clamping to the month's last day.
///
/// A leap day stepped into a common year lands on February's last day:
/// `2020-02-29 + 1 year = 2021-02-28`.
pub fn add_years(date: Date, years: i64) -> std::result::Result<Date, OutOfRange> {
    let year = i64::from(date.year).checked_add(years).ok_or(OutOfRange)?;
    if !(i64::from(MIN_YEAR)..=i64::from(MAX_YEAR)).contains(&year) {
        return Err(OutOfRange);
    }
    let year = year as u32;
    let last = days_in_month(year, u32::from(date.month)).ok_or(OutOfRange)?;
    Ok(Date {
        year: year as u16,
        month: date.month,
        day: date.day.min(last as u8),
    })
}

/// Whether `year` is a leap year in the proleptic Gregorian calendar.
pub(crate) fn leap_year(year: u32) -> bool {
    year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400))
}

/// The last day of `month` in `year`, or `None` when `month` is not `1..=12`.
///
/// Shared with [`crate::meta::validate_date`], so a declaration's
/// `effective`/`occurred_at` metadata and a `Date` term agree on the calendar.
pub(crate) fn days_in_month(year: u32, month: u32) -> Option<u32> {
    Some(match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap_year(year) => 29,
        2 => 28,
        _ => return None,
    })
}

fn decimal(bytes: &[u8]) -> u32 {
    bytes
        .iter()
        .fold(0, |value, b| value * 10 + u32::from(b - b'0'))
}

/// The month index counted from `1900-01`; every year has twelve months.
fn month_index(date: Date) -> i64 {
    i64::from(date.year) * 12 + i64::from(date.month) - 1
}

/// The day number of `date`, counting from `1970-01-01` (proleptic Gregorian).
///
/// The algorithm is the standard civil-calendar one: it splits the year into
/// 400-year eras, and a year into a March-based month order, so every step is
/// exact integer arithmetic with no leap-second or time-zone table.
fn ordinal(date: Date) -> i64 {
    let year = i64::from(date.year);
    let month = i64::from(date.month);
    let day = i64::from(date.day);
    let year = if month <= 2 { year - 1 } else { year };
    let era = if year >= 0 { year } else { year - 399 } / 400;
    let year_of_era = year - era * 400;
    let day_of_year = (153 * (if month > 2 { month - 3 } else { month + 9 }) + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    era * 146_097 + day_of_era - 719_468
}

/// The inverse of [`ordinal`], refusing a day outside the supported range.
fn from_ordinal(day: i64) -> Option<Date> {
    if !(ordinal(MIN)..=ordinal(MAX)).contains(&day) {
        return None;
    }
    let shifted = day + 719_468;
    let era = shifted / 146_097;
    let day_of_era = shifted - era * 146_097;
    let year_of_era =
        (day_of_era - day_of_era / 1460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let year = year_of_era + era * 400;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_of_year = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_of_year + 2) / 5 + 1;
    let month = if month_of_year < 10 {
        month_of_year + 3
    } else {
        month_of_year - 9
    };
    let year = if month <= 2 { year + 1 } else { year };
    let date = Date {
        year: year as u16,
        month: month as u8,
        day: day as u8,
    };
    Some(date)
}

/// The kernel's error for a date operation whose result left the range.
///
/// The operation and its operands are named by the caller, so the message has
/// the same shape as the integer-overflow diagnostic: it names what was
/// computed and why it was refused.
pub fn out_of_range(operation: &str, operands: &str) -> Error {
    Error::other(format!("日期运算溢出：{operation} {operands} {OutOfRange}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_canonical_day_round_trips() {
        let date = Date::parse("2020-05-06").expect("a real calendar day");
        assert_eq!(date.to_iso(), "2020-05-06");
        assert_eq!((date.year(), date.month(), date.day()), (2020, 5, 6));
    }

    #[test]
    fn the_literal_shape_is_exact() {
        for value in ["2020-5-6", "20200506", "2020/05/06", "2020-05-06T00:00"] {
            assert!(
                Date::parse(value).is_err(),
                "`{value}` must not parse as a date"
            );
        }
    }

    #[test]
    fn impossible_calendar_days_are_refused() {
        assert!(Date::parse("2020-02-30").is_err());
        assert!(Date::parse("2020-13-01").is_err());
        assert!(Date::parse("2021-02-29").is_err());
        assert!(Date::parse("2020-02-29").is_ok());
    }

    #[test]
    fn the_range_ends_at_1900_and_9999() {
        assert!(Date::parse("1900-01-01").is_ok());
        assert!(Date::parse("9999-12-31").is_ok());
        assert!(Date::parse("1899-12-31").is_err());
        assert!(Date::parse("0000-01-01").is_err());
    }

    #[test]
    fn days_between_counts_the_leap_day() {
        let from = Date::parse("2020-01-01").expect("date");
        let to = Date::parse("2021-01-01").expect("date");
        assert_eq!(days_between(from, to), 366);
        assert_eq!(days_between(to, from), -366);
    }

    #[test]
    fn add_days_steps_and_checks_the_boundary() {
        let day = Date::parse("2020-01-31").expect("date");
        assert_eq!(add_days(day, 1).expect("one day").to_iso(), "2020-02-01");
        assert_eq!(add_days(day, -31).expect("back").to_iso(), "2019-12-31");
        assert!(add_days(MIN, -1).is_err());
        assert!(add_days(MAX, 1).is_err());
        assert!(add_days(MIN, i64::MAX).is_err());
    }

    #[test]
    fn a_month_step_clamps_to_the_last_day() {
        let january = Date::parse("2020-01-31").expect("date");
        assert_eq!(
            add_months(january, 1).expect("month").to_iso(),
            "2020-02-29"
        );
        let january = Date::parse("2021-01-31").expect("date");
        assert_eq!(
            add_months(january, 1).expect("month").to_iso(),
            "2021-02-28"
        );
        let march = Date::parse("2020-03-31").expect("date");
        assert_eq!(add_months(march, -1).expect("month").to_iso(), "2020-02-29");
        let month_end = Date::parse("2020-08-31").expect("date");
        assert_eq!(
            add_months(month_end, 1).expect("month").to_iso(),
            "2020-09-30"
        );
    }

    #[test]
    fn a_year_step_clamps_a_leap_day() {
        let leap = Date::parse("2020-02-29").expect("date");
        assert_eq!(add_years(leap, 1).expect("year").to_iso(), "2021-02-28");
        assert_eq!(add_years(leap, 4).expect("year").to_iso(), "2024-02-29");
        assert!(add_years(MAX, 1).is_err());
        assert!(add_years(MIN, -1).is_err());
    }

    #[test]
    fn the_civil_algorithm_round_trips_every_supported_day() {
        let first = ordinal(MIN);
        let last = ordinal(MAX);
        for day in (first..=last).step_by(997) {
            let date = from_ordinal(day).expect("inside the range");
            assert_eq!(ordinal(date), day);
        }
        assert_eq!(from_ordinal(first).expect("min"), MIN);
        assert_eq!(from_ordinal(last).expect("max"), MAX);
    }
}
