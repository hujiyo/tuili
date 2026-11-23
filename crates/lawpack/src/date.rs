//! Calendar-date validation, shared by pack manifests, corpora and the CLI.

/// Check that `value` is a real `YYYY-MM-DD` calendar day.
///
/// Only the shape and the calendar are checked; whether the date makes legal
/// sense in its context is left to the caller. `field` names the value in the
/// error; the CLI passes the option name. Exposed as
/// [`validate_date`](crate::validate_date) so a session option and a manifest
/// accept exactly the same dates.
pub fn validate(field: &str, value: &str) -> Result<(), String> {
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
