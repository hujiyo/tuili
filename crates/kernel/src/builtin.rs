//! The kernel's built-in literal types and the operations it evaluates.
//!
//! Integers are exact: a value is an `i64`, and a literal is [`Expr::Num`].
//! Dates are calendar days: a value is a [`crate::date::Date`], and a literal is
//! [`Expr::Date`]. There is no floating point anywhere in this kernel, no
//! rounding, and no conversion between the two literal types: an integer is
//! never read as a date, and a date is never read as a number.
//!
//! The operations are ordinary constants with fixed types, so they appear in
//! terms exactly like a declared function does. What sets them apart is that
//! [`crate::norm::whnf`] *evaluates* them as soon as every argument is a
//! literal: `add 3000 2000` reduces to `5000`, and `addYears d"2020-02-29" 1`
//! reduces to `d"2021-02-28"`. When the head is not yet applied to enough
//! literals the term stays neutral, which is what lets a rule's conclusion
//! `addYears ?d ?n` be opened, matched and closed before it is ever a value.
//!
//! An `i64` overflow or a date outside `1900-01-01..=9999-12-31` is an error,
//! never a wraparound or a clamp: the message names the operation and its
//! operands. There is no division, so division by zero cannot arise; a future
//! division would have to report it the same way.
//!
//! A comparison reduces to one of the two built-in propositions [`TRUE`] or
//! [`FALSE`]. `less` and `le` accept either two `Int` operands or two `Date`
//! operands — the operand types decide which comparison is meant, and a mixed
//! pair is an error rather than an implicit conversion. That makes a comparison
//! decidable by evaluation; it does not give the reasoner a way to derive a
//! comparison from facts. A rule `guard` is exactly this: an explicit
//! comparison over the instance's parameter values whose truth value is judged
//! per instance (see [`crate::norm::evaluate_comparison`]).

use crate::date::{self, Date};
use crate::error::{Error, Result};
use crate::term::Expr;

/// The built-in integer type. A literal [`Expr::Num`] has this type.
pub const INT: &str = "Int";
/// The built-in calendar-date type. A literal [`Expr::Date`] has this type.
pub const DATE: &str = "Date";
/// Binary addition on [`INT`].
pub const ADD: &str = "add";
/// Binary subtraction on [`INT`].
pub const SUB: &str = "sub";
/// Binary multiplication on [`INT`].
pub const MUL: &str = "mul";
/// Unary negation on [`INT`].
pub const NEG: &str = "neg";
/// `less x y` is `x < y`, on two [`INT`]s or two [`DATE`]s.
pub const LESS: &str = "less";
/// `le x y` is `x ≤ y`, on two [`INT`]s or two [`DATE`]s.
pub const LE: &str = "le";
/// `daysBetween d1 d2` is the whole-day distance from `d1` to `d2`, as an [`INT`].
pub const DAYS_BETWEEN: &str = "daysBetween";
/// `addDays d n` is `d` moved by `n` whole days.
pub const ADD_DAYS: &str = "addDays";
/// `addMonths d n` is `d` moved by `n` whole months, calendar-aware.
pub const ADD_MONTHS: &str = "addMonths";
/// `addYears d n` is `d` moved by `n` whole years, calendar-aware.
pub const ADD_YEARS: &str = "addYears";
/// The proposition a true comparison reduces to.
pub const TRUE: &str = "True";
/// The proposition a false comparison reduces to.
pub const FALSE: &str = "False";

/// Every built-in name, in a stable order, so a diagnostic can list them.
pub const NAMES: &[&str] = &[
    INT,
    DATE,
    ADD,
    SUB,
    MUL,
    NEG,
    LESS,
    LE,
    DAYS_BETWEEN,
    ADD_DAYS,
    ADD_MONTHS,
    ADD_YEARS,
    TRUE,
    FALSE,
];

/// Whether `name` is a built-in constant and therefore cannot be declared.
///
/// A declaration with a built-in name is refused instead of silently shadowing
/// the evaluation: `add` must mean the built-in addition everywhere, or a
/// certificate could not be rechecked.
pub fn is_reserved(name: &str) -> bool {
    NAMES.contains(&name)
}

/// The comparison operation an expression is headed by, if any.
///
/// A rule premise or `unless` headed by a comparison is refused at load time:
/// a comparison is a computed expression, not a proposition a fact can prove.
/// Turning "the comparison evaluated to `True`" into "the premise holds" would
/// be an implicit reduction pretending to be evidence, so it is not wired into
/// rule triggering. A `guard` is the one explicit place where a comparison is
/// judged, and it must be headed by this operation: the loader rejects a guard
/// that is not written as `less` or `le`.
pub fn comparison_head(expression: &Expr) -> Option<Op> {
    let name = expression.head_const()?;
    match Op::from_name(&name) {
        Some(op @ (Op::Less | Op::Le)) => Some(op),
        _ => None,
    }
}

/// The truth value a built-in comparison produced: `Some(true)` for [`TRUE`],
/// `Some(false)` for [`FALSE`], `None` for anything else.
///
/// This is a *reading* of the evaluated form, not a guess: a term that is
/// neither proposition carries no truth value, and the caller reports that
/// instead of treating it as false.
pub fn truth_value(expression: &Expr) -> Option<bool> {
    match expression {
        Expr::Const(name) => {
            let name = name.as_ref();
            if name == TRUE {
                Some(true)
            } else if name == FALSE {
                Some(false)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// The type of a built-in constant, or `None` when `name` is not built in.
///
/// `Int` and `Date` are sorts, the operations are functions over them, and the
/// two comparison results are propositions. The types are built from the built-in
/// sort constants themselves, so no environment declaration is involved.
///
/// `less` and `le` are the one overloaded pair: this table gives them the
/// `Int` type scheme, and [`crate::check::infer`] selects the `Date` scheme when
/// both operands are dates. A partially applied `less` therefore keeps the
/// `Int` reading; the surface syntax always applies it to both operands.
pub fn type_of(name: &str) -> Option<Expr> {
    let int = || Expr::constant(INT);
    let date = || Expr::constant(DATE);
    Some(match name {
        INT | DATE => Expr::Sort(1),
        TRUE | FALSE => Expr::Sort(0),
        ADD | SUB | MUL => Expr::pi(int(), Expr::pi(int(), int())),
        NEG => Expr::pi(int(), int()),
        LESS | LE => Expr::pi(int(), Expr::pi(int(), Expr::Sort(0))),
        DAYS_BETWEEN => Expr::pi(date(), Expr::pi(date(), int())),
        ADD_DAYS | ADD_MONTHS | ADD_YEARS => Expr::pi(date(), Expr::pi(int(), date())),
        _ => return None,
    })
}

/// One literal operand of a built-in operation.
///
/// The kind is part of the value: an [`Operand::Int`] is not a date and an
/// [`Operand::Date`] is not a number, so an operation that receives the wrong
/// kind refuses it explicitly instead of converting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operand {
    /// An exact integer literal.
    Int(i64),
    /// A calendar-day literal.
    Date(Date),
}

impl Operand {
    /// How the operand is printed in an error message.
    pub fn show(self) -> String {
        match self {
            Operand::Int(value) => value.to_string(),
            Operand::Date(value) => format!("d\"{}\"", value.to_iso()),
        }
    }
}

/// One built-in operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Neg,
    Less,
    Le,
    DaysBetween,
    AddDays,
    AddMonths,
    AddYears,
}

impl Op {
    /// The operation a constant name stands for, or `None` for a name that is
    /// not an operation (including the sort names, [`TRUE`] and [`FALSE`]).
    pub fn from_name(name: &str) -> Option<Op> {
        Some(match name {
            ADD => Op::Add,
            SUB => Op::Sub,
            MUL => Op::Mul,
            NEG => Op::Neg,
            LESS => Op::Less,
            LE => Op::Le,
            DAYS_BETWEEN => Op::DaysBetween,
            ADD_DAYS => Op::AddDays,
            ADD_MONTHS => Op::AddMonths,
            ADD_YEARS => Op::AddYears,
            _ => return None,
        })
    }

    /// The constant name.
    pub fn name(self) -> &'static str {
        match self {
            Op::Add => ADD,
            Op::Sub => SUB,
            Op::Mul => MUL,
            Op::Neg => NEG,
            Op::Less => LESS,
            Op::Le => LE,
            Op::DaysBetween => DAYS_BETWEEN,
            Op::AddDays => ADD_DAYS,
            Op::AddMonths => ADD_MONTHS,
            Op::AddYears => ADD_YEARS,
        }
    }

    /// How many literal arguments the operation takes.
    pub fn arity(self) -> usize {
        match self {
            Op::Neg => 1,
            _ => 2,
        }
    }

    /// The operand kinds as they are written in a diagnostic.
    fn signature(self) -> &'static str {
        match self {
            Op::Add | Op::Sub | Op::Mul => "Int Int → Int",
            Op::Neg => "Int → Int",
            Op::Less | Op::Le => "Int Int → Prop 或 Date Date → Prop",
            Op::DaysBetween => "Date Date → Int",
            Op::AddDays | Op::AddMonths | Op::AddYears => "Date Int → Date",
        }
    }

    fn kind_error(self, operands: &[Operand]) -> Error {
        let shown = operands
            .iter()
            .map(|operand| operand.show())
            .collect::<Vec<_>>()
            .join(" ");
        Error::other(format!(
            "内建运算 `{}` 的操作数类型不匹配：期望 {}，实际（{}）；本系统不做隐式转换",
            self.name(),
            self.signature(),
            shown
        ))
    }

    fn overflow(self, operands: &[Operand]) -> Error {
        let shown = operands
            .iter()
            .map(|operand| operand.show())
            .collect::<Vec<_>>()
            .join(" ");
        Error::other(format!(
            "整数运算溢出：{} {} 的结果超出 i64 范围（{}..={}）",
            self.name(),
            shown,
            i64::MIN,
            i64::MAX
        ))
    }

    fn date_overflow(self, operands: &[Operand]) -> Error {
        let shown = operands
            .iter()
            .map(|operand| operand.show())
            .collect::<Vec<_>>()
            .join(" ");
        date::out_of_range(self.name(), &shown)
    }

    /// Evaluate the operation on its literal arguments.
    ///
    /// Returns the reduced term: a literal for the arithmetic operations, [`TRUE`]
    /// / [`FALSE`] for a comparison. An `i64` overflow, a date outside the
    /// supported range, or an operand of the wrong kind is an error naming the
    /// operation and its operands.
    pub fn apply(self, operands: &[Operand]) -> Result<Expr> {
        if operands.len() != self.arity() {
            // The kernel only calls this after checking the arity; a mismatch
            // is an internal inconsistency, not a user error, so it is
            // reported plainly instead of guessed at.
            return Err(Error::other(format!(
                "内建运算 `{}` 的参数数量不匹配：期望 {} 个，实际 {} 个",
                self.name(),
                self.arity(),
                operands.len()
            )));
        }
        Ok(match (self, operands) {
            (Op::Add, [Operand::Int(x), Operand::Int(y)]) => {
                Expr::Num(x.checked_add(*y).ok_or_else(|| self.overflow(operands))?)
            }
            (Op::Sub, [Operand::Int(x), Operand::Int(y)]) => {
                Expr::Num(x.checked_sub(*y).ok_or_else(|| self.overflow(operands))?)
            }
            (Op::Mul, [Operand::Int(x), Operand::Int(y)]) => {
                Expr::Num(x.checked_mul(*y).ok_or_else(|| self.overflow(operands))?)
            }
            (Op::Neg, [Operand::Int(x)]) => {
                Expr::Num(x.checked_neg().ok_or_else(|| self.overflow(operands))?)
            }
            // A comparison is typed over one literal kind at a time: two
            // integers or two dates. A mixed pair is refused rather than
            // converted, and it is refused here as well as by the type checker.
            (Op::Less, [Operand::Int(x), Operand::Int(y)]) => {
                Expr::constant(if x < y { TRUE } else { FALSE })
            }
            (Op::Le, [Operand::Int(x), Operand::Int(y)]) => {
                Expr::constant(if x <= y { TRUE } else { FALSE })
            }
            (Op::Less, [Operand::Date(x), Operand::Date(y)]) => {
                Expr::constant(if x < y { TRUE } else { FALSE })
            }
            (Op::Le, [Operand::Date(x), Operand::Date(y)]) => {
                Expr::constant(if x <= y { TRUE } else { FALSE })
            }
            (Op::DaysBetween, [Operand::Date(from), Operand::Date(to)]) => {
                Expr::Num(date::days_between(*from, *to))
            }
            (Op::AddDays, [Operand::Date(from), Operand::Int(days)]) => {
                Expr::Date(date::add_days(*from, *days).map_err(|_| self.date_overflow(operands))?)
            }
            (Op::AddMonths, [Operand::Date(from), Operand::Int(months)]) => Expr::Date(
                date::add_months(*from, *months).map_err(|_| self.date_overflow(operands))?,
            ),
            (Op::AddYears, [Operand::Date(from), Operand::Int(years)]) => Expr::Date(
                date::add_years(*from, *years).map_err(|_| self.date_overflow(operands))?,
            ),
            _ => return Err(self.kind_error(operands)),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(value: i64) -> Operand {
        Operand::Int(value)
    }

    fn day(value: &str) -> Operand {
        Operand::Date(Date::parse(value).expect("a real calendar day"))
    }

    #[test]
    fn a_comparison_of_mixed_kinds_is_refused() {
        let error = Op::Less.apply(&[int(1), day("2020-05-06")]).unwrap_err();
        assert!(error.to_string().contains("不做隐式转换"), "{error}");
    }

    #[test]
    fn a_date_operation_refuses_an_integer_operand() {
        let error = Op::AddYears.apply(&[int(2020), int(1)]).unwrap_err();
        assert!(error.to_string().contains("addYears"), "{error}");
    }

    #[test]
    fn the_date_operations_evaluate_on_literals() {
        assert_eq!(
            Op::DaysBetween
                .apply(&[day("2020-01-01"), day("2021-01-01")])
                .expect("days"),
            Expr::Num(366)
        );
        assert_eq!(
            Op::AddYears
                .apply(&[day("2020-02-29"), int(1)])
                .expect("years"),
            Expr::Date(Date::parse("2021-02-28").expect("date"))
        );
        assert_eq!(
            Op::AddMonths
                .apply(&[day("2020-01-31"), int(1)])
                .expect("months"),
            Expr::Date(Date::parse("2020-02-29").expect("date"))
        );
        assert_eq!(
            Op::AddDays
                .apply(&[day("2020-01-31"), int(1)])
                .expect("days"),
            Expr::Date(Date::parse("2020-02-01").expect("date"))
        );
    }

    #[test]
    fn stepping_past_the_range_is_an_error() {
        let error = Op::AddDays.apply(&[day("9999-12-31"), int(1)]).unwrap_err();
        let message = error.to_string();
        assert!(message.contains("日期运算溢出"), "{message}");
        assert!(message.contains("1900-01-01..=9999-12-31"), "{message}");
    }
}
