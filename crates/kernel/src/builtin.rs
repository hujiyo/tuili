//! The kernel's built-in integer type and arithmetic.
//!
//! Integers are exact: a value is an `i64`, and a literal is [`Expr::Num`].
//! There is no floating point anywhere in this kernel, and no rounding.
//!
//! The operations are ordinary constants with fixed types, so they appear in
//! terms exactly like a declared function does. What sets them apart is that
//! [`crate::norm::whnf`] *evaluates* them as soon as every argument is a
//! literal: `add 3000 2000` reduces to `5000`. When the head is not yet applied
//! to enough literals the term stays neutral, which is what lets a rule's
//! conclusion `add ?a ?b` be opened, matched and closed before it is ever a
//! number.
//!
//! Overflow is an error, never a wraparound: an `i64` result outside its range
//! is reported with the operation and its operands. Division is not
//! implemented, so division by zero cannot arise; a future division would have
//! to report it the same way.
//!
//! A comparison reduces to one of the two built-in propositions [`TRUE`] or
//! [`FALSE`]. That makes a comparison decidable by evaluation; it does not
//! give the reasoner a way to derive a comparison from facts, which stays out
//! of this step.

use crate::error::{Error, Result};
use crate::term::Expr;

/// The built-in integer type. A literal [`Expr::Num`] has this type.
pub const INT: &str = "Int";
/// Binary addition on [`INT`].
pub const ADD: &str = "add";
/// Binary subtraction on [`INT`].
pub const SUB: &str = "sub";
/// Binary multiplication on [`INT`].
pub const MUL: &str = "mul";
/// Unary negation on [`INT`].
pub const NEG: &str = "neg";
/// `less x y` is `x < y`.
pub const LESS: &str = "less";
/// `le x y` is `x ≤ y`.
pub const LE: &str = "le";
/// The proposition a true comparison reduces to.
pub const TRUE: &str = "True";
/// The proposition a false comparison reduces to.
pub const FALSE: &str = "False";

/// Every built-in name, in a stable order, so a diagnostic can list them.
pub const NAMES: &[&str] = &[INT, ADD, SUB, MUL, NEG, LESS, LE, TRUE, FALSE];

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
/// rule triggering.
pub fn comparison_head(expression: &Expr) -> Option<Op> {
    let name = expression.head_const()?;
    match Op::from_name(&name) {
        Some(op @ (Op::Less | Op::Le)) => Some(op),
        _ => None,
    }
}

/// The type of a built-in constant, or `None` when `name` is not built in.
///
/// `Int : Type`, the operations are functions over `Int`, and the two
/// comparison results are propositions. The types are built from the built-in
/// `Int` constant itself, so no environment declaration is involved.
pub fn type_of(name: &str) -> Option<Expr> {
    let int = || Expr::constant(INT);
    Some(match name {
        INT => Expr::Sort(1),
        TRUE | FALSE => Expr::Sort(0),
        ADD | SUB | MUL => Expr::pi(int(), Expr::pi(int(), int())),
        NEG => Expr::pi(int(), int()),
        LESS | LE => Expr::pi(int(), Expr::pi(int(), Expr::Sort(0))),
        _ => return None,
    })
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
}

impl Op {
    /// The operation a constant name stands for, or `None` for a name that is
    /// not an operation (including [`INT`], [`TRUE`] and [`FALSE`]).
    pub fn from_name(name: &str) -> Option<Op> {
        Some(match name {
            ADD => Op::Add,
            SUB => Op::Sub,
            MUL => Op::Mul,
            NEG => Op::Neg,
            LESS => Op::Less,
            LE => Op::Le,
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
        }
    }

    /// How many integer arguments the operation takes.
    pub fn arity(self) -> usize {
        match self {
            Op::Add | Op::Sub | Op::Mul | Op::Less | Op::Le => 2,
            Op::Neg => 1,
        }
    }

    /// Evaluate the operation on its literal arguments.
    ///
    /// Returns the reduced term: a literal for the arithmetic operations, or
    /// [`TRUE`] / [`FALSE`] for a comparison. An out-of-range `i64` result is
    /// an error naming the operation and its operands.
    pub fn apply(self, arguments: &[i64]) -> Result<Expr> {
        let overflow = || {
            let shown = arguments
                .iter()
                .map(i64::to_string)
                .collect::<Vec<_>>()
                .join(" ");
            Error::other(format!(
                "整数运算溢出：{} {} 的结果超出 i64 范围（{}..={}）",
                self.name(),
                shown,
                i64::MIN,
                i64::MAX
            ))
        };
        Ok(match (self, arguments) {
            (Op::Add, [x, y]) => Expr::Num(x.checked_add(*y).ok_or_else(overflow)?),
            (Op::Sub, [x, y]) => Expr::Num(x.checked_sub(*y).ok_or_else(overflow)?),
            (Op::Mul, [x, y]) => Expr::Num(x.checked_mul(*y).ok_or_else(overflow)?),
            (Op::Neg, [x]) => Expr::Num(x.checked_neg().ok_or_else(overflow)?),
            (Op::Less, [x, y]) => Expr::constant(if x < y { TRUE } else { FALSE }),
            (Op::Le, [x, y]) => Expr::constant(if x <= y { TRUE } else { FALSE }),
            // The kernel only calls this after checking the arity; a mismatch
            // is an internal inconsistency, not a user error, so it is
            // reported plainly instead of guessed at.
            _ => {
                return Err(Error::other(format!(
                    "内建运算 `{}` 的参数数量不匹配：期望 {} 个，实际 {} 个",
                    self.name(),
                    self.arity(),
                    arguments.len()
                )))
            }
        })
    }
}
