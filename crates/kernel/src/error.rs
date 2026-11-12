//! Kernel errors. Every message is meant to be readable by someone who is
//! writing law or philosophy, not only by a type theorist.

use crate::term::Expr;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    /// A name was used that is not in the environment.
    UnknownName(String),
    /// A name was introduced although it is already taken.
    DuplicateName(String),
    /// The term does not have the type it claims.
    TypeMismatch { expected: Expr, actual: Expr },
    /// The expression is not a function type, so it cannot be applied.
    NotAFunction(Expr),
    /// Expected a sort, found something else.
    NotASort(Expr),
    /// A de Bruijn index escaped its binder.
    OutOfScope { index: usize, bound: usize },
    /// A declared rule is not *well-founded*: it would let the system derive
    /// the very thing it concludes, with no way to break the loop.
    NotWellFounded(String),
    /// An inductive hierarchy is not strictly positive.
    NotPositive(String),
    /// A universe constraint cannot be satisfied.
    UniverseMismatch { expected: u32, actual: u32 },
    /// A hard structural failure with a free-form explanation.
    Other(String),
}

impl Error {
    pub fn other(msg: impl Into<String>) -> Self {
        Error::Other(msg.into())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::UnknownName(n) => write!(f, "未知名称：{n}"),
            Error::DuplicateName(n) => write!(f, "名称已被占用：{n}"),
            Error::TypeMismatch { expected, actual } => {
                write!(f, "类型不匹配：期望 {expected}，实际 {actual}")
            }
            Error::NotAFunction(e) => write!(f, "这不是函数类型，无法应用于参数：{e}"),
            Error::NotASort(e) => write!(f, "期望一个类型（sort），得到：{e}"),
            Error::OutOfScope { index, bound } => {
                write!(f, "变量越界：索引 {index} 超出了 {bound} 层绑定")
            }
            Error::NotWellFounded(n) => write!(f, "规则 {n} 不满足有根据性"),
            Error::NotPositive(n) => write!(f, "归纳类型 {n} 不是严格正的"),
            Error::UniverseMismatch { expected, actual } => {
                write!(f, "宇宙层级不匹配：期望 Type {expected}，实际 Type {actual}")
            }
            Error::Other(s) => write!(f, "{s}"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;
