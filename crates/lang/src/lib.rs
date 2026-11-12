//! The language layer.
//!
//! Nothing in this crate is trusted. The kernel re-checks every term produced
//! here.

pub mod ast;
pub mod elab;
pub mod lexer;
pub mod module;
pub mod parser;

pub use module::{Library, LoadError, LoadReport, Theory};
pub use parser::Parser;
