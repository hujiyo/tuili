//! The official legal-pack manifest.
//!
//! A legal pack is a directory containing a `lawpack.toml` manifest. The
//! manifest records the pack's identity, its jurisdiction and territory, its
//! effective date range, and the files that belong to it.
//!
//! This crate validates the manifest's *format* only. It does not import rules,
//! does not check that the listed files exist, and does not judge whether the
//! legal content is correct or applicable. Those are separate steps. Discovery
//! refuses symbolic links and pack directories that resolve outside the root.
//!
//! ```
//! use std_deduce_lawpack::Manifest;
//!
//! let text = r#"
//! [pack]
//! name = "cn.constitution"
//! version = "0.1.0"
//! jurisdiction = "CN"
//! territory = "CN"
//! effective_from = "1982-12-04"
//! "#;
//! let manifest = Manifest::parse(text).unwrap();
//! assert_eq!(manifest.pack.name, "cn.constitution");
//! ```

mod load;
mod manifest;

pub use load::{load, scan, LoadedPack, PackError, Scan, MANIFEST_FILE};
pub use manifest::{Manifest, ManifestError, PackFile, PackInfo};
