//! The official legal-pack manifest, registry lock, and article corpus.
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
//! The crate also hashes pack content and manages the `std.lock` registry lock,
//! which records the version and content hash of every pack. Verification
//! compares a directory against its lock; it does not import or certify
//! anything either.
//!
//! [`corpus`] holds the article-level texts used to check a rule's quotation.
//! [`corpus::audit`] proves that a quotation matches a stored article; it does
//! not prove that a rule is a faithful or applicable reading of the law.
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

pub mod corpus;
mod date;
mod hex;
mod load;
mod lock;
mod manifest;

pub use load::{load, scan, LoadedPack, PackError, Scan, MANIFEST_FILE};
pub use lock::{
    build_lock, hash_pack, verify_lock, LockReport, LockedPack, Lockfile, LOCK_FILE, LOCK_VERSION,
};
pub use manifest::{Manifest, ManifestError, PackFile, PackInfo};
