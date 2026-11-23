//! The environment identity a certificate records.
//!
//! The identity is built from what the session actually loaded: the canonical
//! profile name, the session's `--as-of` date and `--jurisdiction` code, every
//! pack with its manifest version, lock hash and trust level, and the hash of
//! every corpus file a loaded pack links. It is always a
//! [`EnvironmentIdentity::Recorded`]: an exported certificate that says
//! nothing about its environment cannot be checked against one later.
//!
//! The identity is strict on purpose. Packs are recorded in name order and
//! corpora in `(law, version)` order. A duplicate pack name, a corpus link
//! that cannot be read or hashed, and two links to one `(law, version)` with
//! different hashes are all errors; the certificate is never written with a
//! guessed or partial identity.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use std_deduce_cert::{
    CorpusRecord, EnvironmentIdentity, EnvironmentRecord, ExplicitText, PackRecord, TrustLevel,
};
use std_deduce_lang::module::escape_path;
use std_deduce_lawpack::corpus::hash_file;
use std_deduce_lawpack::Trust;

use crate::packs::LoadedPackInfo;

/// Build the identity of the current session.
///
/// `profile` is the canonical name the environment's `profile_name` reports,
/// `as_of` and `jurisdiction` are the session's `--as-of` / `--jurisdiction`
/// values (already validated when the arguments were parsed), `packs` are the
/// packs loaded in this session, and `corpus_root` is the directory that holds
/// `<law>/<version>.json` corpus files (the CLI uses
/// `<current directory>/law/corpus`). An unspecified `as_of` or jurisdiction is
/// recorded as an explicit `null`, never omitted.
pub(crate) fn build(
    profile: Option<&str>,
    as_of: Option<&str>,
    jurisdiction: Option<&str>,
    packs: &[LoadedPackInfo],
    corpus_root: &Path,
) -> Result<EnvironmentIdentity, String> {
    let mut pack_records: BTreeMap<String, PackRecord> = BTreeMap::new();
    for pack in packs {
        let record = PackRecord {
            name: pack.name.clone(),
            version: pack.version.clone(),
            hash: pack.hash.clone(),
            trust: trust_level(pack.trust),
        };
        if pack_records.insert(record.name.clone(), record).is_some() {
            return Err(format!(
                "包 `{}` 重复出现在已加载包中，无法记录环境身份",
                escape_path(&pack.name)
            ));
        }
    }

    let mut corpus_records: BTreeMap<(String, String), CorpusRecord> = BTreeMap::new();
    for pack in packs {
        let Some(link) = &pack.corpus else {
            continue;
        };
        let (law, version) = split_corpus_link(link, pack)?;
        let path = corpus_path(corpus_root, &law, &version);
        let hash = hash_file(&path).map_err(|error| {
            format!(
                "包 `{}` 链接的语料 `{}` 无法读取或哈希：{}",
                escape_path(&pack.name),
                escape_path(link),
                escape_path(&error.to_string())
            )
        })?;
        let record = CorpusRecord {
            law,
            version,
            file_sha256: hash,
        };
        let key = (record.law.clone(), record.version.clone());
        match corpus_records.get(&key) {
            Some(existing) if existing.file_sha256 != record.file_sha256 => {
                return Err(format!(
                    "语料 `{}/{}` 被不同包以不同哈希引用，无法记录单一身份",
                    escape_path(&key.0),
                    escape_path(&key.1)
                ));
            }
            Some(_) => {}
            None => {
                corpus_records.insert(key, record);
            }
        }
    }

    let record = EnvironmentRecord {
        profile: explicit_text(profile),
        packs: pack_records.into_values().collect(),
        corpora: corpus_records.into_values().collect(),
        as_of: explicit_text(as_of),
        jurisdiction: explicit_text(jurisdiction),
    };
    record
        .validate()
        .map_err(|error| format!("环境身份无效：{error}"))?;
    Ok(EnvironmentIdentity::Recorded(record))
}

/// The `<law>/<version>.json` path below the corpus root.
fn corpus_path(root: &Path, law: &str, version: &str) -> PathBuf {
    root.join(law).join(format!("{version}.json"))
}

/// Split a manifest's `<law>/<version>` corpus link.
///
/// The manifest already validates the link's shape when the registry is
/// scanned. This repeats the split so a link that somehow reaches the session
/// without the slash is an error instead of a guessed path.
fn split_corpus_link(link: &str, pack: &LoadedPackInfo) -> Result<(String, String), String> {
    let Some((law, version)) = link.split_once('/') else {
        return Err(format!(
            "包 `{}` 的语料链接 `{}` 不是 `<law>/<version>`",
            escape_path(&pack.name),
            escape_path(link)
        ));
    };
    if law.is_empty() || version.is_empty() {
        return Err(format!(
            "包 `{}` 的语料链接 `{}` 不是 `<law>/<version>`",
            escape_path(&pack.name),
            escape_path(link)
        ));
    }
    Ok((law.to_owned(), version.to_owned()))
}

/// Map the registry's open trust levels onto the certificate's closed enum.
fn trust_level(trust: Trust) -> TrustLevel {
    match trust {
        Trust::Experimental => TrustLevel::Experimental,
        Trust::Local => TrustLevel::Local,
        Trust::Community => TrustLevel::Community,
        Trust::Official => TrustLevel::Official,
    }
}

/// A present session value, or the explicit `null` the wire format requires.
fn explicit_text(value: Option<&str>) -> ExplicitText {
    value.map(ExplicitText::some).unwrap_or_default()
}
