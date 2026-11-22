//! Article-level legal corpora and rule-citation auditing.
//!
//! A corpus is a JSON file at `corpus/<law-id>/<version>.json` that records the
//! official text of individual articles. [`audit`] compares a rule's recorded
//! citation with one of those texts. It proves only that the quotation matches
//! the stored article: it does not prove that the rule faithfully formalises
//! the article, that the article applies to a case, or that the law is correct.
//!
//! Corpus files are static repository data; this crate never downloads one.
//! Parsing is strict: `deny_unknown_fields`, a supported format version, real
//! calendar dates, a well-formed `sha256:` value, a non-empty article list and
//! unique article numbers. A broken corpus is an error, never a skipped file.
//!
//! The audit reads exactly the fields of a rule's `source` that bear on the
//! quotation: the instrument name, the article number, the version, the quoted
//! wording, the hash and the jurisdiction.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use serde::Deserialize;
use sha2::{Digest, Sha256};

use crate::{date, hex};

/// The corpus format version this crate understands.
pub const CORPUS_FORMAT: u32 = 1;

/// The corpus file extension.
const CORPUS_EXTENSION: &str = "json";

/// A parsed article-level corpus.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Corpus {
    /// Corpus format version; currently [`CORPUS_FORMAT`].
    pub format: u32,
    /// Stable law id: lowercase ASCII letters, digits, `.` and `-`.
    pub law: String,
    /// Display title, also matched against a citation's `text`.
    pub title: String,
    /// Other names a citation may use for this instrument.
    #[serde(default)]
    pub aliases: Vec<String>,
    /// Version matched against a citation's `version`, for example `2018`.
    pub version: String,
    /// Jurisdiction code, for example `CN`.
    pub jurisdiction: String,
    /// First effective date, `YYYY-MM-DD`.
    #[serde(default)]
    pub effective_from: Option<String>,
    /// Where the official text was retrieved from.
    #[serde(default)]
    pub source_url: Option<String>,
    /// Retrieval date, `YYYY-MM-DD`.
    #[serde(default)]
    pub retrieved_at: Option<String>,
    /// SHA-256 of the source text this corpus was excerpted from, as
    /// `sha256:` followed by 64 lowercase hex digits. Recorded provenance:
    /// the audit does not recompute it.
    #[serde(default)]
    pub text_sha256: Option<String>,
    /// Free-form note, for example how a correction was recorded in the
    /// corpus. Never used for matching.
    #[serde(default)]
    pub notes: Option<String>,
    /// The articles, in the order the corpus lists them.
    pub articles: Vec<Article>,
}

/// One article of a corpus.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Article {
    /// Article number as written in the law, for example `第三十九条`.
    pub number: String,
    /// The article's body: no `第X条` prefix, paragraphs joined with `\n`.
    pub text: String,
}

/// A corpus file that could not be read or validated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CorpusError {
    path: PathBuf,
    message: String,
}

impl CorpusError {
    fn new(path: PathBuf, message: impl Into<String>) -> Self {
        CorpusError {
            path,
            message: message.into(),
        }
    }

    /// The path the error belongs to.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// The error message, without the path.
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for CorpusError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}：{}", self.path.display(), self.message)
    }
}

impl std::error::Error for CorpusError {}

/// A corpus found on disk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoadedCorpus {
    /// The JSON file.
    pub path: PathBuf,
    /// Its parsed and validated content.
    pub corpus: Corpus,
}

/// Everything one scan of a corpus directory found.
///
/// An empty `corpora` list with no `errors` means the directory holds no
/// corpus, not that every citation passed: the caller must treat that as
/// "nothing was verified".
#[derive(Debug, Default)]
pub struct Scan {
    /// Corpora that parsed and validated, in stable path order.
    pub corpora: Vec<LoadedCorpus>,
    /// Files that could not be read or validated.
    pub errors: Vec<CorpusError>,
}

impl Corpus {
    /// Parse and validate a corpus from JSON text.
    ///
    /// A path is not available here, so errors say `corpus.json`.
    pub fn parse(text: &str) -> Result<Corpus, CorpusError> {
        parse_at(Path::new("corpus.json"), text)
    }

    /// Read, parse and validate a corpus file.
    pub fn read(path: &Path) -> Result<Corpus, CorpusError> {
        let text = fs::read_to_string(path).map_err(|error| {
            CorpusError::new(path.to_path_buf(), format!("无法读取语料文件：{error}"))
        })?;
        parse_at(path, &text)
    }

    /// Does a citation's instrument name match this corpus's title or aliases?
    ///
    /// Both sides are whitespace-normalized: trimmed and with every run of
    /// whitespace collapsed to one space.
    pub fn matches_name(&self, text: &str) -> bool {
        let wanted = normalize_space(text);
        normalize_space(&self.title) == wanted
            || self
                .aliases
                .iter()
                .any(|alias| normalize_space(alias) == wanted)
    }

    /// The article whose number matches `locator` after whitespace
    /// normalization.
    pub fn article(&self, locator: &str) -> Option<&Article> {
        let wanted = normalize_space(locator);
        self.articles
            .iter()
            .find(|article| normalize_space(&article.number) == wanted)
    }

    fn validate(&self) -> Result<(), String> {
        if self.format != CORPUS_FORMAT {
            return Err(format!(
                "不支持的语料格式版本 {}：当前只支持 {CORPUS_FORMAT}",
                self.format
            ));
        }
        if self.law.is_empty() {
            return Err("law 不能为空".to_owned());
        }
        let law_allowed = self.law.bytes().all(|byte| {
            byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'.' || byte == b'-'
        });
        if !law_allowed {
            return Err(format!(
                "law `{}` 含非法字符：只允许小写 ASCII 字母、数字、点和短横",
                self.law
            ));
        }
        require_text("title", &self.title)?;
        require_text("version", &self.version)?;
        require_text("jurisdiction", &self.jurisdiction)?;
        if let Some(value) = &self.effective_from {
            date::validate("effective_from", value)?;
        }
        if let Some(value) = &self.retrieved_at {
            date::validate("retrieved_at", value)?;
        }
        if let Some(value) = &self.text_sha256 {
            if !is_sha256(value) {
                return Err("text_sha256 必须是 sha256: 后接 64 位小写十六进制".to_owned());
            }
        }
        if self.articles.is_empty() {
            return Err("articles 不能为空：语料至少要有一条条文".to_owned());
        }
        let mut numbers = BTreeSet::new();
        for (index, article) in self.articles.iter().enumerate() {
            require_text(&format!("articles[{index}].number"), &article.number)?;
            require_text(&format!("articles[{index}].text"), &article.text)?;
            // Matching normalizes whitespace, so two numbers that only differ
            // in whitespace would be indistinguishable. Refuse them here
            // instead of silently picking the first one at audit time.
            let normalized = normalize_space(&article.number);
            if !numbers.insert(normalized) {
                return Err(format!("条号 `{}` 重复", article.number));
            }
        }
        Ok(())
    }
}

fn parse_at(path: &Path, text: &str) -> Result<Corpus, CorpusError> {
    let corpus: Corpus = serde_json::from_str(text).map_err(|error| {
        CorpusError::new(path.to_path_buf(), format!("语料 JSON 解析失败：{error}"))
    })?;
    corpus
        .validate()
        .map_err(|message| CorpusError::new(path.to_path_buf(), message))?;
    Ok(corpus)
}

fn require_text(field: &str, value: &str) -> Result<(), String> {
    if value.trim().is_empty() {
        Err(format!("{field} 不能为空"))
    } else {
        Ok(())
    }
}

/// Scan `root` for corpora laid out as `<law-id>/<version>.json`.
///
/// Only direct child directories are read, and only their regular `.json`
/// files. Files outside that layout are not corpora and are ignored. The only
/// fatal conditions are that `root` itself cannot be read; a missing or empty
/// corpus directory is an empty successful scan, which the caller must not
/// mistake for a passing audit.
///
/// A `(law, version)` pair may appear only once. A duplicate is reported and
/// the later file is not added, so the caller can report every error.
pub fn scan(root: &Path) -> Result<Scan, CorpusError> {
    let entries = fs::read_dir(root).map_err(|error| {
        CorpusError::new(root.to_path_buf(), format!("无法读取语料目录：{error}"))
    })?;
    let mut dirs = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|error| {
            CorpusError::new(root.to_path_buf(), format!("无法读取目录项：{error}"))
        })?;
        let file_type = entry.file_type().map_err(|error| {
            CorpusError::new(entry.path(), format!("无法读取目录项类型：{error}"))
        })?;
        if file_type.is_dir() {
            dirs.push(entry.path());
        }
    }
    // Directory order is platform-dependent; sort it so output is stable.
    dirs.sort();

    let mut corpora = Vec::new();
    let mut errors = Vec::new();
    let mut seen: BTreeMap<(String, String), PathBuf> = BTreeMap::new();
    for dir in dirs {
        let files = match corpus_files(&dir) {
            Ok(files) => files,
            Err(error) => {
                errors.push(error);
                continue;
            }
        };
        for path in files {
            match Corpus::read(&path) {
                Ok(corpus) => {
                    let key = (corpus.law.clone(), corpus.version.clone());
                    if let Some(first) = seen.get(&key) {
                        errors.push(CorpusError::new(
                            path,
                            format!(
                                "语料 `{}@{}` 与 {} 重复",
                                corpus.law,
                                corpus.version,
                                first.display()
                            ),
                        ));
                        continue;
                    }
                    seen.insert(key, path.clone());
                    corpora.push(LoadedCorpus { path, corpus });
                }
                Err(error) => errors.push(error),
            }
        }
    }
    Ok(Scan { corpora, errors })
}

fn corpus_files(dir: &Path) -> Result<Vec<PathBuf>, CorpusError> {
    let entries = fs::read_dir(dir).map_err(|error| {
        CorpusError::new(dir.to_path_buf(), format!("无法读取语料目录：{error}"))
    })?;
    let mut files = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|error| {
            CorpusError::new(dir.to_path_buf(), format!("无法读取目录项：{error}"))
        })?;
        let file_type = entry.file_type().map_err(|error| {
            CorpusError::new(entry.path(), format!("无法读取目录项类型：{error}"))
        })?;
        if !file_type.is_file() {
            continue;
        }
        let path = entry.path();
        if path.extension().and_then(|extension| extension.to_str()) == Some(CORPUS_EXTENSION) {
            files.push(path);
        }
    }
    // File order is platform-dependent; sort it so output is stable.
    files.sort();
    Ok(files)
}

/// The source fields an audit reads.
///
/// This mirrors the parts of a kernel `SourceRef` that bear on a quotation,
/// without making this crate depend on the kernel.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Citation<'a> {
    /// Instrument name, matched against a corpus's title and aliases.
    pub text: &'a str,
    /// Article number, matched against `Article::number`.
    pub locator: &'a str,
    /// Version, matched against `Corpus::version` when non-empty.
    pub version: &'a str,
    /// The quoted wording. Required for a check to happen.
    pub quote: &'a str,
    /// `sha256:<64 lowercase hex>` of the article text, when recorded.
    pub hash: &'a str,
    /// Jurisdiction code, compared with `Corpus::jurisdiction` when non-empty.
    pub jurisdiction: &'a str,
}

/// How one citation check ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Audit {
    /// The quotation matched the article (and the hash, when recorded).
    Hit,
    /// The source has no quotation, so nothing was checked.
    NoQuote,
    /// No corpus matched the instrument name, so nothing was checked.
    NoCorpus,
    /// The corpus has no article with the citation's number.
    NoArticle,
    /// The name matched, but no candidate corpus has the citation's version.
    VersionMismatch,
    /// Several candidate corpora remain and choosing one would be a guess.
    Ambiguous,
    /// The quotation differs from the article text.
    Mismatch,
    /// The recorded hash is malformed or does not match the article text.
    HashMismatch,
    /// The citation lacks an instrument name or an article number.
    InvalidSource,
    /// The citation's jurisdiction differs from the corpus's.
    JurisdictionMismatch,
}

impl Audit {
    /// Whether the quotation was checked and matched.
    pub fn is_hit(self) -> bool {
        self == Audit::Hit
    }

    /// Whether the source could not be checked at all. This is not a pass.
    pub fn is_unverified(self) -> bool {
        matches!(self, Audit::NoQuote | Audit::NoCorpus)
    }
}

/// Which corpus a citation was compared with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CorpusId {
    /// The corpus's law id.
    pub law: String,
    /// The corpus's version.
    pub version: String,
}

impl fmt::Display for CorpusId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}@{}", self.law, self.version)
    }
}

/// The outcome of checking one citation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuditResult {
    /// What the check established.
    pub audit: Audit,
    /// The corpus selected for comparison, when one was selected.
    pub corpus: Option<CorpusId>,
    /// A human-readable explanation; empty for a hit.
    pub detail: String,
}

/// Check one citation against `corpora`.
///
/// The checks run in a fixed order and the first failure decides the result:
/// a missing quotation, a missing name or number, an unmatched instrument
/// name, the version, the article number, the quotation text, the hash and the
/// jurisdiction. Matching the name does not pick a corpus by guess: when
/// several candidates remain the result is [`Audit::Ambiguous`].
///
/// Quotation comparison removes every Unicode whitespace character from both
/// sides and then compares the remaining characters; punctuation, digits and
/// letters must match exactly. A missing hash is not a failure, but it also
/// fixes nothing: the caller should report it as unfixed.
pub fn audit(corpora: &[Corpus], citation: &Citation<'_>) -> AuditResult {
    if citation.quote.trim().is_empty() {
        return result(Audit::NoQuote, None, "没有引文原文");
    }
    if citation.text.trim().is_empty() || citation.locator.trim().is_empty() {
        return result(Audit::InvalidSource, None, "来源缺少法名或条号");
    }

    let candidates: Vec<&Corpus> = corpora
        .iter()
        .filter(|corpus| corpus.matches_name(citation.text))
        .collect();
    if candidates.is_empty() {
        return result(Audit::NoCorpus, None, "未找到语料");
    }
    let available = candidate_ids(&candidates);

    let mut selected = candidates;
    if !citation.version.is_empty() {
        selected.retain(|corpus| corpus.version == citation.version);
        if selected.is_empty() {
            return result(
                Audit::VersionMismatch,
                None,
                format!("版本不符：来源 {}，语料 {available}", citation.version),
            );
        }
    }
    if selected.len() > 1 {
        return result(
            Audit::Ambiguous,
            None,
            format!("同名语料有多个候选（{available}），无法唯一确定"),
        );
    }
    let corpus = selected[0];
    let id = Some(CorpusId {
        law: corpus.law.clone(),
        version: corpus.version.clone(),
    });

    let Some(article) = corpus.article(citation.locator) else {
        return result(Audit::NoArticle, id, "语料中没有该条号");
    };
    if strip_whitespace(citation.quote) != strip_whitespace(&article.text) {
        return result(Audit::Mismatch, id, "引文与条文不一致");
    }
    if !citation.hash.is_empty() {
        if !is_sha256(citation.hash) {
            return result(
                Audit::HashMismatch,
                id,
                "哈希格式无效：应为 sha256: 加 64 位小写十六进制",
            );
        }
        let actual = format!(
            "sha256:{}",
            hex::encode(&Sha256::digest(article.text.as_bytes()))
        );
        if actual != citation.hash {
            return result(Audit::HashMismatch, id, "引文哈希不符");
        }
    }
    if !citation.jurisdiction.is_empty() && citation.jurisdiction != corpus.jurisdiction {
        return result(
            Audit::JurisdictionMismatch,
            id,
            format!(
                "管辖不符：来源 {}，语料 {}",
                citation.jurisdiction, corpus.jurisdiction
            ),
        );
    }
    result(Audit::Hit, id, String::new())
}

fn result(audit: Audit, corpus: Option<CorpusId>, detail: impl Into<String>) -> AuditResult {
    AuditResult {
        audit,
        corpus,
        detail: detail.into(),
    }
}

/// The candidates as `law@version`, sorted so a failure message is stable.
fn candidate_ids(corpora: &[&Corpus]) -> String {
    let mut ids: Vec<String> = corpora
        .iter()
        .map(|corpus| format!("{}@{}", corpus.law, corpus.version))
        .collect();
    ids.sort();
    ids.join("、")
}

/// Trim and collapse every run of whitespace to one space.
fn normalize_space(value: &str) -> String {
    value.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Remove every Unicode whitespace character.
fn strip_whitespace(value: &str) -> String {
    value
        .chars()
        .filter(|character| !character.is_whitespace())
        .collect()
}

/// Is this `sha256:` followed by exactly 64 lowercase hex digits?
fn is_sha256(value: &str) -> bool {
    let Some(digest) = value.strip_prefix("sha256:") else {
        return false;
    };
    digest.len() == 64
        && digest
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
