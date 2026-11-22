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
//! calendar dates, a well-formed `sha256:` value, a non-empty article list,
//! unique article numbers and, when present, a coverage ledger. The ledger has
//! exactly one entry per article in corpus order; each entry is `formalized`,
//! `partial`, `indexed` or `needs_ontology`, with rules only for the first two,
//! a note required for `partial` (and allowed on any status) and a named gap
//! for `needs_ontology`. Gap keys must be used by at least one article, and a
//! rule name may appear under only one article. A broken corpus is an error, never a skipped file.
//!
//! The audit reads exactly the fields of a rule's `source` that bear on the
//! quotation: the instrument name, the article number, the version, the quoted
//! wording, the hash and the jurisdiction.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use serde::de::{Error as _, MapAccess, Visitor};
use serde::{Deserialize, Deserializer};
use sha2::{Digest, Sha256};

use crate::{date, hex};

/// The corpus format version this crate understands.
pub const CORPUS_FORMAT: u32 = 2;

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
    /// `sha256:` followed by 64 lowercase hex digits. Recorded provenance
    /// only: neither parsing nor the audit recomputes or verifies it.
    #[serde(default)]
    pub text_sha256: Option<String>,
    /// Free-form note, for example how a correction was recorded in the
    /// corpus. Never used for matching.
    #[serde(default)]
    pub notes: Option<String>,
    /// Declared v2 coverage ledger of this corpus. It is a statement, not a
    /// check: the audit and `:packs` print it but do not compare it with the
    /// rules in an environment.
    #[serde(default)]
    pub coverage: Option<Coverage>,
    /// The articles, in the order the corpus lists them.
    pub articles: Vec<Article>,
}

/// A corpus's declared coverage.
///
/// The ledger has one [`ArticleCoverage`] per article, in corpus order. Its
/// counts are declarations, not a check: the audit and `:packs` print them but
/// do not compare them with the rules in an environment.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Coverage {
    /// Concepts that need a human reading; may be empty.
    pub open_concepts: Vec<String>,
    /// Free-form explanation of the coverage counts and semantics.
    #[serde(default)]
    pub notes: Option<String>,
    /// Named ontology gaps. Every key must be used by a `needs_ontology`
    /// article, and every `needs_ontology` article must name an existing key.
    #[serde(deserialize_with = "deserialize_gaps")]
    pub gaps: BTreeMap<String, String>,
    /// One ledger entry per corpus article, in the same order.
    pub articles: Vec<ArticleCoverage>,
}

/// How much of one article is covered by rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CoverageStatus {
    /// At least one core operative sentence is written as a rule.
    Formalized,
    /// Rules cover some sentences; a substantive clause remains open.
    Partial,
    /// The article is indexed only, with no formalization claim.
    Indexed,
    /// A named ontology is missing; this is not an omission.
    NeedsOntology,
}

/// One article's entry in the coverage ledger.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArticleCoverage {
    /// Article number, matching the corpus article at the same position.
    pub number: String,
    /// Coverage status.
    pub status: CoverageStatus,
    /// Rules formalising this article. Required and non-empty for
    /// `formalized` and `partial`; forbidden for the other two statuses.
    #[serde(default)]
    pub rules: Vec<String>,
    /// Substantive clause left unmodelled. Required for `partial`.
    #[serde(default)]
    pub note: Option<String>,
    /// Named ontology gap. Required for `needs_ontology`.
    #[serde(default)]
    pub gap: Option<String>,
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
        if let Some(coverage) = &self.coverage {
            coverage.validate(&self.articles)?;
        }
        Ok(())
    }
}

impl Coverage {
    /// Validate the ledger against the corpus articles.
    ///
    /// The ledger must match the article list one-to-one and in order, every
    /// status must carry exactly the fields it allows, every gap key must be
    /// used, and a rule may belong to only one article.
    fn validate(&self, articles: &[Article]) -> Result<(), String> {
        if self.articles.len() != articles.len() {
            return Err(format!(
                "coverage.articles 有 {} 条，articles 有 {} 条；必须一一对应",
                self.articles.len(),
                articles.len()
            ));
        }
        let mut seen = BTreeSet::new();
        for (index, (entry, article)) in self.articles.iter().zip(articles).enumerate() {
            let field = format!("coverage.articles[{index}].number");
            require_text(&field, &entry.number)?;
            require_unpadded(&field, &entry.number)?;
            let normalized = normalize_space(&entry.number);
            if !seen.insert(normalized.clone()) {
                return Err(format!("coverage.articles 条号 `{}` 重复", entry.number));
            }
            if normalized != normalize_space(&article.number) {
                return Err(format!(
                    "coverage.articles[{index}] 条号 `{}` 与 articles[{index}] 条号 `{}` 不符；必须一一对应且顺序一致",
                    entry.number, article.number
                ));
            }
        }

        let mut formalized = 0;
        for (index, entry) in self.articles.iter().enumerate() {
            let field = format!("coverage.articles[{index}]");
            if let Some(note) = &entry.note {
                require_text(&format!("{field}.note"), note)?;
            }
            match entry.status {
                CoverageStatus::Formalized => {
                    formalized += 1;
                    require_rules(&field, &entry.rules)?;
                    if entry.gap.is_some() {
                        return Err(format!("{field} 是 formalized，不能声明 gap"));
                    }
                }
                CoverageStatus::Partial => {
                    require_rules(&field, &entry.rules)?;
                    if entry.gap.is_some() {
                        return Err(format!("{field} 是 partial，不能声明 gap"));
                    }
                    let note = entry
                        .note
                        .as_deref()
                        .ok_or_else(|| format!("{field} 是 partial，必须声明非空 note"))?;
                    require_text(&format!("{field}.note"), note)?;
                }
                CoverageStatus::Indexed => {
                    if !entry.rules.is_empty() {
                        return Err(format!("{field} 是 indexed，不能声明 rules"));
                    }
                    if entry.gap.is_some() {
                        return Err(format!("{field} 是 indexed，不能声明 gap"));
                    }
                }
                CoverageStatus::NeedsOntology => {
                    if !entry.rules.is_empty() {
                        return Err(format!("{field} 是 needs_ontology，不能声明 rules"));
                    }
                    let gap = entry
                        .gap
                        .as_deref()
                        .ok_or_else(|| format!("{field} 是 needs_ontology，必须声明非空 gap"))?;
                    require_text(&format!("{field}.gap"), gap)?;
                    if !self.gaps.contains_key(gap) {
                        return Err(format!("{field} 引用了未定义的 gap `{gap}`"));
                    }
                }
            }
        }
        if formalized == 0 {
            return Err("coverage.articles 至少要有一条 formalized".to_owned());
        }

        let mut rules: BTreeMap<&str, &str> = BTreeMap::new();
        for entry in &self.articles {
            for rule in &entry.rules {
                require_text("coverage.articles.rules", rule)?;
                require_unpadded("coverage.articles.rules", rule)?;
                if let Some(first) = rules.insert(rule.as_str(), entry.number.as_str()) {
                    return Err(format!(
                        "规则 `{rule}` 同时被 `{first}` 和 `{}` 引用；一条规则只能引用一个条号",
                        entry.number
                    ));
                }
            }
        }

        let mut used_gaps = BTreeSet::new();
        for (gap, description) in &self.gaps {
            require_text("coverage.gaps 的键", gap)?;
            require_unpadded("coverage.gaps 的键", gap)?;
            require_text(&format!("coverage.gaps.{gap}"), description)?;
        }
        for entry in &self.articles {
            if entry.status == CoverageStatus::NeedsOntology {
                if let Some(gap) = &entry.gap {
                    used_gaps.insert(gap.as_str());
                }
            }
        }
        for gap in self.gaps.keys() {
            if !used_gaps.contains(gap.as_str()) {
                return Err(format!(
                    "coverage.gaps 中的 `{gap}` 没有被任何 needs_ontology 条文引用"
                ));
            }
        }

        let mut concepts = BTreeSet::new();
        for (index, concept) in self.open_concepts.iter().enumerate() {
            require_text(&format!("coverage.open_concepts[{index}]"), concept)?;
            require_unpadded(&format!("coverage.open_concepts[{index}]"), concept)?;
            let normalized = normalize_space(concept);
            if !concepts.insert(normalized) {
                return Err(format!("coverage.open_concepts 概念 `{concept}` 重复"));
            }
        }
        Ok(())
    }

    /// How many articles have `status` in the ledger.
    pub fn count(&self, status: CoverageStatus) -> usize {
        self.articles
            .iter()
            .filter(|entry| entry.status == status)
            .count()
    }

    /// The article numbers with `status`, in ledger order.
    pub fn numbers(&self, status: CoverageStatus) -> Vec<&str> {
        self.articles
            .iter()
            .filter(|entry| entry.status == status)
            .map(|entry| entry.number.as_str())
            .collect()
    }

    /// How many `needs_ontology` articles name each gap, ordered by descending
    /// count and then by gap code, so the display is stable.
    pub fn gap_counts(&self) -> Vec<(&str, usize)> {
        let mut counts: BTreeMap<&str, usize> =
            self.gaps.keys().map(|gap| (gap.as_str(), 0)).collect();
        for entry in &self.articles {
            if let Some(gap) = &entry.gap {
                *counts.entry(gap.as_str()).or_insert(0) += 1;
            }
        }
        let mut rows: Vec<(&str, usize)> = counts.into_iter().collect();
        rows.sort_by(|left, right| right.1.cmp(&left.1).then_with(|| left.0.cmp(right.0)));
        rows
    }
}

/// Require a non-empty rule list for `formalized` and `partial`.
fn require_rules(field: &str, rules: &[String]) -> Result<(), String> {
    if rules.is_empty() {
        Err(format!("{field} 必须有非空 rules"))
    } else {
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
    if value.trim().is_empty()
        || !value
            .chars()
            .any(|character| !character.is_whitespace() && !is_invisible_format(character))
    {
        Err(format!("{field} 不能为空"))
    } else {
        Ok(())
    }
}

/// Deserialize the `gaps` object while rejecting duplicate keys.
///
/// A plain `BTreeMap` would keep the last value and silently hide the duplicate;
/// a strict corpus format must report it instead.
fn deserialize_gaps<'de, D>(deserializer: D) -> Result<BTreeMap<String, String>, D::Error>
where
    D: Deserializer<'de>,
{
    struct GapsVisitor;

    impl<'de> Visitor<'de> for GapsVisitor {
        type Value = BTreeMap<String, String>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("以字符串为键和值的对象")
        }

        fn visit_map<M>(self, mut map: M) -> Result<Self::Value, M::Error>
        where
            M: MapAccess<'de>,
        {
            let mut gaps = BTreeMap::new();
            while let Some((key, value)) = map.next_entry::<String, String>()? {
                if gaps.insert(key.clone(), value).is_some() {
                    return Err(M::Error::custom(format!("coverage.gaps 键 `{key}` 重复")));
                }
            }
            Ok(gaps)
        }
    }

    deserializer.deserialize_map(GapsVisitor)
}

/// Characters that occupy no visible space but are not `char::is_whitespace`.
///
/// A note made only of these characters is empty for a human reader even though
/// `trim()` leaves it non-empty.
fn is_invisible_format(character: char) -> bool {
    character.is_control()
        || matches!(
            character,
            '\u{00AD}'
                | '\u{061C}'
                | '\u{180E}'
                | '\u{200B}'..='\u{200F}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202A}'..='\u{202E}'
                | '\u{2060}'..='\u{206F}'
                | '\u{FE00}'..='\u{FE0F}'
                | '\u{FEFF}'
                | '\u{FFF9}'..='\u{FFFB}'
        )
}

/// Reject leading or trailing whitespace instead of silently trimming it.
///
/// A declaration is shown as written; trimming it would change what the corpus
/// claims without reporting the error.
fn require_unpadded(field: &str, value: &str) -> Result<(), String> {
    if value.trim() != value {
        Err(format!("{field} 不能有首尾空白"))
    } else {
        Ok(())
    }
}

/// Scan `root` for corpora laid out as `<law-id>/<version>.json`.
///
/// The layout is strict: the root may contain only law directories, each law
/// directory may contain only regular `<version>.json` files, the directory
/// name must equal the corpus's `law`, and the file stem must equal its
/// `version`. A nested directory, a non-`.json` file, a root-level file or a
/// name mismatch is reported as an error, never skipped. The only fatal
/// conditions are that `root` itself or one of its direct entries cannot be
/// read; a missing or empty corpus directory is an empty successful scan,
/// which the caller must not mistake for a passing audit.
///
/// A `(law, version)` pair may appear only once. A duplicate is reported and
/// the later file is not added, so the caller can report every error. The
/// strict layout makes this unreachable through the filesystem today, but the
/// check stays so a future loader cannot silently replace one corpus with
/// another.
pub fn scan(root: &Path) -> Result<Scan, CorpusError> {
    let entries = fs::read_dir(root).map_err(|error| {
        CorpusError::new(root.to_path_buf(), format!("无法读取语料目录：{error}"))
    })?;
    let mut errors = Vec::new();
    let mut law_dirs = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|error| {
            CorpusError::new(root.to_path_buf(), format!("无法读取目录项：{error}"))
        })?;
        let path = entry.path();
        let file_type = entry.file_type().map_err(|error| {
            CorpusError::new(path.clone(), format!("无法读取目录项类型：{error}"))
        })?;
        if !file_type.is_dir() {
            errors.push(CorpusError::new(
                path,
                "语料根目录下只能有 <law> 目录；发现布局外的文件或链接",
            ));
            continue;
        }
        let Some(name) = path
            .file_name()
            .and_then(|name| name.to_str())
            .map(str::to_owned)
        else {
            errors.push(CorpusError::new(path, "语料目录名不是有效的 UTF-8"));
            continue;
        };
        law_dirs.push((path, name));
    }
    // Directory order is platform-dependent; sort it so output is stable.
    law_dirs.sort_by(|left, right| left.0.cmp(&right.0));

    let mut corpora = Vec::new();
    let mut seen: BTreeMap<(String, String), PathBuf> = BTreeMap::new();
    for (dir, dir_name) in law_dirs {
        let (files, layout_errors) = match corpus_files(&dir) {
            Ok(found) => found,
            Err(error) => {
                errors.push(error);
                continue;
            }
        };
        let has_layout_errors = !layout_errors.is_empty();
        errors.extend(layout_errors);
        if files.is_empty() && !has_layout_errors {
            errors.push(CorpusError::new(
                dir,
                "法律目录下没有任何语料；期望 <version>.json",
            ));
            continue;
        }
        for path in files {
            match Corpus::read(&path) {
                Ok(corpus) => {
                    if corpus.law != dir_name {
                        errors.push(CorpusError::new(
                            path,
                            format!("语料 law `{}` 与目录名 `{dir_name}` 不符", corpus.law),
                        ));
                        continue;
                    }
                    let stem = path.file_stem().and_then(|stem| stem.to_str());
                    if stem != Some(corpus.version.as_str()) {
                        errors.push(CorpusError::new(
                            path,
                            format!(
                                "语料 version `{}` 与文件名主干不符；文件名必须是 `<version>.json`",
                                corpus.version
                            ),
                        ));
                        continue;
                    }
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

/// List the `.json` files directly under one law directory, reporting every
/// entry that is not a regular `<version>.json` file.
fn corpus_files(dir: &Path) -> Result<(Vec<PathBuf>, Vec<CorpusError>), CorpusError> {
    let entries = fs::read_dir(dir).map_err(|error| {
        CorpusError::new(dir.to_path_buf(), format!("无法读取语料目录：{error}"))
    })?;
    let mut files = Vec::new();
    let mut errors = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|error| {
            CorpusError::new(dir.to_path_buf(), format!("无法读取目录项：{error}"))
        })?;
        let path = entry.path();
        let file_type = entry.file_type().map_err(|error| {
            CorpusError::new(path.clone(), format!("无法读取目录项类型：{error}"))
        })?;
        if file_type.is_dir() {
            errors.push(CorpusError::new(
                path,
                "法律目录下不能有子目录；语料必须是 <law>/<version>.json",
            ));
            continue;
        }
        if !file_type.is_file() {
            errors.push(CorpusError::new(
                path,
                "法律目录下只能有普通 <version>.json 文件",
            ));
            continue;
        }
        if path.extension().and_then(|extension| extension.to_str()) != Some(CORPUS_EXTENSION) {
            errors.push(CorpusError::new(
                path,
                "法律目录下只能有 <version>.json 语料文件",
            ));
            continue;
        }
        files.push(path);
    }
    // File order is platform-dependent; sort it so output is stable.
    files.sort();
    Ok((files, errors))
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
    /// `sha256:<64 lowercase hex>` of the article text exactly as stored
    /// (UTF-8, including newlines), when recorded.
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
    /// The recorded article-text hash is malformed or does not match it.
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
    /// Whether a well-formed `hash` was actually compared with the SHA-256 of
    /// the article text. `false` when the hash is empty, malformed, or the
    /// check failed before reaching the hash step.
    pub hash_checked: bool,
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
/// fixes nothing: the caller should report it as unfixed. A recorded hash is
/// the SHA-256 of the article text exactly as stored, including newlines.
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
    let mut hash_checked = false;
    if !citation.hash.is_empty() {
        if !is_sha256(citation.hash) {
            return result(
                Audit::HashMismatch,
                id,
                "条文哈希格式无效：应为 sha256: 加 64 位小写十六进制",
            );
        }
        let actual = format!(
            "sha256:{}",
            hex::encode(&Sha256::digest(article.text.as_bytes()))
        );
        if actual != citation.hash {
            let mut checked = result(Audit::HashMismatch, id, "条文哈希不符");
            checked.hash_checked = true;
            return checked;
        }
        hash_checked = true;
    }
    if !citation.jurisdiction.is_empty() && citation.jurisdiction != corpus.jurisdiction {
        let mut checked = result(
            Audit::JurisdictionMismatch,
            id,
            format!(
                "管辖不符：来源 {}，语料 {}",
                citation.jurisdiction, corpus.jurisdiction
            ),
        );
        checked.hash_checked = hash_checked;
        return checked;
    }
    let mut checked = result(Audit::Hit, id, String::new());
    checked.hash_checked = hash_checked;
    checked
}

fn result(audit: Audit, corpus: Option<CorpusId>, detail: impl Into<String>) -> AuditResult {
    AuditResult {
        audit,
        corpus,
        hash_checked: false,
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
