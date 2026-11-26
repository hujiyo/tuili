//! Strict, versioned JSON case descriptions.
//!
//! A case description is **untrusted input**. It may bring facts (with their
//! identity and source), the time and place a fact occurred, individual
//! constants, goals and analysis assumptions — nothing else. It can never
//! declare a rule, predicate, interpretation, risk theme, priority or any other
//! legal concept: a case description does not define law.
//!
//! Every field is checked here, before the session environment is touched, and
//! every rejection names the JSON path that failed (for example
//! `facts[2].identity`). There are no defaults for required fields, no guessed
//! identities and no skipped entries: one bad entry rejects the whole file.
//!
//! The identity keywords are the kernel's [`FactIdentity`] keywords, so a JSON
//! case and a `.std` case spell evidence the same way. `verified` /
//! `stipulated` are claims exactly as they are in a `.std` case file: the
//! system records that someone asserted them, it does not verify them.
//!
//! This module only parses and validates the document; elaborating proposition
//! text against the loaded environment and inserting the declarations is the
//! session's job.

use std::collections::BTreeSet;
use std::io::Read as _;

use serde_json::{Map, Value};
use std_deduce_kernel::env::{escape_control, FactIdentity, SourceRef};
use std_deduce_lang::lexer::{lex, Tok};
use std_deduce_lang::module::escape_path;

/// The only schema version this build accepts. An unknown version is rejected
/// and the error names the supported one.
pub(crate) const SCHEMA_VERSION: u64 = 1;

/// The same file-size bound the certificate reader uses: a case description is
/// an untrusted JSON document, so it is read as bytes and checked before it is
/// parsed.
pub(crate) const MAX_CASE_JSON_BYTES: usize = 8 * 1024 * 1024;

/// JSON nesting bound, matching `serde_json`'s default recursion limit used by
/// the certificate reader. The schema itself nests only four levels deep; the
/// bound exists so a pathological document is a diagnostic instead of a stack
/// overflow.
pub(crate) const MAX_CASE_JSON_DEPTH: usize = 128;

/// Every array in the document (`facts`, `assumptions`, `goals`, `objects`,
/// `imports`) is bounded so a case cannot blow up load time silently.
pub(crate) const MAX_CASE_ENTRIES: usize = 10_000;

const TOP_LEVEL_FIELDS: &[&str] = &[
    "schema_version",
    "case",
    "imports",
    "reference",
    "facts",
    "goals",
    "assumptions",
    "objects",
];
const REFERENCE_FIELDS: &[&str] = &["as_of", "jurisdiction"];
const FACT_FIELDS: &[&str] = &[
    "proposition",
    "identity",
    "source",
    "occurred_at",
    "occurred_in",
];
const SOURCE_FIELDS: &[&str] = &[
    "text",
    "locator",
    "version",
    "effective",
    "note",
    "quote",
    "url",
    "jurisdiction",
    "retrieved_at",
    "hash",
];
const OBJECT_FIELDS: &[&str] = &["name", "type", "source"];

/// Field names that would let a case description define law.
///
/// They are not merely unknown: a document that writes one is rejected with the
/// boundary statement, never silently ignored. The list is deliberately
/// explicit so a producer gets a usable diagnostic instead of a generic
/// "unknown field".
const CONCEPT_FIELDS: &[&str] = &[
    "rule",
    "rules",
    "pred",
    "preds",
    "predicate",
    "predicates",
    "interpret",
    "interprets",
    "interpretation",
    "interpretations",
    "def",
    "defs",
    "sort",
    "sorts",
    "risk",
    "risks",
    "priority",
    "priorities",
    "contrary",
    "unique",
    "uniq",
    "open",
    "namespace",
    "decl",
    "decls",
    "declaration",
    "declarations",
    "theory",
    "axiom",
    "axioms",
];

/// A JSON validation failure: the JSON path and the message.
type Problem = (String, String);

/// One individual constant a case declares.
///
/// Individuals are the nouns a fact talks about, not legal concepts: the type
/// must be a declared sort (checked by the session), never `Prop`, `Type` or a
/// function type. A case description may not invent a sort or predicate.
#[derive(Debug, Clone)]
pub(crate) struct CaseObject {
    pub(crate) path: String,
    pub(crate) name: String,
    pub(crate) ty: String,
    pub(crate) source: Option<SourceRef>,
}

/// One asserted proposition together with who asserts it and where it comes
/// from. `occurred_at` / `occurred_in` are explicit values; an absent field
/// stays absent and is never filled from the session date.
#[derive(Debug, Clone)]
pub(crate) struct CaseFact {
    pub(crate) path: String,
    pub(crate) proposition: String,
    pub(crate) identity: FactIdentity,
    pub(crate) source: SourceRef,
    pub(crate) occurred_at: Option<String>,
    pub(crate) occurred_in: Option<String>,
}

/// One target proposition the case wants checked. Goals are type-checked at
/// load time but are not proved by loading; a query proves them.
#[derive(Debug, Clone)]
pub(crate) struct CaseGoal {
    pub(crate) path: String,
    pub(crate) proposition: String,
}

/// A validated case description.
#[derive(Debug, Clone)]
pub(crate) struct CaseFile {
    pub(crate) case: Option<String>,
    pub(crate) imports: Vec<String>,
    pub(crate) as_of: Option<String>,
    pub(crate) jurisdiction: Option<String>,
    pub(crate) objects: Vec<CaseObject>,
    pub(crate) facts: Vec<CaseFact>,
    pub(crate) assumptions: Vec<CaseFact>,
    pub(crate) goals: Vec<CaseGoal>,
}

impl CaseFile {
    /// The identities the document actually declared, for the load summary.
    pub(crate) fn identity_counts(&self) -> Vec<(FactIdentity, usize)> {
        let mut counts: Vec<(FactIdentity, usize)> = Vec::new();
        for fact in self.facts.iter().chain(self.assumptions.iter()) {
            match counts
                .iter_mut()
                .find(|(identity, _)| *identity == fact.identity)
            {
                Some((_, count)) => *count += 1,
                None => counts.push((fact.identity, 1)),
            }
        }
        counts
    }
}

/// Read and validate one case description.
///
/// The returned error is already rendered as
/// `<path>:<JSON 路径>: error: <message>` (or `<path>:$: error: ...` for a
/// whole-document failure such as a bad byte size or malformed JSON).
pub(crate) fn read(path: &str) -> Result<CaseFile, String> {
    // Read at most one byte past the limit, so a huge untrusted file cannot be
    // pulled into memory merely to reject it. The post-read check also rejects
    // a file that was smaller when opened and grew while it was read.
    let file = std::fs::File::open(path)
        .map_err(|error| render(path, "$", format!("读取失败：{error}")))?;
    let mut bytes = Vec::new();
    file.take((MAX_CASE_JSON_BYTES as u64) + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| render(path, "$", format!("读取失败：{error}")))?;
    if bytes.len() > MAX_CASE_JSON_BYTES {
        return Err(render(
            path,
            "$",
            format!("案件 JSON 超过 {MAX_CASE_JSON_BYTES} 字节上限"),
        ));
    }
    let text = String::from_utf8(bytes)
        .map_err(|error| render(path, "$", format!("案件 JSON 不是有效 UTF-8：{error}")))?;
    check_depth(&text).map_err(|(line, col, depth)| {
        render(
            path,
            "$",
            format!(
                "JSON 嵌套深度超过上限 {MAX_CASE_JSON_DEPTH} 层：第 {line} 行第 {col} 列达到至少 {depth} 层"
            ),
        )
    })?;
    let value: Value = serde_json::from_str(&text).map_err(|error| {
        render(
            path,
            "$",
            format!(
                "JSON 解析失败（第 {} 行第 {} 列）：{error}",
                error.line(),
                error.column()
            ),
        )
    })?;
    parse_value(&value).map_err(|(json_path, message)| render(path, &json_path, message))
}

/// Render one case diagnostic: `file:JSON 路径: error: message`.
///
/// The path components include user text (object names, unknown field names),
/// so both components are escaped before they reach a terminal or a log.
pub(crate) fn render(path: &str, json_path: &str, message: impl std::fmt::Display) -> String {
    format!(
        "{}:{}: error: {}",
        escape_path(path),
        escape_control(json_path),
        message
    )
}

/// A path relative to the document root (`$`).
fn join(parent: &str, key: &str) -> String {
    if parent == "$" {
        key.to_owned()
    } else {
        format!("{parent}.{key}")
    }
}

fn at_index(parent: &str, index: usize) -> String {
    format!("{parent}[{index}]")
}

fn problem<T>(path: impl Into<String>, message: impl Into<String>) -> Result<T, Problem> {
    Err((path.into(), message.into()))
}

fn kind(value: &Value) -> &'static str {
    match value {
        Value::Null => "null",
        Value::Bool(_) => "布尔",
        Value::Number(_) => "数字",
        Value::String(_) => "字符串",
        Value::Array(_) => "数组",
        Value::Object(_) => "对象",
    }
}

fn as_object<'a>(value: &'a Value, path: &str) -> Result<&'a Map<String, Value>, Problem> {
    value.as_object().ok_or_else(|| {
        (
            path.to_owned(),
            format!("必须是 JSON 对象，实际是 {}", kind(value)),
        )
    })
}

fn as_array<'a>(value: &'a Value, path: &str) -> Result<&'a [Value], Problem> {
    let items = value.as_array().ok_or_else(|| {
        (
            path.to_owned(),
            format!("必须是 JSON 数组，实际是 {}", kind(value)),
        )
    })?;
    if items.len() > MAX_CASE_ENTRIES {
        return problem(
            path,
            format!("数组超过上限 {MAX_CASE_ENTRIES}：实际 {} 个", items.len()),
        );
    }
    Ok(items)
}

fn as_string<'a>(value: &'a Value, path: &str) -> Result<&'a str, Problem> {
    value.as_str().ok_or_else(|| {
        (
            path.to_owned(),
            format!("必须是字符串，实际是 {}", kind(value)),
        )
    })
}

fn non_blank<'a>(value: &'a str, path: &str) -> Result<&'a str, Problem> {
    if value.trim().is_empty() {
        return problem(path, "不能为空：空字符串或纯空白都不接受");
    }
    Ok(value)
}

fn required_field<'a>(
    map: &'a Map<String, Value>,
    key: &str,
    parent: &str,
) -> Result<&'a Value, Problem> {
    map.get(key)
        .ok_or_else(|| (join(parent, key), format!("缺少必填字段 `{key}`")))
}

fn required_string<'a>(
    map: &'a Map<String, Value>,
    key: &str,
    parent: &str,
) -> Result<&'a str, Problem> {
    let value = required_field(map, key, parent)?;
    as_string(value, &join(parent, key))
}

fn optional_string(
    map: &Map<String, Value>,
    key: &str,
    parent: &str,
) -> Result<Option<String>, Problem> {
    match map.get(key) {
        None => Ok(None),
        Some(value) => {
            let path = join(parent, key);
            let text = as_string(value, &path)?;
            Ok(Some(non_blank(text, &path)?.to_owned()))
        }
    }
}

fn check_fields(map: &Map<String, Value>, allowed: &[&str], parent: &str) -> Result<(), Problem> {
    for key in map.keys() {
        if allowed.contains(&key.as_str()) {
            continue;
        }
        let path = join(parent, key);
        if CONCEPT_FIELDS.contains(&key.as_str()) {
            return problem(
                path,
                format!(
                    "案件描述不能定义法律：字段 `{key}` 不允许出现。\
                     这份 JSON 只能带来事实、身份、来源、时间地点与目标，\
                     不能声明规则、谓词、解释、风险或优先级"
                ),
            );
        }
        let allowed = allowed
            .iter()
            .map(|field| format!("`{field}`"))
            .collect::<Vec<_>>()
            .join("、");
        return problem(path, format!("未知字段 `{key}`；允许的字段是 {allowed}"));
    }
    Ok(())
}

/// Validate the document-level nesting depth without trusting `serde_json`'s
/// recursive parser for the bound.
///
/// Braces inside string literals do not count, and a backslash escapes the next
/// character inside a string. An unbalanced document is left to the JSON parser;
/// this only answers "how deep did it get".
fn check_depth(text: &str) -> Result<(), (usize, usize, usize)> {
    let mut depth = 0usize;
    let mut line = 1usize;
    let mut column = 1usize;
    let mut in_string = false;
    let mut escaped = false;
    for ch in text.chars() {
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
        } else {
            match ch {
                '"' => in_string = true,
                '{' | '[' => {
                    depth += 1;
                    if depth > MAX_CASE_JSON_DEPTH {
                        return Err((line, column, depth));
                    }
                }
                '}' | ']' => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
        if ch == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    Ok(())
}

fn parse_value(value: &Value) -> Result<CaseFile, Problem> {
    let map = as_object(value, "$")?;
    check_fields(map, TOP_LEVEL_FIELDS, "$")?;

    let version = match map.get("schema_version") {
        None => {
            return problem(
                "schema_version",
                "缺少必填字段；当前支持的 schema_version 是 1",
            )
        }
        Some(Value::Number(number)) => number.as_u64(),
        Some(other) => {
            return problem(
                "schema_version",
                format!("schema_version 必须是整数 1，实际是{}", kind(other)),
            )
        }
    };
    match version {
        Some(SCHEMA_VERSION) => {}
        Some(other) => {
            return problem(
                "schema_version",
                format!("不支持的 schema_version {other}；当前只支持 1"),
            )
        }
        None => {
            return problem(
                "schema_version",
                "schema_version 必须是整数 1（不接受小数或字符串）",
            )
        }
    }

    let case = optional_string(map, "case", "$")?;

    let imports = {
        let value = required_field(map, "imports", "$")?;
        let mut imports = string_array(value, "imports", validate_package_name)?;
        // A repeated import is harmless, like a repeated `import` line in a
        // `.std` file; the report and the registry pass see it once.
        let mut seen = BTreeSet::new();
        imports.retain(|name| seen.insert(name.clone()));
        imports
    };

    let mut as_of = None;
    let mut jurisdiction = None;
    if let Some(value) = map.get("reference") {
        let reference = as_object(value, "reference")?;
        check_fields(reference, REFERENCE_FIELDS, "reference")?;
        if reference.is_empty() {
            return problem(
                "reference",
                "reference 至少要写 as_of 或 jurisdiction 之一；空对象不表示任何值",
            );
        }
        if let Some(date) = optional_string(reference, "as_of", "reference")? {
            std_deduce_kernel::meta::validate_date("reference.as_of", &date)
                .map_err(|error| ("reference.as_of".to_owned(), error))?;
            as_of = Some(date);
        }
        if let Some(code) = optional_string(reference, "jurisdiction", "reference")? {
            std_deduce_kernel::meta::validate_jurisdiction_code("reference.jurisdiction", &code)
                .map_err(|error| ("reference.jurisdiction".to_owned(), error))?;
            jurisdiction = Some(code);
        }
    }

    let facts_value = required_field(map, "facts", "$")?;
    let facts = parse_facts(facts_value, "facts", false)?;
    let assumptions = match map.get("assumptions") {
        Some(value) => parse_facts(value, "assumptions", true)?,
        None => Vec::new(),
    };
    let objects = match map.get("objects") {
        Some(value) => parse_objects(value)?,
        None => Vec::new(),
    };
    let goals = match map.get("goals") {
        Some(value) => {
            let items = string_array(value, "goals", |_, _| Ok(()))?;
            items
                .into_iter()
                .enumerate()
                .map(|(index, proposition)| CaseGoal {
                    path: at_index("goals", index),
                    proposition,
                })
                .collect()
        }
        None => Vec::new(),
    };

    Ok(CaseFile {
        case,
        imports,
        as_of,
        jurisdiction,
        objects,
        facts,
        assumptions,
        goals,
    })
}

fn string_array<F>(value: &Value, path: &str, mut validate: F) -> Result<Vec<String>, Problem>
where
    F: FnMut(&str, &str) -> Result<(), Problem>,
{
    let items = as_array(value, path)?;
    let mut out = Vec::with_capacity(items.len());
    for (index, item) in items.iter().enumerate() {
        let item_path = at_index(path, index);
        let text = as_string(item, &item_path)?;
        let text = non_blank(text, &item_path)?;
        validate(text, &item_path)?;
        out.push(text.to_owned());
    }
    Ok(out)
}

fn parse_facts(value: &Value, section: &str, assumption: bool) -> Result<Vec<CaseFact>, Problem> {
    let items = as_array(value, section)?;
    let mut facts = Vec::with_capacity(items.len());
    for (index, item) in items.iter().enumerate() {
        facts.push(parse_fact(item, &at_index(section, index), assumption)?);
    }
    Ok(facts)
}

fn parse_fact(value: &Value, path: &str, assumption: bool) -> Result<CaseFact, Problem> {
    let map = as_object(value, path)?;
    check_fields(map, FACT_FIELDS, path)?;

    let proposition = non_blank(
        required_string(map, "proposition", path)?,
        &join(path, "proposition"),
    )?
    .to_owned();
    let identity_text = required_string(map, "identity", path)?;
    let identity = FactIdentity::from_keyword(identity_text).ok_or_else(|| {
        (
            join(path, "identity"),
            format!(
                "`{identity_text}` 不是合法身份；只能是 verified / user_asserted / \
                 assumed / disputed / stipulated"
            ),
        )
    })?;
    if assumption && identity != FactIdentity::Assumed {
        // The section and the identity must agree: an analysis assumption is
        // not a court finding, an agreement between the parties or a party's
        // claim, and those belong in `facts` where their evidence is stated.
        let reason = match identity {
            FactIdentity::Verified => "分析假设不能声称法院查明",
            FactIdentity::Stipulated => "分析假设不能声称双方无争议",
            FactIdentity::UserAsserted => "分析假设不能用用户陈述表示；用户陈述请写在 facts 里",
            FactIdentity::Disputed => "分析假设不能用对方争议表示；争议事实请写在 facts 里",
            FactIdentity::Assumed => "分析假设的身份必须显式写 assumed",
        };
        return problem(
            join(path, "identity"),
            format!("{reason}（assumptions 的 identity 只能显式写 assumed）"),
        );
    }
    let source_value = required_field(map, "source", path)?;
    let source = parse_source(source_value, &join(path, "source"))?;

    let occurred_at = optional_string(map, "occurred_at", path)?;
    if let Some(date) = &occurred_at {
        std_deduce_kernel::meta::validate_date(&join(path, "occurred_at"), date)
            .map_err(|error| (join(path, "occurred_at"), error))?;
    }
    let occurred_in = optional_string(map, "occurred_in", path)?;
    if let Some(code) = &occurred_in {
        std_deduce_kernel::meta::validate_jurisdiction_code(&join(path, "occurred_in"), code)
            .map_err(|error| (join(path, "occurred_in"), error))?;
    }

    Ok(CaseFact {
        path: path.to_owned(),
        proposition,
        identity,
        source,
        occurred_at,
        occurred_in,
    })
}

fn parse_source(value: &Value, path: &str) -> Result<SourceRef, Problem> {
    let map = as_object(value, path)?;
    check_fields(map, SOURCE_FIELDS, path)?;
    let text = non_blank(required_string(map, "text", path)?, &join(path, "text"))?.to_owned();
    let locator = non_blank(
        required_string(map, "locator", path)?,
        &join(path, "locator"),
    )?
    .to_owned();
    let mut source = SourceRef::new(text, locator);
    source.version = optional_string(map, "version", path)?.unwrap_or_default();
    source.effective = optional_string(map, "effective", path)?;
    if let Some(date) = &source.effective {
        std_deduce_kernel::meta::validate_date(&join(path, "effective"), date)
            .map_err(|error| (join(path, "effective"), error))?;
    }
    source.note = optional_string(map, "note", path)?.unwrap_or_default();
    source.quote = optional_string(map, "quote", path)?.unwrap_or_default();
    source.url = optional_string(map, "url", path)?.unwrap_or_default();
    source.jurisdiction = optional_string(map, "jurisdiction", path)?.unwrap_or_default();
    if !source.jurisdiction.is_empty() {
        std_deduce_kernel::meta::validate_jurisdiction_code(
            &join(path, "jurisdiction"),
            &source.jurisdiction,
        )
        .map_err(|error| (join(path, "jurisdiction"), error))?;
    }
    source.retrieved_at = optional_string(map, "retrieved_at", path)?.unwrap_or_default();
    source.hash = optional_string(map, "hash", path)?.unwrap_or_default();
    Ok(source)
}

fn parse_objects(value: &Value) -> Result<Vec<CaseObject>, Problem> {
    let items = as_array(value, "objects")?;
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut objects = Vec::with_capacity(items.len());
    for (index, item) in items.iter().enumerate() {
        let path = at_index("objects", index);
        let map = as_object(item, &path)?;
        check_fields(map, OBJECT_FIELDS, &path)?;
        let name =
            non_blank(required_string(map, "name", &path)?, &join(&path, "name"))?.to_owned();
        validate_case_name(&name, &join(&path, "name"))?;
        if !seen.insert(name.clone()) {
            return problem(
                join(&path, "name"),
                format!("对象 `{name}` 重复声明；同名对象只能声明一次"),
            );
        }
        let ty = non_blank(required_string(map, "type", &path)?, &join(&path, "type"))?.to_owned();
        let source = match map.get("source") {
            Some(value) => Some(parse_source(value, &join(&path, "source"))?),
            None => None,
        };
        objects.push(CaseObject {
            path,
            name,
            ty,
            source,
        });
    }
    Ok(objects)
}

/// A package name must be one identifier token, exactly as `import` reads it.
///
/// The check rejects whitespace, a line break, a `--` comment start and any
/// other shape the `.std` grammar could not import. The registry still decides
/// whether the package exists and is loadable.
fn validate_package_name(name: &str, path: &str) -> Result<(), Problem> {
    validate_identifier(name, path, false)
}

/// A case object's name is an unqualified identifier, like an `obj` name in a
/// `.std` case file (a case file has no namespace).
fn validate_case_name(name: &str, path: &str) -> Result<(), Problem> {
    validate_identifier(name, path, true)
}

fn validate_identifier(name: &str, path: &str, unqualified: bool) -> Result<(), Problem> {
    if unqualified && name.contains('.') {
        return problem(
            path,
            "案件对象名不能带命名空间前缀；案件 JSON 没有 namespace",
        );
    }
    let tokens = lex(name).map_err(|error| (path.to_owned(), format!("不是合法名称：{error}")))?;
    let single = matches!(
        tokens.as_slice(),
        [first, last]
            if matches!(&first.tok, Tok::Ident(ident) if ident == name)
                && matches!(last.tok, Tok::Eof)
    );
    if !single {
        return problem(
            path,
            format!("`{name}` 必须是单个标识符（不能含空白、换行、标点或注释）"),
        );
    }
    Ok(())
}
