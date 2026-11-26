//! `:search` — deterministic article-text lookup over linked corpora.
//!
//! This command returns candidate provisions, never a legal conclusion. It
//! searches the `articles` text of the corpora under `<current directory>/
//! law/corpus`, reports the corpus's declared coverage ledger, and lists the
//! loaded rules whose sources cite the article. It does not understand the
//! query semantically, does not use a language model, and does not create rules.
//!
//! Matching is literal and whitespace-normalized: both the article text and the
//! keyword are trimmed and every run of Unicode whitespace is collapsed to one
//! space; the keyword is then split on spaces and every part must occur as a
//! literal substring (the parts need not be adjacent). No regular expression is
//! compiled. Filters never fall back: a version that no corpus in scope records
//! is an error, and a corpus without a recorded jurisdiction is reported as
//! "管辖未记录" instead of being treated as a match.

use std::collections::BTreeSet;
use std::io::Write;
use std::path::Path;

use std_deduce_kernel::env::{escape_control, DeclKind, Env};
use std_deduce_lawpack::corpus::{self, article_hash, Article, Corpus, CoverageStatus};
use std_deduce_lawpack::Trust;

use crate::packs::LoadedPackInfo;
use crate::Outcome;

/// Default number of results printed when `--limit` is not given.
pub(crate) const SEARCH_LIMIT_DEFAULT: usize = 20;

/// Hard upper bound for `--limit`. A bigger request is a usage error, never a
/// silently truncated result.
pub(crate) const SEARCH_LIMIT_MAX: usize = 64;

/// Context characters kept on each side of a match in the printed snippet.
const SNIPPET_CONTEXT: usize = 12;

/// Maximum characters of an article shown when no keyword was given.
const SNIPPET_WHOLE: usize = 60;

pub(crate) fn search(
    arg: &str,
    env: &Env,
    packs: &[LoadedPackInfo],
    out: &mut impl Write,
) -> Result<Outcome, String> {
    let mut options = Options::parse(arg)?;
    let terms = keyword_terms(&options.keyword);
    let root = crate::corpus_root("")?;
    let scan =
        corpus::scan_for_search(&root).map_err(|error| escape_control(&error.to_string()))?;
    let all_ids: Vec<String> = scan
        .corpora
        .iter()
        .map(|loaded| format!("{}@{}", loaded.corpus.law, loaded.corpus.version))
        .collect();
    let all_corpora: Vec<&Corpus> = scan.corpora.iter().map(|loaded| &loaded.corpus).collect();
    if !scan.errors.is_empty() {
        for error in &scan.errors {
            writeln!(out, "{}", escape_control(&error.to_string())).ok();
        }
        return Err(format!("{} 个语料错误，未进行检索", scan.errors.len()));
    }
    if scan.corpora.is_empty() {
        writeln!(
            out,
            "语料目录中没有语料：{}",
            crate::escape_display_path(&root)
        )
        .ok();
        return Ok(Outcome::Gap);
    }

    let mut scoped: Vec<&Corpus> = all_corpora.clone();
    write_header(out, &options, &terms, &root);
    if let Some(law) = &options.law {
        let before = scoped.len();
        scoped.retain(|corpus| law_matches(corpus, law));
        if scoped.is_empty() {
            return Err(format!(
                "没有该法名的语料：`{}`（语料：{}）",
                escape_control(law),
                available_ids(&all_ids)
            ));
        }
        writeln!(
            out,
            "法名过滤：`{}` 保留 {}/{} 个语料",
            escape_control(law),
            scoped.len(),
            before
        )
        .ok();
    }
    if let Some(version) = &options.version {
        let candidates: Vec<&Corpus> = scoped
            .iter()
            .copied()
            .filter(|corpus| corpus.version == *version)
            .collect();
        if candidates.is_empty() {
            let versions: Vec<&str> = scoped
                .iter()
                .map(|corpus| corpus.version.as_str())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            return Err(format!(
                "没有该版本的语料：`{}`（现有版本：{}）",
                escape_control(version),
                if versions.is_empty() {
                    "（无）".to_owned()
                } else {
                    versions
                        .iter()
                        .map(|value| format!("`{}`", escape_control(value)))
                        .collect::<Vec<_>>()
                        .join("、")
                }
            ));
        }
        writeln!(
            out,
            "版本过滤：`{}` 保留 {} 个语料",
            escape_control(version),
            candidates.len()
        )
        .ok();
        scoped = candidates;
    }

    // Check the article before the jurisdiction filter: an article that exists
    // only in a corpus whose jurisdiction is unrecorded is "excluded by the
    // filter", not "the article does not exist". The literal form is tried
    // first, so a corpus that stores `39` stays directly addressable; only when
    // it has no such number is `第三十九条` tried.
    if let Some(raw) = options.article.clone() {
        let (chosen, also_present) = resolve_article(&scoped, &raw)?;
        if let Some(also_present) = also_present {
            writeln!(
                out,
                "注：条号同时存在字面 `{}` 与 `{}`，按字面 `{}` 匹配。",
                escape_control(&raw),
                escape_control(&also_present),
                escape_control(&raw)
            )
            .ok();
        }
        writeln!(out, "条号过滤：`{}`", escape_control(&chosen)).ok();
        options.article = Some(chosen);
    }

    if let Some(code) = &options.jurisdiction {
        let mut retained = Vec::new();
        let mut unrecorded = Vec::new();
        let mut mismatched = 0;
        for corpus in scoped.iter().copied() {
            if corpus.jurisdiction.trim().is_empty() {
                unrecorded.push(corpus);
            } else if corpus.jurisdiction.trim() == code.trim() {
                retained.push(corpus);
            } else {
                mismatched += 1;
            }
        }
        for corpus in &unrecorded {
            writeln!(
                out,
                "注：{} 的语料没有记录管辖，已排除；如需检索该语料请去掉 --jurisdiction",
                escape_control(&format!("{}@{}", corpus.law, corpus.version))
            )
            .ok();
        }
        if retained.is_empty() && unrecorded.is_empty() {
            return Err(format!("没有管辖为 `{}` 的语料", escape_control(code)));
        }
        writeln!(
            out,
            "管辖过滤：`{}` 保留 {} 个语料（因管辖不同排除 {} 份，因管辖未记录排除 {} 份）",
            escape_control(code),
            retained.len(),
            mismatched,
            unrecorded.len()
        )
        .ok();
        scoped = retained;
    }

    let mut hits: Vec<Hit<'_>> = Vec::new();
    for corpus in scoped.iter().copied() {
        for (index, article) in corpus.articles.iter().enumerate() {
            if let Some(wanted) = &options.article {
                if !numbers_equal(&article.number, wanted) {
                    continue;
                }
            }
            if !terms.is_empty() && !terms_match(&article.text, &terms) {
                continue;
            }
            hits.push(Hit {
                corpus,
                article,
                index,
            });
        }
    }
    hits.sort_by(|left, right| {
        left.corpus
            .law
            .cmp(&right.corpus.law)
            .then_with(|| left.corpus.version.cmp(&right.corpus.version))
            .then_with(|| left.index.cmp(&right.index))
    });

    let total = hits.len();
    if total == 0 {
        writeln!(out, "没有命中的条文。").ok();
        return Ok(Outcome::Gap);
    }
    let shown = total.min(options.limit);
    writeln!(
        out,
        "命中 {total} 条：显示前 {shown} 条（--limit 上限 {SEARCH_LIMIT_MAX}）。"
    )
    .ok();
    if total > shown {
        writeln!(
            out,
            "已截断：命中 {total} 条，只显示按（法名, 版本, 条号）稳定排序后的前 {shown} 条；\
             可用 --limit 调整（上限 {SEARCH_LIMIT_MAX}）。"
        )
        .ok();
        writeln!(out).ok();
    }
    let context = SearchContext {
        env,
        packs,
        all_corpora: &all_corpora,
        terms: &terms,
    };
    let mut hash_mismatch = false;
    for hit in hits.iter().take(shown) {
        write_hit(out, hit, &options, &context, &mut hash_mismatch);
        writeln!(out).ok();
    }
    if hash_mismatch {
        Ok(Outcome::Gap)
    } else {
        Ok(Outcome::Proved)
    }
}

/// The parsed command arguments.
struct Options {
    /// The keyword exactly as typed (internal whitespace preserved) so a
    /// diagnostic can escape a newline or control character verbatim.
    keyword: String,
    law: Option<String>,
    version: Option<String>,
    article: Option<String>,
    jurisdiction: Option<String>,
    /// Never zero and never above [`SEARCH_LIMIT_MAX`]; [`Options::parse`]
    /// rejects both.
    limit: usize,
}

impl Options {
    fn parse(arg: &str) -> Result<Options, String> {
        let pieces = pieces(arg);
        let option_at = pieces.iter().position(|piece| piece.text.starts_with('-'));
        // No keyword (option_at = Some(0)) is accepted only with `--article`,
        // checked at the end of this function.
        let keyword = match option_at {
            Some(0) => String::new(),
            Some(index) => {
                let start = pieces[0].start;
                let end = pieces[index - 1].end;
                arg[start..end].to_owned()
            }
            None => match (pieces.first(), pieces.last()) {
                (Some(first), Some(last)) => arg[first.start..last.end].to_owned(),
                _ => String::new(),
            },
        };
        let mut options = Options {
            keyword,
            law: None,
            version: None,
            article: None,
            jurisdiction: None,
            limit: SEARCH_LIMIT_DEFAULT,
        };
        let mut index = option_at.unwrap_or(pieces.len());
        let mut limit_given = false;
        while index < pieces.len() {
            let name = pieces[index].text;
            if !name.starts_with("--") {
                return Err(format!(
                    "`{}` 不是选项；关键词必须写在选项之前",
                    escape_control(name)
                ));
            }
            let value = pieces
                .get(index + 1)
                .ok_or_else(|| format!("选项 `{}` 缺少值", escape_control(name)))?;
            if value.text.starts_with('-') {
                return Err(format!(
                    "选项 `{}` 缺少值（`{}` 看起来是另一个选项）",
                    escape_control(name),
                    escape_control(value.text)
                ));
            }
            match name {
                "--law" => set_once("--law", &mut options.law, value.text)?,
                "--version" => set_once("--version", &mut options.version, value.text)?,
                "--article" => {
                    let literal = normalize_space(value.text);
                    if let Some(Err(error)) = numeric_article(value.text) {
                        return Err(error);
                    }
                    set_once("--article", &mut options.article, &literal)?
                }
                "--jurisdiction" => {
                    set_once("--jurisdiction", &mut options.jurisdiction, value.text)?
                }
                "--limit" => {
                    if limit_given {
                        return Err("选项 `--limit` 重复；每个选项只能给出一次".to_owned());
                    }
                    limit_given = true;
                    options.limit = parse_limit(value.text)?;
                }
                other => {
                    return Err(format!(
                    "未知选项 `{}`；可用：--law / --version / --article / --jurisdiction / --limit",
                    escape_control(other)
                ))
                }
            }
            index += 2;
        }
        if options.keyword.trim().is_empty() && options.article.is_none() {
            return Err(
                "用法：:search <关键词> [--law <法名>] [--version <版本>] [--article <条号>] \
                 [--jurisdiction <代码>] [--limit <n>]（只有给出 --article 时可以省略关键词）"
                    .to_owned(),
            );
        }
        Ok(options)
    }
}

/// One whitespace-separated argument piece with its byte range in `arg`.
struct Piece<'a> {
    start: usize,
    end: usize,
    text: &'a str,
}

fn pieces(arg: &str) -> Vec<Piece<'_>> {
    let mut result = Vec::new();
    let mut start = None;
    for (index, character) in arg.char_indices() {
        if character.is_whitespace() {
            if let Some(from) = start.take() {
                result.push(Piece {
                    start: from,
                    end: index,
                    text: &arg[from..index],
                });
            }
        } else if start.is_none() {
            start = Some(index);
        }
    }
    if let Some(from) = start {
        result.push(Piece {
            start: from,
            end: arg.len(),
            text: &arg[from..],
        });
    }
    result
}

fn set_once(name: &str, slot: &mut Option<String>, value: &str) -> Result<(), String> {
    if slot.is_some() {
        return Err(format!(
            "选项 `{}` 重复；每个选项只能给出一次",
            escape_control(name)
        ));
    }
    *slot = Some(value.to_owned());
    Ok(())
}

fn parse_limit(value: &str) -> Result<usize, String> {
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(format!(
            "`--limit` 的值 `{}` 不是十进制整数",
            escape_control(value)
        ));
    }
    let limit: usize = value
        .parse()
        .map_err(|_| format!("`--limit` 的值 `{}` 超出可处理范围", escape_control(value)))?;
    if limit == 0 {
        return Err("`--limit` 必须大于 0".to_owned());
    }
    if limit > SEARCH_LIMIT_MAX {
        return Err(format!(
            "`--limit {limit}` 超出上限 {SEARCH_LIMIT_MAX}；请改用不超过 {SEARCH_LIMIT_MAX} 的值"
        ));
    }
    Ok(limit)
}

/// The Chinese ordinal form of an ASCII article number, if the value is one.
///
/// `39`, `第39条` and `39条` become `第三十九条`. A value outside 1–9999 is an
/// error instead of a literal article number, so `10000` never silently matches
/// a corpus that happens to store that text. Any other form returns `None` and
/// is matched literally by the caller.
fn numeric_article(value: &str) -> Option<Result<String, String>> {
    let original = normalize_space(value);
    let mut inner = original.as_str();
    if let Some(rest) = inner.strip_prefix('第') {
        inner = rest;
    }
    if let Some(rest) = inner.strip_suffix('条') {
        inner = rest;
    }
    if inner.is_empty() || !inner.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let number: u32 = match inner.parse() {
        Ok(number) => number,
        Err(_) => {
            return Some(Err(format!(
                "条号数字 `{}` 超出可处理范围（只支持 1–9999）",
                escape_control(value)
            )))
        }
    };
    if number == 0 || number > 9999 {
        return Some(Err(format!(
            "条号 `{}` 无效：只支持 1–9999",
            escape_control(value)
        )));
    }
    Some(Ok(format!("第{}条", chinese_number(number))))
}

/// Render 1–9999 as a Chinese article-number body (`三十九`, `一百四十三`).
fn chinese_number(number: u32) -> String {
    const DIGITS: [char; 10] = ['零', '一', '二', '三', '四', '五', '六', '七', '八', '九'];
    let mut rendered = String::new();
    let mut zero_pending = false;
    for (position, unit) in ["千", "百", "十", ""].iter().enumerate() {
        let divisor = 10u32.pow((3 - position) as u32);
        let digit = (number / divisor) % 10;
        if digit == 0 {
            if !rendered.is_empty() {
                zero_pending = true;
            }
            continue;
        }
        if zero_pending {
            rendered.push('零');
            zero_pending = false;
        }
        // Ten is `十`, not `一十`; 110 is `一百一十`, not `一百十`.
        if !(digit == 1 && position == 2 && rendered.is_empty()) {
            rendered.push(DIGITS[digit as usize]);
        }
        rendered.push_str(unit);
    }
    if rendered.is_empty() {
        rendered.push('零');
    }
    rendered
}

fn write_header(out: &mut impl Write, options: &Options, terms: &[String], root: &Path) {
    if options.keyword.trim().is_empty() {
        writeln!(out, "条文检索：无关键词（--article 直接列出条文）").ok();
    } else {
        writeln!(
            out,
            "条文检索：关键词「{}」",
            escape_control(&options.keyword)
        )
        .ok();
    }
    writeln!(
        out,
        "匹配规则：语料正文与关键词都做空白归一化（trim 并把连续空白折叠为空格）；\
         关键词按空白切成 {} 个词元，每个词元都按字面出现即命中（不要求相邻）；不使用正则。",
        terms.len()
    )
    .ok();
    writeln!(out, "语料根：{}", crate::escape_display_path(root)).ok();
    let mut filters = Vec::new();
    if let Some(law) = &options.law {
        filters.push(format!("法名 `{}`", escape_control(law)));
    }
    if let Some(version) = &options.version {
        filters.push(format!("版本 `{}`", escape_control(version)));
    }
    if let Some(article) = &options.article {
        filters.push(format!("条号 `{}`", escape_control(article)));
    }
    if let Some(code) = &options.jurisdiction {
        filters.push(format!("管辖 `{}`", escape_control(code)));
    }
    filters.push(format!("limit {}", options.limit));
    writeln!(out, "过滤：{}", filters.join("；")).ok();
    writeln!(
        out,
        "排序：按（法名, 版本, 条号）稳定排序；条文检索不构成法律结论。"
    )
    .ok();
    writeln!(out).ok();
}

fn available_ids(ids: &[String]) -> String {
    if ids.is_empty() {
        return "（无）".to_owned();
    }
    ids.iter()
        .map(|id| format!("`{}`", escape_control(id)))
        .collect::<Vec<_>>()
        .join("、")
}

fn law_matches(corpus: &Corpus, wanted: &str) -> bool {
    corpus.matches_name(wanted) || normalize_space(&corpus.law) == normalize_space(wanted)
}

fn article_exists(corpora: &[&Corpus], wanted: &str) -> bool {
    corpora.iter().any(|corpus| {
        corpus
            .articles
            .iter()
            .any(|article| numbers_equal(&article.number, wanted))
    })
}

/// Resolve `--article` against the selected corpora.
///
/// The literal value is checked first; only when no corpus stores it is the
/// ASCII number's Chinese ordinal tried. When both forms exist, the literal one
/// is used and the caller prints a note. Returns an error when neither exists,
/// naming both attempted forms.
fn resolve_article(corpora: &[&Corpus], raw: &str) -> Result<(String, Option<String>), String> {
    let literal = normalize_space(raw);
    let numeric = numeric_article(raw).transpose()?;
    if article_exists(corpora, &literal) {
        let also_present =
            numeric.filter(|chinese| chinese != &literal && article_exists(corpora, chinese));
        return Ok((literal, also_present));
    }
    if let Some(chinese) = numeric {
        if article_exists(corpora, &chinese) {
            return Ok((chinese, None));
        }
        return Err(format!(
            "没有该条号的语料：`{}`（也尝试 `{}`，均不存在）",
            escape_control(raw),
            escape_control(&chinese)
        ));
    }
    Err(format!(
        "没有该条号的语料：`{}`（在已选语料范围内）",
        escape_control(raw)
    ))
}

fn numbers_equal(left: &str, right: &str) -> bool {
    normalize_space(left) == normalize_space(right)
}

fn normalize_space(value: &str) -> String {
    value.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn keyword_terms(keyword: &str) -> Vec<String> {
    normalize_space(keyword)
        .split(' ')
        .filter(|term| !term.is_empty())
        .map(str::to_owned)
        .collect()
}

fn terms_match(text: &str, terms: &[String]) -> bool {
    let normalized = normalize_space(text);
    terms.iter().all(|term| normalized.contains(term))
}

struct Hit<'a> {
    corpus: &'a Corpus,
    article: &'a Article,
    index: usize,
}

/// The immutable session and scan data one result needs while printing.
struct SearchContext<'a, 'b> {
    env: &'a Env,
    packs: &'a [LoadedPackInfo],
    all_corpora: &'a [&'b Corpus],
    terms: &'a [String],
}

fn write_hit(
    out: &mut impl Write,
    hit: &Hit<'_>,
    options: &Options,
    context: &SearchContext<'_, '_>,
    hash_mismatch: &mut bool,
) {
    writeln!(
        out,
        "{}@{} {}",
        escape_control(&hit.corpus.law),
        escape_control(&hit.corpus.version),
        escape_control(&hit.article.number)
    )
    .ok();
    write_trust(out, hit.corpus, context.packs);
    writeln!(
        out,
        "  片段：{}",
        escape_control(&snippet(&hit.article.text, context.terms))
    )
    .ok();
    let report = rule_report(context.env, hit.corpus, hit.article, context.all_corpora);
    let has_linked_pack = has_linked_pack(hit.corpus, context.packs);
    write_coverage(out, hit, report.loaded.len(), has_linked_pack);
    write_rules(
        out,
        hit,
        context.env,
        &report,
        has_linked_pack,
        options.article.is_some(),
        hash_mismatch,
    );
    if options.article.is_some() {
        writeln!(out, "  全文：{}", escape_control(&hit.article.text)).ok();
        writeln!(
            out,
            "  条文哈希：{}（条文正文原样 UTF-8，含换行；与 :audit 同口径）",
            article_hash(&hit.article.text)
        )
        .ok();
    }
}

fn has_linked_pack(corpus: &Corpus, packs: &[LoadedPackInfo]) -> bool {
    let link = format!("{}/{}", corpus.law, corpus.version);
    packs
        .iter()
        .any(|pack| pack.corpus.as_deref() == Some(link.as_str()))
}

/// Print the trust level of a loaded pack that links exactly this corpus.
///
/// A corpus with no loaded pack is not labelled: the trust level belongs to a
/// pack, not to a corpus, and inventing one would misstate provenance.
fn write_trust(out: &mut impl Write, corpus: &Corpus, packs: &[LoadedPackInfo]) {
    let link = format!("{}/{}", corpus.law, corpus.version);
    for pack in packs {
        if pack.corpus.as_deref() == Some(link.as_str()) {
            writeln!(
                out,
                "  信任：{}（{}@{}）",
                crate::trust_label(pack.trust, pack.trust == Trust::Official),
                escape_control(&pack.name),
                escape_control(&pack.version)
            )
            .ok();
        }
    }
}

fn write_coverage(out: &mut impl Write, hit: &Hit<'_>, loaded_rules: usize, has_linked_pack: bool) {
    let entry = coverage_entry(hit);
    let Some(entry) = entry else {
        writeln!(out, "  覆盖：覆盖率台账不可用（不猜覆盖状态）").ok();
        return;
    };
    let label = match entry.status {
        CoverageStatus::Formalized => "已形式化",
        CoverageStatus::Partial => "部分",
        CoverageStatus::Indexed => "仅索引",
        CoverageStatus::NeedsOntology => "待本体",
    };
    writeln!(out, "  覆盖：{label}（来源：语料 coverage 台账）").ok();
    match entry.status {
        CoverageStatus::Indexed | CoverageStatus::NeedsOntology if loaded_rules > 0 => {
            writeln!(
                out,
                "  台账与已加载规则不一致：台账声明{label}，但已加载规则引用了该条。"
            )
            .ok();
        }
        CoverageStatus::Formalized | CoverageStatus::Partial
            if has_linked_pack && loaded_rules == 0 =>
        {
            writeln!(
                out,
                "  台账与已加载规则不一致：台账声明{label}，但当前环境没有引用该条的已加载规则。"
            )
            .ok();
        }
        _ => {}
    }
    match entry.status {
        CoverageStatus::Partial => {
            if let Some(note) = &entry.note {
                writeln!(out, "  残余：{}", escape_control(note)).ok();
            }
        }
        CoverageStatus::NeedsOntology => {
            if let Some(gap) = &entry.gap {
                let description = hit
                    .corpus
                    .coverage
                    .as_ref()
                    .and_then(|coverage| coverage.gaps.get(gap));
                match description {
                    Some(description) => {
                        writeln!(
                            out,
                            "  本体缺口：{}（{}）",
                            escape_control(gap),
                            escape_control(description)
                        )
                        .ok();
                    }
                    None => {
                        writeln!(out, "  本体缺口：{}", escape_control(gap)).ok();
                    }
                }
            }
        }
        _ => {
            if let Some(note) = &entry.note {
                writeln!(out, "  备注：{}", escape_control(note)).ok();
            }
        }
    }
}

fn coverage_entry<'a>(hit: &Hit<'a>) -> Option<&'a std_deduce_lawpack::corpus::ArticleCoverage> {
    let coverage = hit.corpus.coverage.as_ref()?;
    let entry = coverage.articles.get(hit.index)?;
    numbers_equal(&entry.number, &hit.article.number).then_some(entry)
}

/// A loaded rule body whose source names this article, before the quote and
/// jurisdiction checks.
struct MatchedRule {
    name: String,
    declared_hash: Option<String>,
}

/// How loaded rules relate to one article and to the corpus's declared ledger.
struct RuleReport {
    /// Loaded rules whose source selects this article and agrees with the
    /// article text and recorded jurisdiction.
    loaded: Vec<(String, String)>,
    /// Rules that name this article but whose quote or jurisdiction disagrees.
    rejected: Vec<(String, String)>,
    /// Rules whose citation omits a version while several corpora of the same
    /// law exist; the version is not guessed.
    ambiguous: Vec<(String, Vec<String>)>,
    /// Every rule body that names this article (used for hash checks).
    matched: Vec<MatchedRule>,
}

fn rule_report(
    env: &Env,
    corpus: &Corpus,
    article: &Article,
    all_corpora: &[&Corpus],
) -> RuleReport {
    let mut report = RuleReport {
        loaded: Vec::new(),
        rejected: Vec::new(),
        ambiguous: Vec::new(),
        matched: Vec::new(),
    };
    for decl in env.iter() {
        if !matches!(decl.kind, DeclKind::Rule(_)) {
            continue;
        }
        let name = decl.name.to_string();
        let mut exact = None;
        let mut ambiguous_versions: Option<Vec<String>> = None;
        for source in &decl.sources {
            if source.text.trim().is_empty() || !corpus.matches_name(&source.text) {
                continue;
            }
            if !numbers_equal(&source.locator, &article.number) {
                continue;
            }
            if source.version.is_empty() {
                let versions = versions_for_name(all_corpora, &source.text);
                if versions.len() > 1 {
                    ambiguous_versions.get_or_insert(versions);
                    continue;
                }
            } else if source.version != corpus.version {
                continue;
            }
            exact = Some(source);
            break;
        }
        let Some(source) = exact else {
            if let Some(versions) = ambiguous_versions {
                report.ambiguous.push((name, versions));
            }
            continue;
        };
        let quote_ok = source.quote.trim().is_empty()
            || strip_whitespace(&source.quote) == strip_whitespace(&article.text);
        let jurisdiction_ok =
            source.jurisdiction.is_empty() || source.jurisdiction == corpus.jurisdiction;
        let citation = source.one_line();
        report.matched.push(MatchedRule {
            name: name.clone(),
            declared_hash: (!source.hash.is_empty()).then(|| source.hash.clone()),
        });
        if quote_ok && jurisdiction_ok {
            report.loaded.push((name, citation));
        } else {
            let reason = if !quote_ok {
                "引文与条文不一致"
            } else {
                "管辖不符"
            };
            report.rejected.push((name, reason.to_owned()));
        }
    }
    report.loaded.sort();
    report.loaded.dedup();
    report.rejected.sort();
    report.rejected.dedup();
    report.ambiguous.sort();
    report.ambiguous.dedup();
    report
}

fn versions_for_name(corpora: &[&Corpus], name: &str) -> Vec<String> {
    let mut versions: Vec<String> = corpora
        .iter()
        .filter(|corpus| corpus.matches_name(name))
        .map(|corpus| corpus.version.clone())
        .collect();
    versions.sort();
    versions.dedup();
    versions
}

fn strip_whitespace(value: &str) -> String {
    value
        .chars()
        .filter(|character| !character.is_whitespace())
        .collect()
}

fn write_rules(
    out: &mut impl Write,
    hit: &Hit<'_>,
    env: &Env,
    report: &RuleReport,
    has_linked_pack: bool,
    check_hash: bool,
    hash_mismatch: &mut bool,
) {
    if !report.loaded.is_empty() {
        writeln!(out, "  引用规则（已加载）：").ok();
        for (name, citation) in &report.loaded {
            writeln!(out, "    - {} ← {}", escape_control(name), citation).ok();
        }
    }
    for (name, reason) in &report.rejected {
        writeln!(
            out,
            "  已加载规则 `{}` 的来源与语料不一致（{reason}），未列为引用规则。",
            escape_control(name)
        )
        .ok();
    }
    for (name, versions) in &report.ambiguous {
        writeln!(
            out,
            "  注：规则 `{}` 未记录版本，存在多版本（{}），无法确定引用哪一版，未列为引用规则。",
            escape_control(name),
            versions
                .iter()
                .map(|version| escape_control(version))
                .collect::<Vec<_>>()
                .join("/")
        )
        .ok();
    }

    let declared = coverage_entry(hit)
        .map(|entry| entry.rules.as_slice())
        .unwrap_or(&[]);
    let loaded_names: BTreeSet<&str> = report
        .loaded
        .iter()
        .map(|(name, _)| name.as_str())
        .collect();
    let mut no_pack: Vec<&str> = Vec::new();
    for name in declared {
        if loaded_names.contains(name.as_str()) {
            continue;
        }
        match env.get(name) {
            Some(decl) if matches!(decl.kind, DeclKind::Rule(_)) => {
                let sources = if decl.sources.is_empty() {
                    "（没有来源）".to_owned()
                } else {
                    decl.sources
                        .iter()
                        .map(|source| source.one_line())
                        .collect::<Vec<_>>()
                        .join("、")
                };
                writeln!(
                    out,
                    "  台账与已加载规则不一致：清单声明 `{}`，已加载规则 `{}` 的来源是 {}。",
                    escape_control(name),
                    escape_control(name),
                    sources
                )
                .ok();
            }
            _ if has_linked_pack => {
                writeln!(
                    out,
                    "  清单声明 `{}`，当前环境未加载该规则",
                    escape_control(name)
                )
                .ok();
            }
            _ => no_pack.push(name.as_str()),
        }
    }
    if !no_pack.is_empty() {
        writeln!(
            out,
            "  清单声明（包未加载）：{}",
            no_pack
                .iter()
                .map(|name| format!("「{}」", escape_control(name)))
                .collect::<Vec<_>>()
                .join("、")
        )
        .ok();
        writeln!(
            out,
            "  注：包未加载，无法给出条号定位；先 :load 或 import <包名> 再检索。"
        )
        .ok();
    }

    if check_hash {
        let local = article_hash(&hit.article.text);
        if report.matched.is_empty() {
            if report.ambiguous.is_empty() {
                writeln!(out, "  注：哈希为本地计算，未与包核对。").ok();
            } else {
                writeln!(
                    out,
                    "  注：规则未记录版本，无法确定引用哪一版；哈希为本地计算，未与包核对。"
                )
                .ok();
            }
        } else {
            let declared_hashes: Vec<&String> = report
                .matched
                .iter()
                .filter_map(|rule| rule.declared_hash.as_ref())
                .collect();
            if declared_hashes.is_empty() {
                writeln!(out, "  注：规则未记录 hash，哈希为本地计算，未与包核对。").ok();
            } else {
                let mut mismatched = false;
                for rule in &report.matched {
                    let Some(declared) = &rule.declared_hash else {
                        continue;
                    };
                    if declared != &local {
                        mismatched = true;
                        *hash_mismatch = true;
                        writeln!(
                            out,
                            "  ⚠ 语料哈希与规则声明不一致（本地 {}，规则 {}）；规则 `{}`。",
                            local,
                            escape_control(declared),
                            escape_control(&rule.name)
                        )
                        .ok();
                    }
                }
                if !mismatched {
                    writeln!(
                        out,
                        "  哈希核对：{} 条规则声明的 hash 与本地计算一致。",
                        declared_hashes.len()
                    )
                    .ok();
                }
            }
        }
    }

    if report.loaded.is_empty()
        && declared.is_empty()
        && report.matched.is_empty()
        && report.ambiguous.is_empty()
    {
        if coverage_entry(hit).is_none() {
            writeln!(
                out,
                "  尚未形式化（当前会话没有引用该条的规则；覆盖率台账不可用，无法核对清单声明）"
            )
            .ok();
        } else {
            writeln!(out, "  尚未形式化").ok();
        }
    }
}

fn snippet(text: &str, terms: &[String]) -> String {
    let normalized = normalize_space(text);
    if terms.is_empty() {
        return truncate_chars(&normalized, SNIPPET_WHOLE);
    }
    let mut first = usize::MAX;
    let mut last = 0;
    for term in terms {
        if let Some(index) = normalized.find(term) {
            first = first.min(index);
            last = last.max(index + term.len());
        }
    }
    if first == usize::MAX {
        return truncate_chars(&normalized, SNIPPET_WHOLE);
    }
    let characters: Vec<char> = normalized.chars().collect();
    let start = normalized[..first].chars().count();
    let end = normalized[..last].chars().count();
    let from = start.saturating_sub(SNIPPET_CONTEXT);
    let to = (end + SNIPPET_CONTEXT).min(characters.len());
    let mut body: String = characters[from..to].iter().collect();
    if from > 0 {
        body.insert(0, '…');
    }
    if to < characters.len() {
        body.push('…');
    }
    body
}

fn truncate_chars(text: &str, limit: usize) -> String {
    if text.chars().count() <= limit {
        return text.to_owned();
    }
    let mut shortened: String = text.chars().take(limit).collect();
    shortened.push('…');
    shortened
}
