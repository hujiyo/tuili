//! End-to-end tests for `:audit`.
//!
//! Every case builds its own theory and corpus under a temporary directory, so
//! the tests do not depend on the repository's corpus. The assertions pin the
//! exit codes and the documented output shape.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const UNVERIFIED: i32 = 1;
const ERROR: i32 = 2;

/// Article 39 as one JSON string with an escaped newline.
const ARTICLE_39_JSON: &str =
    r"中华人民共和国公民的住宅不受侵犯。\n禁止非法搜查或者非法侵入公民的住宅。";
const QUOTE_39: &str = "中华人民共和国公民的住宅不受侵犯。禁止非法搜查或者非法侵入公民的住宅。";
const ARTICLE_39_SHA256: &str =
    "sha256:b0102d49a2563dde914e6247384e97403529aeb110f467434e620d1d08735fdb";

fn corpus_json(version: &str, article_text_json: &str) -> String {
    format!(
        r#"{{
  "format": 1,
  "law": "cn.constitution",
  "title": "中华人民共和国宪法",
  "aliases": ["宪法"],
  "version": "{version}",
  "jurisdiction": "CN",
  "articles": [
    {{ "number": "第三十九条", "text": "{article_text_json}" }}
  ]
}}"#
    )
}

fn theory(extra: &str) -> String {
    format!("sort 公民\nsource {extra}\n")
}

fn theory_with_quote(quote: &str) -> String {
    format!(
        "sort 公民\nsource text \"宪法\" locator \"第三十九条\" version \"2018\" quote \"{quote}\"\n"
    )
}

fn run(commands: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce-cli"))
        .args(commands)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn session(theory: &Path, corpus: &Path) -> Output {
    run(&[
        format!(":load {}", theory.display()),
        format!(":audit {}", corpus.display()),
    ])
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn assert_exit(output: &Output, expected: i32) {
    let code = output.status.code();
    assert_eq!(
        code,
        Some(expected),
        "expected exit {expected}, got {code:?}\nstdout:\n{}\nstderr:\n{}",
        stdout(output),
        stderr(output)
    );
}

fn line_starting_with(out: &str, prefix: char) -> &str {
    out.lines()
        .find(|line| line.starts_with(prefix))
        .unwrap_or_else(|| panic!("no line starts with `{prefix}`:\n{out}"))
}

#[test]
fn a_matching_quote_passes() {
    let temp = TempDir::new("hit");
    let theory = temp.theory("theory.std", &theory_with_quote(QUOTE_39));
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, PROVED);
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
    let out = stdout(&output);
    assert_eq!(
        line_starting_with(&out, '✓'),
        "✓ 「宪法第三十九条」← cn.constitution@2018"
    );
    assert!(
        out.contains("核对 1 条来源，命中 1，不一致 0，未核对 0。"),
        "{out}"
    );
    assert!(
        out.contains("条文哈希：0 条已固定并核验，1 条未固定，0 条未核验或格式非法。"),
        "{out}"
    );
}

#[test]
fn a_matching_hash_passes() {
    let temp = TempDir::new("hash-ok");
    let clause = format!(
        "text \"宪法\" locator \"第三十九条\" version \"2018\" quote \"{QUOTE_39}\" hash \"{ARTICLE_39_SHA256}\""
    );
    let theory = temp.theory("theory.std", &theory(&clause));
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("条文哈希：1 条已固定并核验，0 条未固定，0 条未核验或格式非法。"),
        "{out}"
    );
}

#[test]
fn a_wrong_hash_fails() {
    let temp = TempDir::new("hash-bad");
    let wrong = "sha256:b0102d49a2563dde914e6247384e97403529aeb110f467434e620d1d08735fdc";
    let clause = format!(
        "text \"宪法\" locator \"第三十九条\" version \"2018\" quote \"{QUOTE_39}\" hash \"{wrong}\""
    );
    let theory = temp.theory("theory.std", &theory(&clause));
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    let line = line_starting_with(&out, '✗');
    assert!(line.contains("条文哈希不符"), "{line}");
    assert!(line.contains("cn.constitution@2018"), "{line}");
    assert!(
        out.contains("条文哈希：1 条已固定并核验，0 条未固定，0 条未核验或格式非法。"),
        "{out}"
    );
}

#[test]
fn one_changed_character_fails() {
    let temp = TempDir::new("changed");
    let quote = QUOTE_39.replace("住宅不受侵犯", "住宅不受侵范");
    let theory = temp.theory("theory.std", &theory_with_quote(&quote));
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    let line = line_starting_with(&out, '✗');
    assert_eq!(
        line,
        "✗ 「宪法第三十九条」← cn.constitution@2018：引文与条文不一致"
    );
    assert!(
        out.contains("核对 1 条来源，命中 0，不一致 1，未核对 0。"),
        "{out}"
    );
}

#[test]
fn a_missing_corpus_is_unverified() {
    let temp = TempDir::new("missing-corpus");
    let theory = temp.theory("theory.std", &theory_with_quote(QUOTE_39));
    let corpus = temp.path().join("corpus");
    fs::create_dir_all(&corpus).expect("create the empty corpus directory");

    let output = session(&theory, &corpus);
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    assert!(out.contains("语料目录中没有语料"), "{out}");
    assert!(
        out.contains("? 「宪法第三十九条」：未找到语料（未核对）"),
        "{out}"
    );
    assert!(
        out.contains("核对 1 条来源，命中 0，不一致 0，未核对 1。"),
        "{out}"
    );
}

#[test]
fn a_missing_corpus_directory_is_unverified() {
    let temp = TempDir::new("no-corpus-dir");
    let theory = temp.theory("theory.std", &theory_with_quote(QUOTE_39));
    let missing = temp.path().join("does-not-exist");

    let output = session(&theory, &missing);
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    assert!(out.contains("无法读取语料目录"), "{out}");
    assert!(
        out.contains("? 「宪法第三十九条」：未找到语料（未核对）"),
        "{out}"
    );
}

#[test]
fn a_broken_corpus_exits_two() {
    let temp = TempDir::new("broken");
    let theory = temp.theory("theory.std", &theory_with_quote(QUOTE_39));
    temp.corpus("corpus/cn.constitution/2018.json", "not json");
    let corpus = temp.path().join("corpus");

    let output = session(&theory, &corpus);
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("JSON 解析失败"), "{out}");
    assert!(!out.contains("核对 "), "{out}");
    assert!(stderr(&output).contains("语料错误"), "{}", stderr(&output));
}

#[test]
fn a_misplaced_corpus_exits_two() {
    let temp = TempDir::new("misplaced");
    let theory = temp.theory("theory.std", &theory_with_quote(QUOTE_39));
    // The file is named 2019.json but declares version 2018: the strict layout
    // requires the file stem to equal the version.
    temp.corpus(
        "corpus/cn.constitution/2019.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("文件名主干"), "{out}");
    assert!(!out.contains("核对 "), "{out}");
}

#[test]
fn a_nested_corpus_file_exits_two() {
    let temp = TempDir::new("nested");
    let theory = temp.theory("theory.std", &theory_with_quote(QUOTE_39));
    temp.corpus("corpus/cn.constitution/2018/nested.json", "not json");

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("子目录"), "{out}");
    assert!(!out.contains("核对 "), "{out}");
}

#[test]
fn audit_refuses_to_run_before_load() {
    let temp = TempDir::new("no-load");
    let corpus = temp.path().join("corpus");
    fs::create_dir_all(&corpus).expect("create the empty corpus directory");

    let output = run(&[format!(":audit {}", corpus.display())]);
    assert_exit(&output, ERROR);
    assert!(
        stderr(&output).contains("尚未加载理论"),
        "{}",
        stderr(&output)
    );
    assert!(stdout(&output).contains("语料核对：未运行"), "{output:?}");
}

#[test]
fn a_version_mismatch_fails() {
    let temp = TempDir::new("version");
    let theory = temp.theory(
        "theory.std",
        "sort 公民\nsource text \"宪法\" locator \"第三十九条\" version \"2019\" quote \"\
         中华人民共和国公民的住宅不受侵犯。禁止非法搜查或者非法侵入公民的住宅。\"\n",
    );
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    let line = line_starting_with(&out, '✗');
    assert!(line.contains("版本不符"), "{line}");
    assert!(line.contains("2019"), "{line}");
    assert!(line.contains("2018"), "{line}");
}

#[test]
fn a_missing_article_fails() {
    let temp = TempDir::new("no-article");
    let theory = temp.theory(
        "theory.std",
        "sort 公民\nsource text \"宪法\" locator \"第四十条\" version \"2018\" quote \"\
         中华人民共和国公民的住宅不受侵犯。禁止非法搜查或者非法侵入公民的住宅。\"\n",
    );
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    let line = line_starting_with(&out, '✗');
    assert!(line.contains("条号"), "{line}");
}

#[test]
fn an_ambiguous_instrument_without_a_version_fails() {
    let temp = TempDir::new("ambiguous");
    let theory = temp.theory(
        "theory.std",
        &format!("sort 公民\nsource text \"宪法\" locator \"第三十九条\" quote \"{QUOTE_39}\"\n"),
    );
    temp.corpus(
        "corpus/cn.constitution/2017.json",
        &corpus_json("2017", ARTICLE_39_JSON),
    );
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    let line = line_starting_with(&out, '✗');
    assert!(line.contains("候选"), "{line}");
}

#[test]
fn a_missing_quote_is_unverified() {
    let temp = TempDir::new("no-quote");
    let theory = temp.theory(
        "theory.std",
        "sort 公民\nsource text \"宪法\" locator \"第三十九条\" version \"2018\"\n",
    );
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    assert!(
        out.contains("? 「宪法第三十九条」：没有引文原文（未核对）"),
        "{out}"
    );
    assert!(
        out.contains("核对 1 条来源，命中 0，不一致 0，未核对 1。"),
        "{out}"
    );
}

#[test]
fn the_report_stays_one_line_when_a_source_field_contains_a_newline() {
    let temp = TempDir::new("escaping");
    // `\n` is a two-character escape in the theory file; the lexer turns it
    // into a real newline in `text` and in `quote`. The name still normalizes
    // to 「宪法」, and the printed label must escape the newline again.
    let theory = temp.theory(
        "theory.std",
        "sort 公民\nsource text \"宪法\\n\" locator \"第三十九条\" version \"2018\" quote \"\
         中华人民共和国公民的住宅不受侵犯。\\n禁止非法搜查或者非法侵入公民的住宅。\"\n",
    );
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert_eq!(
        line_starting_with(&out, '✓'),
        "✓ 「宪法\\n第三十九条」← cn.constitution@2018"
    );
}

#[test]
fn the_report_escapes_a_control_character_in_a_failure_detail() {
    let temp = TempDir::new("escape-detail");
    let theory = temp.theory(
        "theory.std",
        "sort 公民\nsource text \"宪法\" locator \"第三十九条\" version \"2019\\n\" quote \"\
         中华人民共和国公民的住宅不受侵犯。禁止非法搜查或者非法侵入公民的住宅。\"\n",
    );
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    let line = line_starting_with(&out, '✗');
    assert!(line.contains("版本不符"), "{line}");
    assert!(line.contains("2019\\n"), "{line}");
}

#[test]
fn every_source_is_counted_and_one_unverified_source_fails_the_run() {
    let temp = TempDir::new("counts");
    let theory = temp.theory(
        "theory.std",
        &format!(
            "sort 公民\nsource text \"宪法\" locator \"第三十九条\" version \"2018\" quote \"{QUOTE_39}\"\n\
             sort 住宅\nsource text \"宪法\" locator \"第三十九条\" version \"2018\"\n"
        ),
    );
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    assert_eq!(out.lines().filter(|line| line.starts_with('✓')).count(), 1);
    assert_eq!(out.lines().filter(|line| line.starts_with('?')).count(), 1);
    assert!(
        out.contains("核对 2 条来源，命中 1，不一致 0，未核对 1。"),
        "{out}"
    );
}

#[test]
fn a_jurisdiction_mismatch_fails() {
    let temp = TempDir::new("jurisdiction");
    let clause = format!(
        "text \"宪法\" locator \"第三十九条\" version \"2018\" jurisdiction \"US\" quote \"{QUOTE_39}\""
    );
    let theory = temp.theory("theory.std", &theory(&clause));
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    let line = line_starting_with(&out, '✗');
    assert!(line.contains("管辖不符"), "{line}");
    assert!(line.contains("US") && line.contains("CN"), "{line}");
    assert!(
        out.contains("核对 1 条来源，命中 0，不一致 1，未核对 0。"),
        "{out}"
    );
}

#[test]
fn an_invalid_hash_format_fails_and_is_not_counted_as_fixed() {
    let temp = TempDir::new("bad-hash-format");
    let clause = format!(
        "text \"宪法\" locator \"第三十九条\" version \"2018\" quote \"{QUOTE_39}\" hash \"sha256:abc\""
    );
    let theory = temp.theory("theory.std", &theory(&clause));
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    let line = line_starting_with(&out, '✗');
    assert!(line.contains("条文哈希格式无效"), "{line}");
    assert!(
        out.contains("条文哈希：0 条已固定并核验，0 条未固定，1 条未核验或格式非法。"),
        "{out}"
    );
}

#[test]
fn an_unknown_corpus_field_exits_two() {
    let temp = TempDir::new("unknown-field");
    let theory = temp.theory("theory.std", &theory_with_quote(QUOTE_39));
    let body = corpus_json("2018", ARTICLE_39_JSON)
        .replace("\"format\": 1,", "\"format\": 1,\n  \"bogus\": 1,");
    temp.corpus("corpus/cn.constitution/2018.json", &body);

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("bogus"), "{out}");
    assert!(!out.contains("核对 "), "{out}");
    assert!(stderr(&output).contains("语料错误"), "{}", stderr(&output));
}

#[test]
fn a_corpus_text_hash_is_reported_as_unchecked_metadata() {
    let temp = TempDir::new("text-hash-note");
    let theory = temp.theory("theory.std", &theory_with_quote(QUOTE_39));
    let body = corpus_json("2018", ARTICLE_39_JSON).replace(
        "\"jurisdiction\": \"CN\",",
        "\"jurisdiction\": \"CN\",\n  \"text_sha256\": \"sha256:0000000000000000000000000000000000000000000000000000000000000000\",",
    );
    temp.corpus("corpus/cn.constitution/2018.json", &body);

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("语料的 text_sha256 仅为出处元数据，未重算、未校验"),
        "{out}"
    );
}

#[test]
fn the_report_escapes_invisible_formatting_characters_and_a_backslash() {
    let temp = TempDir::new("escape-format");
    let theory = temp.theory("theory.std", &theory_with_quote(QUOTE_39));
    // The unknown field name carries ESC, U+2028, U+202E and one literal
    // backslash; serde reports it by name, and the audit must escape it.
    let body = format!(
        "{{\n  \"format\": 1,\n  \"law\": \"cn.constitution\",\n  \"title\": \"中华人民共和国宪法\",\n  \"aliases\": [],\n  \"version\": \"2018\",\n  \"jurisdiction\": \"CN\",\n  \"articles\": [ {{ \"number\": \"第三十九条\", \"text\": \"{ARTICLE_39_JSON}\" }} ],\n  \"\\u001b[31m\\u2028\\u202e\\\\\": 1\n}}"
    );
    temp.corpus("corpus/cn.constitution/2018.json", &body);

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(
        out.contains("\\u{001B}[31m\\u{2028}\\u{202E}\\\\"),
        "{out:?}"
    );
    assert!(!out.contains('\u{001B}'), "{out:?}");
    assert!(!out.contains('\u{2028}'), "{out:?}");
    assert!(!out.contains('\u{202E}'), "{out:?}");
}

#[test]
fn the_report_escapes_invisible_characters_in_a_source_version() {
    let temp = TempDir::new("escape-version");
    // `\\` in the theory file becomes one literal backslash after lexing.
    let version = "v\u{2028}\u{202E}\\\\";
    let theory = temp.theory(
        "theory.std",
        &format!(
            "sort 公民\nsource text \"宪法\" locator \"第三十九条\" version \"{version}\" quote \"{QUOTE_39}\"\n"
        ),
    );
    temp.corpus(
        "corpus/cn.constitution/2018.json",
        &corpus_json("2018", ARTICLE_39_JSON),
    );

    let output = session(&theory, &temp.path().join("corpus"));
    assert_exit(&output, UNVERIFIED);
    let out = stdout(&output);
    let line = line_starting_with(&out, '✗');
    assert!(line.contains("版本不符"), "{line:?}");
    assert!(line.contains("v\\u{2028}\\u{202E}\\\\"), "{line:?}");
    assert!(!line.contains('\u{2028}'), "{line:?}");
    assert!(!line.contains('\u{202E}'), "{line:?}");
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cli-audit-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn theory(&self, name: &str, source: &str) -> PathBuf {
        self.write(name, source)
    }

    fn corpus(&self, relative: &str, text: &str) -> PathBuf {
        self.write(relative, text)
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.path.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
        }
        fs::write(&path, text).unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
