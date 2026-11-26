//! End-to-end tests for the binary entry points.
//!
//! Batch loading, the `check` alias, `repl`, usage and version are exercised
//! through the real binary. Assertions pin exit codes and stable text, not
//! whole-output snapshots.

use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const LOAD_ERROR: i32 = 1;
const USAGE_ERROR: i32 = 2;

fn examples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}

fn example(name: &str) -> String {
    let path = examples_dir().join(name);
    assert!(path.is_file(), "missing example file: {}", path.display());
    path.to_string_lossy().into_owned()
}

fn run(args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn run_with_stdin(args: &[String], input: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start the CLI");
    child
        .stdin
        .as_mut()
        .expect("piped stdin")
        .write_all(input.as_bytes())
        .expect("write stdin");
    child.wait_with_output().expect("the CLI exits")
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

/// A temporary directory outside the repository, removed when the test ends.
struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("std-deduce entry {tag} {}-{n}", std::process::id()));
        fs::create_dir_all(&path).unwrap_or_else(|e| panic!("create {}: {e}", path.display()));
        TempDir { path }
    }

    fn write(&self, name: &str, contents: &str) -> PathBuf {
        let path = self.path.join(name);
        fs::write(&path, contents).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

const GOOD_THEORY: &str = "sort 公民\npred 好人 : 公民 → Prop\nobj 张三 : 公民\naxiom 张三是好人 : 好人 张三\n  source text \"测试\" locator \"夹具\"\n";

/// A theory that cannot load: the axiom has no source.
const BAD_THEORY: &str =
    "sort 公民\npred 好人 : 公民 → Prop\nobj 张三 : 公民\naxiom 张三是好人 : 好人 张三\n";

/// A file that fails in the parser: `bogus` is not a declaration keyword.
const BAD_SYNTAX_THEORY: &str = "sort 公民\nbogus\n";

/// A file that parses but fails in elaboration: the predicate's domain is an
/// unknown name, and elaboration has no AST span to report.
const BAD_REFINEMENT_THEORY: &str = "sort 公民\npred 好人 : 未知类型 → Prop\n";

#[test]
fn a_batch_file_loads_and_exits_zero() {
    let output = run(&[example("constitution-39.std")]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains("已加载"), "{out}");
    assert!(
        out.contains("不受侵犯"),
        "the load report lists declarations:\n{out}"
    );
}

#[test]
fn a_failed_batch_load_exits_one_and_skips_the_remaining_commands() {
    let dir = TempDir::new("bad");
    let file = dir.write("坏文件.std", BAD_THEORY);
    let output = run(&[file.display().to_string(), ":why 好人 张三".to_owned()]);
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert!(
        err.contains(&file.display().to_string()),
        "stderr must name the file:\n{err}"
    );
    assert!(
        err.contains(&format!(
            "{}: error: axiom `张三是好人` 缺少 source",
            file.display()
        )),
        "a positionless load error must render as `path: error: ...`:\n{err}"
    );
    assert!(
        !err.contains("错误："),
        "the batch entry must not add a second prefix:\n{err}"
    );
    assert_eq!(
        err.matches(&file.display().to_string()).count(),
        1,
        "the path must appear once:\n{err}"
    );
    let out = stdout(&output);
    assert!(
        !out.contains("推导"),
        "a failed load must not run the remaining commands:\n{out}"
    );
}

#[test]
fn a_batch_syntax_error_prints_path_line_and_column() {
    let dir = TempDir::new("syntax");
    let file = dir.write("坏语法.std", BAD_SYNTAX_THEORY);
    let path = file.display().to_string();
    let output = run(std::slice::from_ref(&path));
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert!(
        err.contains(&format!("{path}:2:1: error: 未知声明关键字 `bogus`")),
        "stderr must be `path:line:col: error: ...`:\n{err}"
    );
    assert_eq!(
        err.matches(&path).count(),
        1,
        "the batch entry must not repeat the path:\n{err}"
    );
    assert!(
        !err.contains("错误："),
        "the batch entry must not add the `:load` prefix:\n{err}"
    );
    assert!(stdout(&output).is_empty(), "no report on a failed load");
}

#[test]
fn a_load_command_syntax_error_keeps_its_prefix_and_position() {
    let dir = TempDir::new("load-syntax");
    let file = dir.write("坏语法.std", BAD_SYNTAX_THEORY);
    let path = file.display().to_string();
    let output = run_with_stdin(&[], &format!(":load {path}\n:quit\n"));
    assert_exit(&output, USAGE_ERROR);
    let out = stdout(&output);
    assert!(
        out.contains(&format!("错误：{path}:2:1: error: 未知声明关键字 `bogus`")),
        "`:load` keeps its `错误：` prefix and the rendered position:\n{out}"
    );
    assert!(stderr(&output).is_empty(), "the REPL reports on stdout");
}

#[test]
fn a_refinement_error_has_no_fabricated_position() {
    let dir = TempDir::new("refinement");
    let file = dir.write("坏精化.std", BAD_REFINEMENT_THEORY);
    let path = file.display().to_string();
    let output = run(std::slice::from_ref(&path));
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert!(
        err.starts_with(&format!("{path}: error: ")),
        "a refinement error has no AST span and must not invent one:\n{err}"
    );
    assert!(err.contains("未知名称 `未知类型`"), "{err}");
    assert_eq!(
        err.matches(&path).count(),
        1,
        "the path must appear once:\n{err}"
    );
}

#[test]
fn a_batch_file_path_with_spaces_loads_as_one_argument() {
    let dir = TempDir::new("space");
    let file = dir.write("含 空格 的理论.std", GOOD_THEORY);
    let output = run(&[file.display().to_string()]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains("已加载"), "{out}");
    assert!(out.contains(&file.display().to_string()), "{out}");
}

#[test]
fn the_check_subcommand_matches_the_direct_file_entry() {
    let direct = run(&[example("constitution-39.std")]);
    let checked = run(&["check".to_owned(), example("constitution-39.std")]);
    assert_exit(&direct, PROVED);
    assert_exit(&checked, PROVED);
    assert_eq!(stdout(&direct), stdout(&checked));
    assert_eq!(stderr(&direct), stderr(&checked));
}

#[test]
fn a_batch_file_then_a_query_runs_after_the_load() {
    let output = run(&[
        example("constitution-39.std"),
        ":why 不受侵犯 张三 甲宅".to_owned(),
    ]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains("已加载"), "{out}");
    assert!(out.contains("推导已通过独立校验。"), "{out}");
}

#[test]
fn help_lists_the_batch_and_certificate_entries() {
    for flag in ["--help", "-h"] {
        let output = run(&[flag.to_owned()]);
        assert_exit(&output, PROVED);
        let out = stdout(&output);
        assert!(out.contains("std-deduce"), "{flag}: {out}");
        assert!(out.contains(":verify-cert"), "{flag}: {out}");
        assert!(out.contains(":explain"), "{flag}: {out}");
        assert!(out.contains("check <文件.std>"), "{flag}: {out}");
    }
}

/// Every user-facing colon command, in one place.
///
/// `--help` and the REPL `:help` must both list all of them; a command added to
/// the dispatcher without a help line failed here instead of being discoverable
/// only from the README. `:help`, `:quit` and `:exit` are REPL controls, not
/// query commands, so they are not in this list.
const COLON_COMMANDS: &[&str] = &[
    ":load",
    ":load-case",
    ":inspect",
    ":given",
    ":fact",
    ":interpret",
    ":asof",
    ":jurisdiction",
    ":why",
    ":explain",
    ":labels",
    ":review",
    ":gap",
    ":branches",
    ":issues",
    ":applicability",
    ":cert",
    ":verify-cert",
    ":redact",
    ":packs",
    ":lock",
    ":audit",
    ":search",
];

/// True when `command` appears as a whole colon command, not as part of a
/// longer one: `:load` also prefixes `:load-case`, and `:cert` suffix-matches
/// `:verify-cert`.
fn mentions_command(text: &str, command: &str) -> bool {
    let joins = |next: Option<char>| matches!(next, Some(c) if c.is_ascii_alphanumeric() || c == '-' || c == '_');
    text.match_indices(command).any(|(start, _)| {
        let before = text[..start].chars().next_back();
        let after = text[start + command.len()..].chars().next();
        !joins(before) && !joins(after)
    })
}

#[test]
fn help_lists_every_user_facing_colon_command() {
    for flag in ["--help", "-h"] {
        let output = run(&[flag.to_owned()]);
        assert_exit(&output, PROVED);
        let out = stdout(&output);
        for command in COLON_COMMANDS {
            assert!(
                mentions_command(&out, command),
                "{flag} must list {command}:\n{out}"
            );
        }
    }
    let repl = run_with_stdin(&[], ":help\n:quit\n");
    assert_exit(&repl, PROVED);
    let out = stdout(&repl);
    for command in COLON_COMMANDS {
        assert!(
            mentions_command(&out, command),
            ":help must list {command}:\n{out}"
        );
    }
}

#[test]
fn version_prints_the_binary_name_and_version() {
    let expected = format!("std-deduce {}\n", env!("CARGO_PKG_VERSION"));
    for flag in ["--version", "-V"] {
        let output = run(&[flag.to_owned()]);
        assert_exit(&output, PROVED);
        assert_eq!(stdout(&output), expected, "{flag}");
        assert!(stderr(&output).is_empty(), "{flag}");
    }
}

#[test]
fn the_repl_entry_forms_start_the_session() {
    for args in [Vec::new(), vec!["repl".to_owned()]] {
        let output = run_with_stdin(&args, ":help\n:quit\n");
        assert_exit(&output, PROVED);
        let out = stdout(&output);
        assert!(out.contains("std-deduce"), "{args:?}: {out}");
        assert!(out.contains(":verify-cert"), "{args:?}: {out}");
        assert!(out.contains(":fact"), "{args:?}: {out}");
        assert!(out.contains(":explain"), "{args:?}: {out}");
        assert!(!out.contains(":check <证书文件>"), "{args:?}: {out}");
    }
}

#[test]
fn check_without_a_file_is_a_usage_error() {
    let output = run(&["check".to_owned()]);
    assert_exit(&output, USAGE_ERROR);
    let err = stderr(&output);
    assert!(err.contains("用法"), "{err}");
    assert!(err.contains("check"), "{err}");
}

#[test]
fn repl_does_not_silently_ignore_extra_arguments() {
    let output = run(&["repl".to_owned(), ":why 好人 张三".to_owned()]);
    assert_exit(&output, USAGE_ERROR);
    let err = stderr(&output);
    assert!(err.contains("用法"), "{err}");
}

#[test]
fn an_option_after_a_file_is_a_usage_error_not_silently_ignored() {
    let output = run(&[example("constitution-39.std"), "--help".to_owned()]);
    assert_exit(&output, USAGE_ERROR);
    let err = stderr(&output);
    assert!(
        err.contains("未知选项"),
        "stderr must name the unknown option:\n{err}"
    );
    assert!(
        err.contains(":why"),
        "the hint must point at :why / :gap:\n{err}"
    );
    assert!(!err.contains("读取失败"), "an option is not a file:\n{err}");
    let out = stdout(&output);
    assert!(
        out.contains("已加载"),
        "the file itself loaded before the usage error:\n{out}"
    );
}

#[test]
fn an_unknown_first_option_is_a_usage_error_not_a_file() {
    for option in ["--foo", "--help=foo"] {
        let output = run(&[option.to_owned()]);
        assert_exit(&output, USAGE_ERROR);
        let err = stderr(&output);
        assert!(err.contains("未知选项"), "{option}: {err}");
        assert!(
            !err.contains("读取失败"),
            "{option} must not be read as a file: {err}"
        );
        assert!(
            stdout(&output).is_empty(),
            "{option} must not print a load report"
        );
    }
}

#[test]
fn check_does_not_treat_an_option_as_a_file() {
    let output = run(&["check".to_owned(), "--help".to_owned()]);
    assert_exit(&output, USAGE_ERROR);
    let err = stderr(&output);
    assert!(err.contains("未知选项"), "{err}");
    assert!(!err.contains("读取失败"), "{err}");
}

#[test]
fn a_repl_option_line_is_not_silently_ignored() {
    let output = run_with_stdin(&[], "--foo\n:quit\n");
    assert_exit(&output, USAGE_ERROR);
    let out = stdout(&output);
    assert!(out.contains("未知选项"), "{out}");
    assert!(out.contains("错误："), "{out}");
}

#[test]
fn a_failed_load_path_with_control_characters_prints_one_escaped_line() {
    let dir = TempDir::new("escaped-path");
    let missing = dir.path.join("坏\u{001B}\u{202E}\n文件.std");
    let path = missing.display().to_string();
    let output = run(std::slice::from_ref(&path));
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert_eq!(
        err.lines().count(),
        1,
        "exactly one diagnostic line:\n{err:?}"
    );
    assert!(
        !err.trim_end_matches('\n').contains('\n'),
        "the raw newline must not reach stderr:\n{err:?}"
    );
    assert!(err.contains("\\n"), "the newline must be escaped:\n{err:?}");
    assert!(err.contains("\\u{001B}"), "ESC must be escaped:\n{err:?}");
    assert!(
        err.contains("\\u{202E}"),
        "U+202E must be escaped:\n{err:?}"
    );
    assert!(!err.contains('\u{001B}'), "{err:?}");
    assert!(!err.contains('\u{202E}'), "{err:?}");
}

#[test]
fn help_lists_the_certificate_identity_options() {
    for flag in ["--help", "-h"] {
        let output = run(&[flag.to_owned()]);
        assert_exit(&output, PROVED);
        let out = stdout(&output);
        assert!(out.contains("--as-of <YYYY-MM-DD>"), "{flag}: {out}");
        assert!(out.contains("--jurisdiction <代码>"), "{flag}: {out}");
        assert!(
            out.contains("适用性判定"),
            "the help must say the options are applicability reference values:\n{flag}: {out}"
        );
        assert!(
            out.contains(":applicability"),
            "the help must name the applicability report:\n{flag}: {out}"
        );
        assert!(
            out.contains(":cert / :verify-cert"),
            "the help must name the commands the options affect:\n{flag}: {out}"
        );
    }
}

#[test]
fn certificate_identity_option_errors_are_usage_errors() {
    let cases: Vec<(&str, Vec<String>, &str)> = vec![
        (
            "impossible calendar day",
            vec!["--as-of".into(), "2026-02-30".into(), "x.std".into()],
            "--as-of `2026-02-30` 的日期 30 超出",
        ),
        (
            "malformed date",
            vec!["--as-of".into(), "2026-1-1".into(), "x.std".into()],
            "--as-of `2026-1-1` 不是 YYYY-MM-DD 日期",
        ),
        (
            "jurisdiction with a separator",
            vec!["--jurisdiction".into(), "CN/".into(), "x.std".into()],
            "--jurisdiction `CN/` 含非法字符",
        ),
        (
            "non-ASCII jurisdiction",
            vec!["--jurisdiction".into(), "中国".into(), "x.std".into()],
            "--jurisdiction `中国` 含非法字符",
        ),
        (
            "empty jurisdiction",
            vec!["--jurisdiction".into(), String::new(), "x.std".into()],
            "--jurisdiction 不能为空",
        ),
        (
            "missing as-of value",
            vec!["--as-of".into()],
            "--as-of 缺少值",
        ),
        (
            "missing jurisdiction value",
            vec!["--jurisdiction".into()],
            "--jurisdiction 缺少值",
        ),
        (
            "as-of value looking like an option",
            vec!["--as-of".into(), "--help".into()],
            "--as-of 缺少值，`--help` 看起来是选项",
        ),
        (
            "duplicate as-of",
            vec![
                "--as-of".into(),
                "2026-11-23".into(),
                "--as-of".into(),
                "2026-11-24".into(),
                "x.std".into(),
            ],
            "--as-of 只能使用一次",
        ),
        (
            "duplicate jurisdiction",
            vec![
                "--jurisdiction".into(),
                "CN".into(),
                "--jurisdiction".into(),
                "US".into(),
                "x.std".into(),
            ],
            "--jurisdiction 只能使用一次",
        ),
        (
            "as-of after env",
            vec!["env".into(), "--as-of".into(), "2026-11-23".into()],
            "env 之前",
        ),
    ];
    for (case, arguments, needle) in cases {
        let output = run(&arguments);
        assert_exit(&output, USAGE_ERROR);
        let err = stderr(&output);
        assert!(
            err.contains(needle),
            "{case}: stderr does not contain {needle:?}\nstderr:\n{err}"
        );
        assert!(
            stdout(&output).is_empty(),
            "{case}: a usage error must not load anything:\n{}",
            stdout(&output)
        );
    }

    // An option after the file is still a usage error, but the batch entry has
    // already loaded the file by then, the same as any other option-looking
    // argument after a file.
    for arguments in [
        vec![
            example("constitution-39.std"),
            "--as-of".into(),
            "2026-11-23".into(),
        ],
        vec![
            example("constitution-39.std"),
            "--jurisdiction".into(),
            "CN".into(),
        ],
    ] {
        let output = run(&arguments);
        assert_exit(&output, USAGE_ERROR);
        let err = stderr(&output);
        assert!(err.contains("未知选项"), "{arguments:?}: {err}");
        assert!(
            stdout(&output).contains("已加载"),
            "{arguments:?}: the file itself loads before the usage error:\n{}",
            stdout(&output)
        );
    }
}

#[test]
fn certificate_identity_option_errors_cannot_inject_a_diagnostic_line() {
    // The lawpack validators embed the raw option value in their error text.
    // A value carrying a newline or ESC must not break the usage diagnostic
    // into a second line or reach the terminal raw, so both validators escape
    // the whole error before it is prefixed.
    let cases: Vec<(&str, Vec<String>, &str)> = vec![
        (
            "as-of with a newline",
            vec![
                "--as-of".into(),
                "2026-11-2\n错误：伪造诊断".into(),
                "x.std".into(),
            ],
            "`2026-11-2\\n错误：伪造诊断` 不是 YYYY-MM-DD 日期",
        ),
        (
            "jurisdiction with ESC",
            vec![
                "--jurisdiction".into(),
                "CN\u{001B}[31m伪造".into(),
                "x.std".into(),
            ],
            "`CN\\u{001B}[31m伪造` 含非法字符",
        ),
    ];
    for (case, arguments, escaped_needle) in cases {
        let output = run(&arguments);
        assert_exit(&output, USAGE_ERROR);
        let err = stderr(&output);
        assert_eq!(
            err.lines().count(),
            1,
            "{case}: exactly one diagnostic line:\n{err:?}"
        );
        assert!(
            err.contains("用法错误："),
            "{case}: the usage prefix must stay:\n{err:?}"
        );
        assert!(
            err.contains(escaped_needle),
            "{case}: the control characters must be escaped:\n{err:?}"
        );
        assert!(!err.contains('\u{001B}'), "{case}: raw ESC:\n{err:?}");
        assert!(
            !err.trim_end_matches('\n').contains('\n'),
            "{case}: the raw newline must not reach stderr:\n{err:?}"
        );
        assert!(
            stdout(&output).is_empty(),
            "{case}: a usage error must not load anything"
        );
    }
}

#[test]
fn a_windows_path_in_a_load_error_is_not_backslash_doubled() {
    let dir = TempDir::new("backslash");
    let file = dir.write("坏文件.std", BAD_THEORY);
    let path = file.display().to_string();
    let output = run(std::slice::from_ref(&path));
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert_eq!(err.lines().count(), 1, "{err:?}");
    assert!(
        err.starts_with(&path),
        "the escaped path must stay readable:\n{err}\npath: {path}"
    );
    if path.contains('\\') {
        assert!(
            !err.contains(&path.replace('\\', "\\\\")),
            "a Windows separator must not be doubled:\n{err}\npath: {path}"
        );
    }
}

#[test]
fn allow_case_rules_requires_the_closed_environment() {
    let output = run(&[
        "--allow-case-rules".to_owned(),
        example("宪法案例-齐玉苓.std"),
    ]);
    assert_exit(&output, USAGE_ERROR);
    let err = stderr(&output);
    assert!(
        err.contains("--allow-case-rules 需要同时给 --closed-env"),
        "{err}"
    );
    assert!(
        stdout(&output).is_empty(),
        "a usage error must not load the file:\n{}",
        stdout(&output)
    );
}

#[test]
fn help_lists_the_closed_environment_options() {
    let output = run(&["--help".to_owned()]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains("--closed-env"), "{out}");
    assert!(
        out.contains("案件文件只能使用已加载法律包里的声明与规则"),
        "{out}"
    );
    assert!(out.contains("--allow-case-rules"), "{out}");
    assert!(out.contains("证书会标记为本地扩展"), "{out}");
}

#[test]
fn closed_env_after_a_file_is_a_usage_error() {
    let output = run(&[example("constitution-39.std"), "--closed-env".to_owned()]);
    assert_exit(&output, USAGE_ERROR);
    let err = stderr(&output);
    assert!(err.contains("未知选项"), "{err}");
    assert!(
        stdout(&output).contains("已加载"),
        "the file itself loaded before the usage error:\n{}",
        stdout(&output)
    );
}
