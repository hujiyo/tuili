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
        err.contains("错误："),
        "stderr must carry the error:\n{err}"
    );
    let out = stdout(&output);
    assert!(
        !out.contains("推导"),
        "a failed load must not run the remaining commands:\n{out}"
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
        assert!(out.contains("check <文件.std>"), "{flag}: {out}");
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
