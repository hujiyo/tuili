//! End-to-end tests for the official `cn.constitution` law pack.
//!
//! These tests exercise the repository's fixed `lawpacks/` registry, so every
//! CLI run starts from the repository root. The corruption test copies the
//! registry into its own temporary directory; it never edits the repository.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const LOAD_FAILED: i32 = 1;
const ERROR: i32 = 2;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The facts-only example that imports the official pack.
fn import_example() -> PathBuf {
    repo_root().join("examples/宪法第三十九条-导入包.std")
}

fn run_in(current_dir: &Path, args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(current_dir)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn run_in_repo(args: &[String]) -> Output {
    run_in(&repo_root(), args)
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// Assert the exit code and that stdout contains every needle.
fn check(output: Output, expected: i32, needles: &[&str]) -> Output {
    let code = output.status.code();
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(
        code,
        Some(expected),
        "expected exit {expected}, got {code:?}\nstdout:\n{out}\nstderr:\n{err}"
    );
    for needle in needles {
        assert!(
            out.contains(needle),
            "stdout does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

fn check_stderr(output: Output, expected: i32, needles: &[&str]) -> Output {
    let code = output.status.code();
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(
        code,
        Some(expected),
        "expected exit {expected}, got {code:?}\nstdout:\n{out}\nstderr:\n{err}"
    );
    for needle in needles {
        assert!(
            err.contains(needle),
            "stderr does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

#[test]
fn the_official_pack_is_listed_and_its_lock_verifies() {
    let output = check(
        run_in_repo(&[":packs lawpacks".to_string()]),
        PROVED,
        &[
            "cn.constitution 0.1.0",
            "中华人民共和国宪法最小官方包（第三十九条示例；完整规则见 M2-16）",
            "文件 1 个",
            "锁定校验：通过（1 个包）",
        ],
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn inspect_marks_pack_declarations_with_the_pack_version() {
    let output = check(
        run_in_repo(&[
            import_example().display().to_string(),
            ":inspect".to_string(),
        ]),
        PROVED,
        &[
            "rule  cn.constitution.非法搜查即侵犯",
            "[cn.constitution@0.1.0]",
            "引文：中华人民共和国公民的住宅不受侵犯。禁止非法搜查或者非法侵入公民的住宅。",
        ],
    );
    let out = stdout(&output);
    // Both sorts, both predicates and the rule all come from the pack and are
    // marked with the locked version; the case objects are not.
    assert_eq!(out.matches("[cn.constitution@0.1.0]").count(), 5, "{out}");
}

#[test]
fn audit_matches_the_quotation_inside_the_official_pack() {
    let output = check(
        run_in_repo(&[import_example().display().to_string(), ":audit".to_string()]),
        PROVED,
        &[
            "✓ 「宪法第三十九条」← cn.constitution@2018",
            "核对 1 条带引文来源：命中 1，不一致 0，未核对 0；另有 1 条来源无引文（不参与核对）。",
            "条文哈希：1 条已固定并核验",
        ],
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

/// A changed pack file must be caught by both the registry lock check and the
/// import path. The copy keeps the repository untouched.
#[test]
fn a_corrupted_pack_file_fails_packs_and_load() {
    let temp = TempDir::new("official-pack-corrupt");
    copy_official_pack(temp.path());
    let theory = temp
        .path()
        .join("lawpacks/cn.constitution/constitution.std");
    let mut text = fs::read_to_string(&theory).expect("read the copied pack file");
    text.push_str("\n-- 改动：破坏锁哈希\n");
    fs::write(&theory, text).expect("write the corrupted pack file");

    let output = check(
        run_in(temp.path(), &[":packs lawpacks".to_string()]),
        ERROR,
        &["哈希不符"],
    );
    assert!(
        stderr(&output).contains("错误：1 个锁定校验错误"),
        "{}",
        stderr(&output)
    );

    let output = check_stderr(
        run_in(
            temp.path(),
            &[
                import_example().display().to_string(),
                ":why cn.constitution.不受侵犯 张三 甲宅".to_string(),
            ],
        ),
        LOAD_FAILED,
        &["哈希不符"],
    );
    assert!(
        !stdout(&output).contains("已加载"),
        "a failed import must not report a loaded theory:\n{}",
        stdout(&output)
    );
}

/// Copy the two files and the lock that make up the official pack.
fn copy_official_pack(root: &Path) {
    let source = repo_root().join("lawpacks");
    let target = root.join("lawpacks");
    copy_file(&source.join("std.lock"), &target.join("std.lock"));
    copy_file(
        &source.join("cn.constitution/lawpack.toml"),
        &target.join("cn.constitution/lawpack.toml"),
    );
    copy_file(
        &source.join("cn.constitution/constitution.std"),
        &target.join("cn.constitution/constitution.std"),
    );
}

fn copy_file(from: &Path, to: &Path) {
    if let Some(parent) = to.parent() {
        fs::create_dir_all(parent)
            .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
    }
    fs::copy(from, to)
        .unwrap_or_else(|error| panic!("copy {} to {}: {error}", from.display(), to.display()));
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cli-official-pack-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
