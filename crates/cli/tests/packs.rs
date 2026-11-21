//! End-to-end tests for `:packs`.
//!
//! Every case builds its own temporary directory tree, so the tests do not
//! depend on whether the repository has a `lawpacks` directory.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const ERROR: i32 = 2;

const VALID: &str = r#"
[pack]
name = "cn.constitution"
version = "0.1.0"
jurisdiction = "CN"
territory = "CN"
effective_from = "1982-12-04"
description = "示例包"

[[files]]
path = "constitution.std"
kind = "theory"

[[files]]
path = "amendment.std"
"#;

fn run(command: &str) -> Output {
    run_in(None, command)
}

fn run_in(current_dir: Option<&Path>, command: &str) -> Output {
    let mut process = Command::new(env!("CARGO_BIN_EXE_std-deduce-cli"));
    process.arg(command);
    if let Some(dir) = current_dir {
        process.current_dir(dir);
    }
    process
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
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

#[test]
fn packs_lists_a_valid_pack() {
    let temp = TempDir::new("list");
    temp.pack("cn.constitution", VALID);
    let output = run(&format!(":packs {}", temp.path().display()));
    assert_exit(&output, PROVED);

    let out = stdout(&output);
    assert!(
        out.contains("cn.constitution 0.1.0  CN/CN  1982-12-04..未注明"),
        "{out}"
    );
    let dir = temp.path().join("cn.constitution").display().to_string();
    assert!(out.contains(&dir), "{out}");
    assert!(out.contains("  示例包"), "{out}");
    assert!(out.contains("  文件 2 个"), "{out}");
    assert!(!out.contains("没有找到法律包"), "{out}");
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn packs_accepts_a_directory_containing_spaces() {
    let temp = TempDir::new("spaces");
    let root = temp.path().join("law packs");
    temp.write_pack_at(&root, "cn.constitution", VALID);

    let output = run(&format!(":packs {}", root.display()));
    assert_exit(&output, PROVED);
    assert!(
        stdout(&output).contains("cn.constitution 0.1.0"),
        "{output:?}"
    );
}

#[test]
fn packs_lists_good_packs_and_reports_bad_manifests() {
    let temp = TempDir::new("mixed");
    temp.pack("good", VALID);
    temp.pack("bad", "[pack]\nname = \"bad.pack\"\nversion = \"1.0\"\n");

    let output = run(&format!(":packs {}", temp.path().display()));
    assert_exit(&output, ERROR);

    let out = stdout(&output);
    assert!(out.contains("cn.constitution 0.1.0"), "{out}");
    let bad = temp.path().join("bad").join("lawpack.toml");
    assert!(out.contains(&bad.display().to_string()), "{out}");
    assert!(out.contains("jurisdiction"), "{out}");
    assert!(!out.contains("没有找到法律包"), "{out}");

    let err = stderr(&output);
    assert!(err.contains("错误："), "{err}");
    assert!(err.contains("1 个法律包清单无效"), "{err}");
}

#[test]
fn packs_fails_when_the_directory_does_not_exist() {
    let temp = TempDir::new("missing");
    let missing = temp.path().join("does-not-exist");

    let output = run(&format!(":packs {}", missing.display()));
    assert_exit(&output, ERROR);
    assert!(stdout(&output).is_empty(), "{}", stdout(&output));

    let err = stderr(&output);
    assert!(err.contains(&missing.display().to_string()), "{err}");
    assert!(err.contains("无法读取法律包目录"), "{err}");
}

#[test]
fn packs_empty_directory_succeeds_and_says_none() {
    let temp = TempDir::new("empty");
    let output = run(&format!(":packs {}", temp.path().display()));
    assert_exit(&output, PROVED);
    assert!(stdout(&output).contains("没有找到法律包。"), "{output:?}");
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn packs_ignores_directories_without_a_manifest() {
    let temp = TempDir::new("no-manifest");
    temp.empty_dir("not-a-pack");
    fs::write(temp.path().join("README.md"), "not a pack").unwrap();

    let output = run(&format!(":packs {}", temp.path().display()));
    assert_exit(&output, PROVED);
    assert!(stdout(&output).contains("没有找到法律包。"), "{output:?}");
}

#[test]
fn packs_defaults_to_lawpacks_in_the_current_directory() {
    let temp = TempDir::new("default");
    temp.pack("lawpacks/cn.constitution", VALID);

    let output = run_in(Some(temp.path()), ":packs");
    assert_exit(&output, PROVED);
    assert!(
        stdout(&output).contains("cn.constitution 0.1.0"),
        "{output:?}"
    );
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cli-packs-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn pack(&self, name: &str, manifest: &str) {
        self.write_pack_at(&self.path, name, manifest);
    }

    fn write_pack_at(&self, root: &Path, name: &str, manifest: &str) {
        let dir = root.join(name);
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
        fs::write(dir.join("lawpack.toml"), manifest)
            .unwrap_or_else(|error| panic!("write manifest: {error}"));
    }

    fn empty_dir(&self, name: &str) {
        let dir = self.path.join(name);
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
