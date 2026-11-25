//! End-to-end tests for `interpret`: loading, `:inspect`, the closed
//! environment, and the fact that a loaded interpretation changes nothing yet.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const LOAD_FAILED: i32 = 1;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn run(args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn run_in(current_dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(current_dir)
        .args(args)
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

fn check(output: Output, expected: i32, needles: &[&str]) -> Output {
    assert_exit(&output, expected);
    let out = stdout(&output);
    let err = stderr(&output);
    for needle in needles {
        assert!(
            out.contains(needle),
            "stdout does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

fn check_stderr(output: Output, expected: i32, needles: &[&str]) -> Output {
    assert_exit(&output, expected);
    let out = stdout(&output);
    let err = stderr(&output);
    for needle in needles {
        assert!(
            err.contains(needle),
            "stderr does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

fn line_with<'a>(out: &'a str, needle: &str) -> &'a str {
    out.lines()
        .find(|line| line.contains(needle))
        .unwrap_or_else(|| panic!("no output line contains {needle:?}\n{out}"))
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-interpretation-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn write(&self, name: &str, contents: &str) -> PathBuf {
        let path = self.path.join(name);
        fs::write(&path, contents)
            .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

const MODULE: &str = r#"
namespace a
pred a.P : Prop
pred a.Q : Prop
interpret a.i : a.P → a.Q
  direction analogy
  source text "解释文本" locator "第一条" version "2020"
"#;

#[test]
fn inspect_shows_an_interpretation_with_direction_and_sources() {
    let temp = TempDir::new("inspect");
    let module = temp.write("module.std", MODULE);
    let output = check(
        run(&[
            "--no-default-packs".to_owned(),
            module.display().to_string(),
            ":inspect".to_owned(),
        ]),
        PROVED,
        &["已加载", "interpret a.i"],
    );
    let out = stdout(&output);
    let line = line_with(&out, "interpret a.i :");
    assert!(
        line.contains("a.P → a.Q 〔方向 analogy〕"),
        "direction missing from the ledger line: {line:?}"
    );
    assert!(
        line.contains("〔来源 「解释文本第一条」（2020）〕"),
        "source summary missing from the ledger line: {line:?}"
    );
    assert!(
        line.trim_end().ends_with("[a]"),
        "a module interpretation must name its namespace: {line:?}"
    );
    assert!(
        !out.contains("interp a.i"),
        "the old opaque kind label must be gone:\n{out}"
    );
    // The full source fields are still printed below the ledger line.
    assert!(
        out.contains("条号：第一条"),
        "full source fields missing:\n{out}"
    );
    assert!(
        out.contains("版本：2020"),
        "full source fields missing:\n{out}"
    );
}

#[test]
fn inspect_escapes_interpretation_source_fields() {
    let temp = TempDir::new("escape");
    let module = temp.write(
        "module.std",
        "namespace a\npred a.P : Prop\npred a.Q : Prop\n\
         interpret a.i : a.P → a.Q\n  direction literal\n\
         \x20 source text \"解释\\n出处\u{202E}\" locator \"第一条\" version \"2020\"\n",
    );
    let output = check(
        run(&[
            "--no-default-packs".to_owned(),
            module.display().to_string(),
            ":inspect".to_owned(),
        ]),
        PROVED,
        &["interpret a.i :"],
    );
    let out = stdout(&output);
    let line = line_with(&out, "interpret a.i :");
    assert!(
        line.contains("解释\\n出处\\u{202E}第一条"),
        "the inline source must be escaped: {line:?}"
    );
    assert!(
        !line.contains('\u{202E}'),
        "a bidi override must not reach the ledger line: {line:?}"
    );
    assert!(
        line.contains("\\n"),
        "a newline in a source field must be escaped: {line:?}"
    );
    assert!(
        !out.contains('\u{202E}'),
        "a bidi override must not reach stdout:\n{out}"
    );
}

#[test]
fn closed_env_rejects_a_case_interpretation_unless_allowed() {
    let temp = TempDir::new("closed");
    let case = temp.write(
        "case.std",
        "import cn.constitution\nobj 张三 : cn.constitution.人\n\
         interpret 国籍解释 : cn.constitution.中国国籍 张三 → cn.constitution.公民 张三\n\
         \x20 direction literal\n  source text \"测试\" locator \"一\" version \"2020\"\n",
    );
    let path = case.display().to_string();

    let rejected = check_stderr(
        run(&["--closed-env".to_owned(), path.clone()]),
        LOAD_FAILED,
        &["封闭环境", "interpret 国籍解释", "--allow-case-rules"],
    );
    assert!(
        !stdout(&rejected).contains("已加载"),
        "a rejected case must not be loaded:\n{}",
        stdout(&rejected)
    );

    let allowed = check(
        run(&[
            "--closed-env".to_owned(),
            "--allow-case-rules".to_owned(),
            path,
            ":inspect".to_owned(),
        ]),
        PROVED,
        &["interpret 国籍解释 :"],
    );
    let out = stdout(&allowed);
    let line = line_with(&out, "interpret 国籍解释 :");
    assert!(
        line.contains("〔方向 literal〕"),
        "direction missing: {line:?}"
    );
    assert!(
        line.trim_end().ends_with("[案件扩展]"),
        "a case interpretation must be marked as a case extension: {line:?}"
    );
}

#[test]
fn an_imported_pack_interpretation_is_loaded_and_marked_with_its_pack() {
    let root = TempDir::new("pack");
    let pack = root.path.join("lawpacks").join("pkg.community");
    fs::create_dir_all(&pack).unwrap();
    fs::write(
        pack.join("lawpack.toml"),
        "[pack]\nname = \"pkg.community\"\nversion = \"0.1.0\"\n\
         jurisdiction = \"CN\"\nterritory = \"CN\"\nnamespace = \"pkg.community\"\n\
         trust = \"community\"\n\n[[files]]\npath = \"theory.std\"\nkind = \"theory\"\n",
    )
    .unwrap();
    fs::write(
        pack.join("theory.std"),
        "namespace pkg.community\npred pkg.community.P : Prop\n\
         pred pkg.community.Q : Prop\n\
         interpret pkg.community.解释 : pkg.community.P → pkg.community.Q\n\
         \x20 direction expand\n\
         \x20 source text \"测试\" locator \"二\" version \"2020\"\n",
    )
    .unwrap();
    let lockfile = std_deduce_lawpack::build_lock(&root.path.join("lawpacks"))
        .expect("the temporary registry is sound");
    lockfile
        .write(
            &root
                .path
                .join("lawpacks")
                .join(std_deduce_lawpack::LOCK_FILE),
        )
        .expect("write the lock");
    root.write("case.std", "import pkg.community\n");

    let output = check(
        run_in(&root.path, &["--no-default-packs", "case.std", ":inspect"]),
        PROVED,
        &["导入 pkg.community", "interpret pkg.community.解释 :"],
    );
    let out = stdout(&output);
    let line = line_with(&out, "interpret pkg.community.解释 :");
    assert!(
        line.contains("〔方向 expand〕"),
        "direction missing: {line:?}"
    );
    assert!(
        line.trim_end().ends_with("[pkg.community@0.1.0]"),
        "a pack interpretation must name its pack: {line:?}"
    );
}

#[test]
fn a_loaded_interpretation_does_not_change_a_derivation() {
    let temp = TempDir::new("inert");
    let case = temp.write(
        "case.std",
        "sort 人\npred P : 人 → Prop\npred Q : 人 → Prop\nobj 张三 : 人\n\
         axiom 事实 : P 张三\n  source text \"案情\" locator \"一\"\n\
         rule 规则 :\n  params x : 人\n  premise P x\n  conclude Q x\n\
         \x20 source text \"案情\" locator \"二\"\n\
         interpret 解释 : P 张三 → Q 张三\n  direction literal\n\
         \x20 source text \"解释\" locator \"一\" version \"2020\"\n",
    );
    let output = check(
        run(&[
            "--no-default-packs".to_owned(),
            case.display().to_string(),
            ":why Q 张三".to_owned(),
        ]),
        PROVED,
        &["▸ Q 张三", "推导已通过独立校验。", "+ 解释"],
    );
    let out = stdout(&output);
    // The inert interpretation is loaded but is not a derivation step: it does
    // not appear in the tree below the root.
    let tree = out
        .split_once("▸ Q 张三")
        .map(|(_, tree)| tree)
        .unwrap_or_else(|| panic!("no derivation tree:\n{out}"));
    assert!(
        !tree.contains("解释"),
        "an interpretation must not enter the derivation:\n{out}"
    );
}
