//! End-to-end tests for the `open` concept marker.
//!
//! The marker is declared in a case, module or pack. These tests cover what is
//! visible to a reader (`:inspect`), the closed-environment gate, pack loading,
//! and that marking a predicate does not change any derivation or certificate.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_lawpack::{build_lock, LOCK_FILE};

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

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-open-concept-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn root(&self) -> &Path {
        &self.path
    }

    fn write(&self, relative: &str, contents: &str) -> PathBuf {
        let path = self.path.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
        }
        fs::write(&path, contents)
            .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path
    }

    fn lawpacks(&self) -> PathBuf {
        self.path.join("lawpacks")
    }

    fn write_pack(&self, name: &str, manifest: &str, files: &[(&str, &str)]) {
        let dir = self.lawpacks().join(name);
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
        fs::write(dir.join("lawpack.toml"), manifest).expect("write manifest");
        for (relative, text) in files {
            let path = dir.join(relative);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent)
                    .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
            }
            fs::write(&path, text).expect("write pack theory");
        }
    }

    fn lock(&self) {
        let root = self.lawpacks();
        let lockfile = build_lock(&root).unwrap_or_else(|errors| {
            panic!(
                "build_lock failed: {}",
                errors
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("; ")
            )
        });
        lockfile
            .write(&root.join(LOCK_FILE))
            .unwrap_or_else(|error| panic!("write lock: {error}"));
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn pack_manifest(name: &str) -> String {
    format!(
        "[pack]\nname = \"{name}\"\nversion = \"0.1.0\"\n\
         jurisdiction = \"CN\"\nterritory = \"CN\"\nnamespace = \"{name}\"\n\n\
         [[files]]\npath = \"theory.std\"\nkind = \"theory\"\n"
    )
}

// ---------------------------------------------------------------------------
// `:inspect`
// ---------------------------------------------------------------------------

#[test]
fn inspect_marks_only_the_opened_predicate() {
    let temp = TempDir::new("inspect");
    let file = temp.write(
        "case.std",
        "sort 人\n\
         pred 损害 : 人 → Prop\n\
         pred 重大 : 人 → Prop\n\
         open 重大\n",
    );
    let output = check(
        run(&[file.display().to_string(), ":inspect".to_owned()]),
        PROVED,
        &["已加载"],
    );
    let out = stdout(&output);
    let pred = |name: &str| {
        out.lines()
            .find(|line| line.contains("pred") && line.contains(name))
            .unwrap_or_else(|| panic!("no predicate line for {name}:\n{out}"))
            .to_owned()
    };
    assert!(
        pred("重大").contains("〔开放概念〕"),
        "the opened predicate must carry the marker: {:?}",
        pred("重大")
    );
    assert!(
        !pred("损害").contains("〔开放概念〕"),
        "an unopened predicate must not carry the marker: {:?}",
        pred("损害")
    );
    assert!(
        out.lines().any(|line| line.contains("open:重大")),
        "the marker declaration must stay visible in the ledger:\n{out}"
    );
    assert!(
        !out.contains("[案件扩展]"),
        "a plain session must not mark case extensions:\n{out}"
    );
}

#[test]
fn a_bad_open_target_is_reported_with_its_line() {
    let temp = TempDir::new("bad-line");
    let file = temp.write("case.std", "sort 人\npred 重大 : 人 → Prop\nopen 不存在\n");
    let output = check_stderr(
        run(&[file.display().to_string()]),
        LOAD_FAILED,
        &[":3:1: error:", "未知谓词", "`不存在`"],
    );
    assert!(
        !stdout(&output).contains("已加载"),
        "a rejected file must not load:\n{}",
        stdout(&output)
    );
}

// ---------------------------------------------------------------------------
// Closed environment
// ---------------------------------------------------------------------------

#[test]
fn closed_env_rejects_a_case_open_unless_case_rules_are_allowed() {
    let temp = TempDir::new("closed");
    let file = temp.write(
        "case.std",
        "import cn.constitution\nopen cn.constitution.非法搜查\n",
    );
    let path = file.display().to_string();

    let rejected = check_stderr(
        run(&["--closed-env".to_owned(), path.clone()]),
        LOAD_FAILED,
        &[
            "封闭环境",
            "open cn.constitution.非法搜查",
            "--allow-case-rules",
        ],
    );
    assert!(!stdout(&rejected).contains("已加载"));

    let allowed = check(
        run(&[
            "--closed-env".to_owned(),
            "--allow-case-rules".to_owned(),
            path,
            ":inspect".to_owned(),
        ]),
        PROVED,
        &["已加载"],
    );
    let out = stdout(&allowed);
    let pred_line = out
        .lines()
        .find(|line| line.contains("pred") && line.contains("cn.constitution.非法搜查 :"))
        .unwrap_or_else(|| panic!("no predicate line:\n{out}"));
    assert!(
        pred_line.contains("〔开放概念〕"),
        "the predicate must be marked: {pred_line:?}"
    );
    assert!(
        !pred_line.contains("[案件扩展]"),
        "the predicate itself comes from the pack: {pred_line:?}"
    );
    let marker_line = out
        .lines()
        .find(|line| line.contains("open:cn.constitution.非法搜查"))
        .unwrap_or_else(|| panic!("no marker declaration line:\n{out}"));
    assert!(
        marker_line.contains("[案件扩展]"),
        "the case's own marker must be a case extension: {marker_line:?}"
    );
}

#[test]
fn a_pack_may_declare_an_open_concept_and_closed_env_loads_it_normally() {
    let temp = TempDir::new("pack");
    temp.write_pack(
        "pkg.open",
        &pack_manifest("pkg.open"),
        &[(
            "theory.std",
            "namespace pkg.open\n\
             sort pkg.open.人\n\
             pred pkg.open.重大 : pkg.open.人 → Prop\n\
             open pkg.open.重大\n",
        )],
    );
    temp.lock();
    let case = temp.write("case.std", "import pkg.open\n");

    let output = check(
        run_in(
            temp.root(),
            &[
                "--closed-env",
                case.to_str().expect("utf-8 path"),
                ":inspect",
            ],
        ),
        PROVED,
        &["已加载", "导入 pkg.open"],
    );
    let out = stdout(&output);
    let pred_line = out
        .lines()
        .find(|line| line.contains("pred") && line.contains("pkg.open.重大"))
        .unwrap_or_else(|| panic!("no pack predicate line:\n{out}"));
    assert!(
        pred_line.contains("〔开放概念〕"),
        "the pack predicate must be marked: {pred_line:?}"
    );
    assert!(
        pred_line.contains("[pkg.open@0.1.0]"),
        "the pack predicate must show its pack suffix: {pred_line:?}"
    );
    assert!(
        !out.contains("[案件扩展]"),
        "a pack's own marker is not a case extension:\n{out}"
    );
}

// ---------------------------------------------------------------------------
// The marker is inert
// ---------------------------------------------------------------------------

/// The same theory, with and without an `open` line: today's derivation and
/// certificate must be byte-for-byte identical. Only the load report gains the
/// marker line.
#[test]
fn opening_a_predicate_changes_neither_why_nor_cert() {
    let temp = TempDir::new("inert");
    let base = "sort 人\n\
                pred 损害 : 人 → Prop\n\
                pred 重大 : 人 → Prop\n\
                obj 甲 : 人\n\
                axiom 损害事实 : 损害 甲\n\
                  source text \"案件\" locator \"一\"\n\
                rule 重大推定 :\n\
                  params x : 人\n\
                  premise 损害 x\n\
                  conclude 重大 x\n\
                  source text \"测试\" locator \"二\"\n";
    let marked = base.replace(
        "pred 重大 : 人 → Prop\n",
        "pred 重大 : 人 → Prop\nopen 重大\n",
    );
    assert_ne!(base, marked, "the fixture must actually add the marker");
    let plain = temp.write("plain.std", base);
    let opened = temp.write("opened.std", &marked);

    for (query, start) in [(":why 重大 甲", "▸"), (":cert 重大 甲", "{")] {
        let plain_out = check(
            run(&[
                "--no-default-packs".to_owned(),
                plain.display().to_string(),
                query.to_owned(),
            ]),
            PROVED,
            &["已加载"],
        );
        let opened_out = check(
            run(&[
                "--no-default-packs".to_owned(),
                opened.display().to_string(),
                query.to_owned(),
            ]),
            PROVED,
            &["已加载", "+ open 重大"],
        );

        let plain_text = stdout(&plain_out);
        let opened_text = stdout(&opened_out);
        let tail = |text: &str| {
            let index = text
                .find(start)
                .unwrap_or_else(|| panic!("no {start:?} section in:\n{text}"));
            text[index..].to_owned()
        };
        assert_eq!(
            tail(&plain_text),
            tail(&opened_text),
            "`{query}` must be identical with and without the marker\nplain:\n{plain_text}\nopened:\n{opened_text}"
        );
    }
}
