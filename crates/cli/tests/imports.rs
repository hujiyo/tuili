//! End-to-end tests for registry-backed `import`.
//!
//! Every test builds a temporary `lawpacks` registry below its own temporary
//! root and runs the CLI with that root as its current directory. No test
//! depends on the repository's `lawpacks` directory or on the working
//! directory the test runner was started from.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_lawpack::{build_lock, Lockfile, LOCK_FILE};

const VERSION: &str = "0.1.0";
const PROVED: i32 = 0;
const FAILED: i32 = 1;
const ERROR: i32 = 2;

fn manifest(name: &str, namespace: Option<&str>, files: &[(&str, &str)]) -> String {
    let mut text = format!(
        "[pack]\nname = \"{name}\"\nversion = \"{VERSION}\"\n\
         jurisdiction = \"CN\"\nterritory = \"CN\"\n"
    );
    if let Some(namespace) = namespace {
        text.push_str(&format!("namespace = \"{namespace}\"\n"));
    }
    for (path, kind) in files {
        text.push_str("\n[[files]]\n");
        text.push_str(&format!("path = \"{path}\"\n"));
        if !kind.is_empty() {
            text.push_str(&format!("kind = \"{kind}\"\n"));
        }
    }
    text
}

fn theory(namespace: &str) -> String {
    format!(
        r#"
namespace {namespace}
sort {namespace}.公民
sort {namespace}.住宅
pred {namespace}.非法搜查 : {namespace}.公民 → {namespace}.住宅 → Prop
pred {namespace}.不受侵犯 : {namespace}.公民 → {namespace}.住宅 → Prop
rule {namespace}.非法搜查即侵犯 :
  params p : {namespace}.公民, h : {namespace}.住宅
  premise {namespace}.非法搜查 p h
  conclude {namespace}.不受侵犯 p h
  source text "测试" locator "一"
"#
    )
}

fn case_source(imports: &[&str], namespace: &str) -> String {
    let mut text = String::new();
    for import in imports {
        text.push_str(&format!("import {import}\n"));
    }
    text.push_str(&format!(
        r#"
obj 张三 : {namespace}.公民
obj 甲宅 : {namespace}.住宅
axiom 事实 : {namespace}.非法搜查 张三 甲宅
  source text "案件" locator "一"
"#
    ));
    text
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cli-imports-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn root(&self) -> &Path {
        &self.path
    }

    fn lawpacks(&self) -> PathBuf {
        self.path.join("lawpacks")
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

    fn write_bytes(&self, relative: &str, bytes: &[u8]) -> PathBuf {
        let path = self.path.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
        }
        fs::write(&path, bytes).unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path
    }

    fn write_pack(&self, name: &str, manifest: &str, files: &[(&str, &str)]) -> PathBuf {
        let dir = self.lawpacks().join(name);
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
        fs::write(dir.join("lawpack.toml"), manifest)
            .unwrap_or_else(|error| panic!("write manifest: {error}"));
        for (relative, text) in files {
            let path = dir.join(relative);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent)
                    .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
            }
            fs::write(&path, text)
                .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        }
        dir
    }

    fn package(&self, name: &str, namespace: &str, source: &str) -> PathBuf {
        self.write_pack(
            name,
            &manifest(name, Some(namespace), &[("theory.std", "theory")]),
            &[("theory.std", source)],
        )
    }

    /// Hash every pack and write `<root>/lawpacks/std.lock`; panic on errors.
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

    fn lockfile(&self) -> Lockfile {
        Lockfile::read(&self.lawpacks().join(LOCK_FILE)).expect("the lock exists")
    }

    fn write_lockfile(&self, lockfile: &Lockfile) {
        lockfile
            .write(&self.lawpacks().join(LOCK_FILE))
            .expect("write lock");
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn run_in(current_dir: &Path, args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(current_dir)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn run_repl_in(current_dir: &Path, input: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(current_dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"));
    child
        .stdin
        .take()
        .expect("stdin is piped")
        .write_all(input.as_bytes())
        .expect("write REPL input");
    child
        .wait_with_output()
        .unwrap_or_else(|error| panic!("failed to wait for the CLI: {error}"))
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

fn line_index(out: &str, prefix: &str) -> usize {
    out.lines()
        .position(|line| line.starts_with(prefix))
        .unwrap_or_else(|| panic!("no output line starts with {prefix:?}\n{out}"))
}

#[test]
fn a_locked_package_can_be_imported_and_proven() {
    let temp = TempDir::new("basic");
    temp.package("pkg.a", "pkg.a", &theory("pkg.a"));
    temp.lock();
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", case.display()),
            ":inspect".to_string(),
            ":why pkg.a.不受侵犯 张三 甲宅".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let err = stderr(&output);
    assert!(err.is_empty(), "{err}");
    assert!(
        out.contains("[pkg.a@0.1.0]"),
        "a package declaration must show its pack and version:\n{out}"
    );
    let case_obj = out
        .lines()
        .find(|line| line.contains("obj   张三"))
        .unwrap_or_else(|| panic!("no case declaration line:\n{out}"));
    assert!(
        !case_obj.contains('['),
        "a case declaration must have no suffix: {case_obj:?}"
    );
    assert!(
        out.contains("推导已通过独立校验。"),
        "the imported rule must prove the case goal:\n{out}"
    );
}

#[test]
fn a_file_without_import_never_needs_a_registry() {
    let temp = TempDir::new("no-registry");
    let plain = temp.write(
        "plain.std",
        "sort 人\npred 好人 : 人 → Prop\nobj 张三 : 人\naxiom 张三好 : 好人 张三\n  source text \"案件\" locator \"一\"\n",
    );

    let output = run_in(
        temp.root(),
        &[format!(":load {}", plain.display()), ":inspect".to_string()],
    );
    assert_exit(&output, PROVED);
    assert!(
        !temp.lawpacks().exists(),
        "a file without import must not create or require lawpacks"
    );
    assert!(stdout(&output).contains("张三好"), "{}", stdout(&output));
}

#[test]
fn a_missing_lock_fails_both_entry_points() {
    let temp = TempDir::new("missing-lock");
    temp.package("pkg.a", "pkg.a", &theory("pkg.a"));
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));

    let explicit = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&explicit, ERROR);
    let err = stderr(&explicit);
    assert!(err.contains("std.lock"), "{err}");
    assert!(err.contains("没有 std.lock"), "{err}");
    assert!(err.contains(": error:"), "{err}");

    let batch = run_in(temp.root(), &[case.display().to_string()]);
    assert_exit(&batch, FAILED);
    let err = stderr(&batch);
    assert!(err.contains("没有 std.lock"), "{err}");
    assert!(
        !err.contains("错误："),
        "batch diagnostics add no prefix: {err}"
    );
}

#[test]
fn every_hash_mismatch_is_reported() {
    let temp = TempDir::new("hash-mismatch");
    temp.package("pkg.a", "pkg.a", &theory("pkg.a"));
    temp.package("pkg.b", "pkg.b", &theory("pkg.b"));
    temp.lock();
    // Change both packs after locking; even though the case imports only one,
    // verifying the registry must report both mismatches.
    fs::write(
        temp.lawpacks().join("pkg.a/theory.std"),
        format!("{}\n", theory("pkg.a")),
    )
    .unwrap();
    fs::write(
        temp.lawpacks().join("pkg.b/theory.std"),
        format!("{}\n", theory("pkg.b")),
    )
    .unwrap();
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));

    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert_eq!(err.matches("哈希不符").count(), 2, "{err}");
    assert!(err.contains("pkg.a"), "{err}");
    assert!(err.contains("pkg.b"), "{err}");
    assert!(err.matches("sha256:").count() >= 4, "{err}");
}

#[test]
fn a_lock_missing_a_pack_or_listing_an_extra_one_fails() {
    let missing = TempDir::new("lock-missing-pack");
    missing.package("pkg.a", "pkg.a", &theory("pkg.a"));
    missing.package("pkg.b", "pkg.b", &theory("pkg.b"));
    missing.lock();
    fs::remove_dir_all(missing.lawpacks().join("pkg.b")).unwrap();
    let case = missing.write("case.std", &case_source(&["pkg.a"], "pkg.a"));
    let output = run_in(missing.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("pkg.b") && err.contains("不存在"), "{err}");

    let extra = TempDir::new("lock-extra-pack");
    extra.package("pkg.a", "pkg.a", &theory("pkg.a"));
    extra.lock();
    extra.package("pkg.b", "pkg.b", &theory("pkg.b"));
    let case = extra.write("case.std", &case_source(&["pkg.a"], "pkg.a"));
    let output = run_in(extra.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("pkg.b") && err.contains("未锁定"), "{err}");
}

#[test]
fn a_version_mismatch_fails_with_both_versions() {
    let temp = TempDir::new("version-mismatch");
    temp.package("pkg.a", "pkg.a", &theory("pkg.a"));
    temp.lock();
    let mut lockfile = temp.lockfile();
    lockfile.pack[0].version = "9.9.9".to_owned();
    temp.write_lockfile(&lockfile);
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));

    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("版本不符"), "{err}");
    assert!(err.contains("9.9.9") && err.contains(VERSION), "{err}");
}

#[test]
fn a_bad_manifest_in_the_registry_fails_the_whole_load() {
    let temp = TempDir::new("scan-error");
    temp.package("pkg.a", "pkg.a", &theory("pkg.a"));
    temp.lock();
    let broken = temp.write(
        "lawpacks/broken/lawpack.toml",
        "[pack]\nname = \"broken\"\nversion = \"1.0\"\n",
    );
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));

    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(
        err.contains("broken") && err.contains("lawpack.toml"),
        "the bad manifest path must be named ({broken:?}): {err}"
    );
    assert!(err.contains("jurisdiction"), "{err}");
}

#[test]
fn duplicate_pack_names_are_rejected() {
    let temp = TempDir::new("duplicate-name");
    temp.package("pkg.a", "pkg.a", &theory("pkg.a"));
    temp.lock();
    temp.write_pack(
        "two",
        &manifest("pkg.a", Some("pkg.a"), &[("theory.std", "theory")]),
        &[("theory.std", &theory("pkg.a"))],
    );
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));

    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("重复"), "{err}");
    assert!(err.contains("pkg.a"), "{err}");
}

#[test]
fn duplicate_namespaces_are_rejected() {
    let temp = TempDir::new("duplicate-namespace");
    temp.package("pkg.a", "pkg.a", &theory("pkg.a"));
    temp.write_pack(
        "pkg.b",
        &manifest("pkg.b", Some("pkg.a"), &[("theory.std", "theory")]),
        &[("theory.std", &theory("pkg.a"))],
    );
    temp.lock();
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));

    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("namespace `pkg.a`"), "{err}");
    assert!(err.contains("重复"), "{err}");
}

#[test]
fn a_missing_registry_names_the_expected_path() {
    let temp = TempDir::new("missing-registry");
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));

    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("lawpacks"), "{err}");
    assert!(err.contains("无法读取法律包目录"), "{err}");
}

#[test]
fn an_import_of_an_absent_package_names_it_and_the_registry() {
    let temp = TempDir::new("missing-package");
    temp.package("pkg.a", "pkg.a", &theory("pkg.a"));
    temp.lock();
    let case = temp.write("case.std", &case_source(&["pkg.missing"], "pkg.a"));

    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("pkg.missing"), "{err}");
    assert!(err.contains("lawpacks"), "{err}");
}

#[test]
fn two_packages_with_the_same_short_names_resolve_qualified_names() {
    let temp = TempDir::new("same-suffix");
    temp.package("pkg.a", "pkg.a", &theory("pkg.a"));
    temp.package("pkg.b", "pkg.b", &theory("pkg.b"));
    temp.lock();
    let case = temp.write(
        "case.std",
        r#"
import pkg.a
import pkg.b
obj 张三 : pkg.a.公民
obj 甲宅 : pkg.a.住宅
obj 李四 : pkg.b.公民
obj 乙宅 : pkg.b.住宅
axiom 甲事实 : pkg.a.非法搜查 张三 甲宅
  source text "案件" locator "一"
axiom 乙事实 : pkg.b.非法搜查 李四 乙宅
  source text "案件" locator "二"
"#,
    );

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", case.display()),
            ":inspect".to_string(),
            ":why pkg.a.不受侵犯 张三 甲宅".to_string(),
            ":why pkg.b.不受侵犯 李四 乙宅".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains("[pkg.a@0.1.0]"), "{out}");
    assert!(out.contains("[pkg.b@0.1.0]"), "{out}");
    assert_eq!(
        out.matches("推导已通过独立校验。").count(),
        2,
        "both qualified goals must prove:\n{out}"
    );
    assert!(
        out.contains("缺：pkg.a.非法搜查") || out.contains("▸ pkg.a.不受侵犯"),
        "{out}"
    );
}

#[test]
fn a_package_dependency_is_loaded_before_its_importer() {
    let temp = TempDir::new("dependency");
    temp.package(
        "pkg.b",
        "pkg.b",
        r#"
namespace pkg.b
sort pkg.b.公民
obj pkg.b.张三 : pkg.b.公民
pred pkg.b.守法 : pkg.b.公民 → Prop
axiom pkg.b.张三守法 : pkg.b.守法 pkg.b.张三
  source text "测试" locator "一"
"#,
    );
    temp.write_pack(
        "pkg.a",
        &manifest("pkg.a", Some("pkg.a"), &[("theory.std", "theory")]),
        &[(
            "theory.std",
            r#"
import pkg.b
namespace pkg.a
axiom pkg.a.可以 : pkg.b.守法 pkg.b.张三
  source text "测试" locator "二"
"#,
        )],
    );
    temp.lock();
    let case = temp.write("case.std", "import pkg.a\n#check pkg.a.可以\n");

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", case.display()),
            ":inspect".to_string(),
            ":why pkg.b.守法 pkg.b.张三".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let dependency = line_index(&out, "  pred  pkg.b.守法");
    let importer = line_index(&out, "  axiom pkg.a.可以");
    assert!(
        dependency < importer,
        "a dependency's declarations must be loaded before the importer's:\n{out}"
    );
    assert!(out.contains("[pkg.a@0.1.0]"), "{out}");
    assert!(out.contains("[pkg.b@0.1.0]"), "{out}");
    assert!(out.contains("推导已通过独立校验。"), "{out}");
}

#[test]
fn a_dependency_shared_by_two_packages_is_loaded_once() {
    let temp = TempDir::new("shared-dependency");
    temp.package("pkg.c", "pkg.c", &theory("pkg.c"));
    for package in ["pkg.a", "pkg.b"] {
        temp.write_pack(
            package,
            &manifest(package, Some(package), &[("theory.std", "theory")]),
            &[(
                "theory.std",
                &format!("import pkg.c\nnamespace {package}\nsort {package}.公民\n"),
            )],
        );
    }
    temp.lock();
    let case = temp.write("case.std", "import pkg.a\nimport pkg.b\n");

    let output = run_in(
        temp.root(),
        &[format!(":load {}", case.display()), ":inspect".to_string()],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert_eq!(
        out.matches("sort  pkg.c.公民").count(),
        1,
        "a dependency shared by two packages must be loaded once:\n{out}"
    );
    assert!(out.contains("[pkg.a@0.1.0]"), "{out}");
    assert!(out.contains("[pkg.b@0.1.0]"), "{out}");
}

#[test]
fn the_same_package_can_be_imported_by_a_later_load() {
    let temp = TempDir::new("reimport");
    temp.package("pkg.a", "pkg.a", &theory("pkg.a"));
    temp.lock();
    let first = temp.write("first.std", "import pkg.a\nobj 张三 : pkg.a.公民\n");
    let second = temp.write("second.std", "import pkg.a\nobj 甲宅 : pkg.a.住宅\n");

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", first.display()),
            format!(":load {}", second.display()),
            ":inspect".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert_eq!(
        out.matches("sort  pkg.a.公民").count(),
        1,
        "a package loaded in an earlier command must not be loaded twice:\n{out}"
    );
    assert!(out.contains("obj   张三 : pkg.a.公民"), "{out}");
    assert!(out.contains("obj   甲宅 : pkg.a.住宅"), "{out}");
    assert_eq!(out.matches("已加载").count(), 2, "{out}");
}

#[test]
fn a_dependency_cycle_names_the_cycle() {
    let temp = TempDir::new("cycle");
    temp.write_pack(
        "pkg.a",
        &manifest("pkg.a", Some("pkg.a"), &[("theory.std", "theory")]),
        &[(
            "theory.std",
            "import pkg.b\nnamespace pkg.a\nsort pkg.a.公民\n",
        )],
    );
    temp.write_pack(
        "pkg.b",
        &manifest("pkg.b", Some("pkg.b"), &[("theory.std", "theory")]),
        &[(
            "theory.std",
            "import pkg.a\nnamespace pkg.b\nsort pkg.b.公民\n",
        )],
    );
    temp.lock();
    let case = temp.write("case.std", "import pkg.a\nsort 案件\n");

    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("成环"), "{err}");
    assert!(
        err.contains("pkg.a") && err.contains("pkg.b"),
        "the cycle must name both packages: {err}"
    );
}

#[test]
fn bad_theory_paths_are_rejected() {
    // `..` escapes the pack directory.
    let traversal = TempDir::new("path-parent");
    traversal.write_pack(
        "pkg.a",
        &manifest("pkg.a", Some("pkg.a"), &[("../outside.std", "theory")]),
        &[],
    );
    traversal.lock();
    let case = traversal.write("case.std", &case_source(&["pkg.a"], "pkg.a"));
    let output = run_in(traversal.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    assert!(stderr(&output).contains("`..`"), "{}", stderr(&output));

    // An absolute path is not a manifest-relative path.
    let absolute = TempDir::new("path-absolute");
    let outside = absolute.root().join("outside.std");
    let raw = outside.to_string_lossy().replace('\\', "/");
    absolute.write_pack("pkg.a", &manifest("pkg.a", Some("pkg.a"), &[]), &[]);
    let manifest_path = absolute.lawpacks().join("pkg.a/lawpack.toml");
    fs::write(
        &manifest_path,
        format!(
            "[pack]\nname = \"pkg.a\"\nversion = \"{VERSION}\"\n\
             jurisdiction = \"CN\"\nterritory = \"CN\"\nnamespace = \"pkg.a\"\n\n\
             [[files]]\npath = \"{raw}\"\nkind = \"theory\"\n"
        ),
    )
    .unwrap();
    absolute.lock();
    let case = absolute.write("case.std", &case_source(&["pkg.a"], "pkg.a"));
    let output = run_in(absolute.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    assert!(stderr(&output).contains("相对路径"), "{}", stderr(&output));
}

#[test]
fn a_missing_or_non_utf8_theory_file_is_rejected() {
    let missing = TempDir::new("theory-missing");
    missing.write_pack(
        "pkg.a",
        &manifest("pkg.a", Some("pkg.a"), &[("missing.std", "theory")]),
        &[],
    );
    missing.lock();
    let case = missing.write("case.std", &case_source(&["pkg.a"], "pkg.a"));
    let output = run_in(missing.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("missing.std"), "{err}");
    assert!(err.contains("无法读取"), "{err}");

    let binary = TempDir::new("theory-binary");
    binary.package("pkg.a", "pkg.a", &theory("pkg.a"));
    binary.write_bytes("lawpacks/pkg.a/theory.std", &[0xff, 0xfe, 0x00, 0x80]);
    binary.lock();
    let case = binary.write("case.std", &case_source(&["pkg.a"], "pkg.a"));
    let output = run_in(binary.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    assert!(stderr(&output).contains("UTF-8"), "{}", stderr(&output));
}

#[test]
fn a_symlinked_theory_file_is_rejected() {
    let temp = TempDir::new("theory-symlink");
    let pack = temp.package("pkg.a", "pkg.a", &theory("pkg.a"));
    temp.lock();
    let target = temp.root().join("outside.std");
    fs::write(&target, theory("pkg.a")).unwrap();
    let link = pack.join("theory.std");
    fs::remove_file(&link).unwrap();
    if !create_file_symlink(&target, &link) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));
    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    assert!(stderr(&output).contains("符号链接"), "{}", stderr(&output));
}

#[test]
fn a_duplicate_or_missing_theory_path_is_rejected() {
    let duplicate = TempDir::new("theory-duplicate");
    duplicate.write_pack(
        "pkg.a",
        &format!(
            "{}\n[[files]]\npath = \"theory.std\"\nkind = \"theory\"\n",
            manifest("pkg.a", Some("pkg.a"), &[("theory.std", "theory")])
        ),
        &[("theory.std", &theory("pkg.a"))],
    );
    duplicate.lock();
    let case = duplicate.write("case.std", &case_source(&["pkg.a"], "pkg.a"));
    let output = run_in(duplicate.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    assert!(stderr(&output).contains("重复"), "{}", stderr(&output));

    let missing_path = TempDir::new("theory-no-path");
    missing_path.write_pack(
        "pkg.a",
        &format!(
            "[pack]\nname = \"pkg.a\"\nversion = \"{VERSION}\"\n\
             jurisdiction = \"CN\"\nterritory = \"CN\"\nnamespace = \"pkg.a\"\n\n\
             [[files]]\nkind = \"theory\"\n"
        ),
        &[],
    );
    missing_path.lock();
    let case = missing_path.write("case.std", &case_source(&["pkg.a"], "pkg.a"));
    let output = run_in(missing_path.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    assert!(stderr(&output).contains("缺少 path"), "{}", stderr(&output));
}

#[test]
fn non_theory_files_are_not_loaded() {
    let temp = TempDir::new("non-theory");
    temp.write_pack(
        "pkg.a",
        &manifest(
            "pkg.a",
            Some("pkg.a"),
            &[("theory.std", "theory"), ("missing-corpus.json", "corpus")],
        ),
        &[("theory.std", &theory("pkg.a"))],
    );
    temp.lock();
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));
    let output = run_in(
        temp.root(),
        &[format!(":load {}", case.display()), ":inspect".to_string()],
    );
    assert_exit(&output, PROVED);
    assert!(
        stdout(&output).contains("[pkg.a@0.1.0]"),
        "{}",
        stdout(&output)
    );
}

#[test]
fn a_pack_without_a_namespace_cannot_be_imported() {
    let temp = TempDir::new("no-namespace");
    temp.write_pack(
        "pkg.a",
        &manifest("pkg.a", None, &[("theory.std", "theory")]),
        &[("theory.std", &theory("pkg.a"))],
    );
    temp.lock();
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));

    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("namespace"), "{err}");
    assert!(err.contains("不能导入"), "{err}");
}

#[test]
fn a_theory_file_must_declare_the_manifest_namespace() {
    let temp = TempDir::new("namespace-mismatch");
    temp.package("pkg.a", "pkg.a", &theory("pkg.other"));
    temp.lock();
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));

    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("pkg.other"), "{err}");
    assert!(err.contains("pkg.a"), "{err}");
    assert!(err.contains("不一致"), "{err}");
    assert!(err.contains("theory.std"), "{err}");
}

#[test]
fn a_pack_without_theory_files_cannot_be_imported() {
    let temp = TempDir::new("no-theory");
    temp.write_pack(
        "pkg.a",
        &manifest("pkg.a", Some("pkg.a"), &[("corpus.json", "corpus")]),
        &[("corpus.json", "{}")],
    );
    temp.lock();
    let case = temp.write("case.std", &case_source(&["pkg.a"], "pkg.a"));

    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    assert!(
        stderr(&output).contains("没有可导入的 theory 文件"),
        "{}",
        stderr(&output)
    );
}

#[test]
fn a_failed_load_rolls_back_both_declarations_and_pack_information() {
    let temp = TempDir::new("transaction");
    temp.package("pkg.c", "pkg.c", &theory("pkg.c"));
    temp.write_pack(
        "pkg.bad",
        &manifest("pkg.bad", Some("pkg.bad"), &[("theory.std", "theory")]),
        &[(
            "theory.std",
            "namespace pkg.bad\nsort pkg.bad.公民\nthis is not a declaration\n",
        )],
    );
    temp.lock();

    // This file imports a good package and then a package whose theory file
    // fails to parse, after the good package has already been loaded.
    let bad_package = temp.write(
        "bad-package.std",
        &format!(
            "import pkg.c\nimport pkg.bad\n{}",
            case_source(&[], "pkg.c")
        ),
    );
    // This file imports a good package, then fails in `Library::load` itself.
    let bad_top = temp.write("bad-top.std", "import pkg.c\n#show pkg.c.不存在\n");
    let good = temp.write(
        "good.std",
        &format!("import pkg.c\n{}", case_source(&[], "pkg.c")),
    );

    let input = format!(
        ":load {}\n:inspect\n:load {}\n:inspect\n:load {}\n:inspect\n:quit\n",
        bad_package.display(),
        bad_top.display(),
        good.display()
    );
    let output = run_repl_in(temp.root(), &input);
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    let final_load = out
        .find("已加载")
        .unwrap_or_else(|| panic!("the final load must succeed:\n{out}"));
    assert!(
        !out[..final_load].contains("pkg.c.公民"),
        "a failed load must not keep a half-loaded package:\n{out}"
    );
    assert!(
        out[final_load..].contains("pkg.c.公民"),
        "the session must still be able to load the package afterwards:\n{out}"
    );
    assert!(
        out[final_load..].contains("[pkg.c@0.1.0]"),
        "the successful load must record package information:\n{out}"
    );
    assert!(out.matches("已加载").count() == 1, "{out}");
}

#[test]
fn a_namespaced_module_loaded_by_path_still_shows_a_bare_namespace() {
    let temp = TempDir::new("bare-namespace");
    let module = temp.write("module.std", "namespace plain\nsort plain.公民\n");

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", module.display()),
            ":inspect".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let line = out
        .lines()
        .find(|line| line.trim_start().starts_with("sort  plain.公民"))
        .unwrap_or_else(|| panic!("no module declaration:\n{out}"));
    assert!(line.trim_end().ends_with("[plain]"), "{line:?}");
    assert!(!line.contains('@'), "{line:?}");
}

#[cfg(unix)]
fn create_file_symlink(target: &Path, link: &Path) -> bool {
    std::os::unix::fs::symlink(target, link).is_ok()
}

#[cfg(windows)]
fn create_file_symlink(target: &Path, link: &Path) -> bool {
    std::os::windows::fs::symlink_file(target, link).is_ok()
}

#[cfg(not(any(unix, windows)))]
fn create_file_symlink(_target: &Path, _link: &Path) -> bool {
    false
}
