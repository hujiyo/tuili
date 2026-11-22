//! End-to-end tests for `:packs`.
//!
//! Every case builds its own temporary directory tree, so the tests do not
//! depend on whether the repository has a `lawpacks` directory.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_kernel::env::escape_control;

const PROVED: i32 = 0;
const ERROR: i32 = 2;

/// Printed by `:packs` when the directory has no `std.lock`.
const UNLOCKED: &str = "锁定校验：未找到 std.lock（未锁定）";
/// Printed by `:packs` when the listing failed, so the lock was not checked.
const LOCK_NOT_RUN: &str = "锁定校验：未运行（清单错误）";

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

const OTHER: &str = r#"
[pack]
name = "cn.civil-code"
version = "2.0"
jurisdiction = "CN"
territory = "CN"
"#;

/// A five-article v2 coverage ledger covering every status and two gaps.
const CORPUS_V2: &str = r#"{
  "format": 2,
  "law": "cn.test",
  "title": "测试法",
  "aliases": [],
  "version": "2018",
  "jurisdiction": "CN",
  "coverage": {
    "open_concepts": ["甲", "乙", "丙", "丁", "戊"],
    "notes": "口径",
    "gaps": {
      "state_organs": "国家机关",
      "kinship": "亲属关系"
    },
    "articles": [
      { "number": "第一条", "status": "formalized", "rules": ["cn.test.规则一"] },
      { "number": "第二条", "status": "partial", "rules": ["cn.test.规则二"], "note": "未建模" },
      { "number": "第三条", "status": "indexed" },
      { "number": "第四条", "status": "needs_ontology", "gap": "kinship" },
      { "number": "第五条", "status": "needs_ontology", "gap": "state_organs" }
    ]
  },
  "articles": [
    { "number": "第一条", "text": "a" },
    { "number": "第二条", "text": "b" },
    { "number": "第三条", "text": "c" },
    { "number": "第四条", "text": "d" },
    { "number": "第五条", "text": "e" }
  ]
}"#;

fn run(command: &str) -> Output {
    run_in(None, command)
}

fn run_in(current_dir: Option<&Path>, command: &str) -> Output {
    let mut process = Command::new(env!("CARGO_BIN_EXE_std-deduce"));
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

/// Render a path exactly as the CLI's output escaping does.
fn escaped_path(path: &Path) -> String {
    escape_control(&path.display().to_string())
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
    let pack_line = format!(
        "cn.constitution 0.1.0  CN/CN  1982-12-04 起  community  {}",
        escaped_path(&temp.path().join("cn.constitution"))
    );
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(
        lines,
        vec![pack_line.as_str(), "  示例包", "  文件 2 个", UNLOCKED]
    );
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
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.len(), 5, "{out:?}");
    let good_line = format!(
        "cn.constitution 0.1.0  CN/CN  1982-12-04 起  community  {}",
        escaped_path(&temp.path().join("good"))
    );
    assert_eq!(lines[0], good_line);
    assert_eq!(lines[1], "  示例包");
    assert_eq!(lines[2], "  文件 2 个");
    let bad = temp.path().join("bad").join("lawpack.toml");
    assert!(
        lines[3].starts_with(&format!("{}：", escaped_path(&bad))),
        "{out:?}"
    );
    assert!(lines[3].contains("jurisdiction"), "{out:?}");
    assert_eq!(lines[4], LOCK_NOT_RUN);

    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个法律包清单错误"]
    );
}

#[test]
fn packs_fails_when_the_directory_does_not_exist() {
    let temp = TempDir::new("missing");
    let missing = temp.path().join("does-not-exist");

    let output = run(&format!(":packs {}", missing.display()));
    assert_exit(&output, ERROR);
    assert!(stdout(&output).is_empty(), "{}", stdout(&output));

    let err = stderr(&output);
    assert!(err.contains(&escaped_path(&missing)), "{err}");
    assert!(err.contains("无法读取法律包目录"), "{err}");
}

#[test]
fn packs_empty_directory_succeeds_and_says_none() {
    let temp = TempDir::new("empty");
    let output = run(&format!(":packs {}", temp.path().display()));
    assert_exit(&output, PROVED);
    assert_eq!(
        stdout(&output).lines().collect::<Vec<_>>(),
        ["没有找到法律包。", UNLOCKED]
    );
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

#[test]
fn packs_rejects_a_dangling_manifest_symlink() {
    let temp = TempDir::new("dangling-link");
    let dir = temp.path().join("pkg");
    fs::create_dir_all(&dir).unwrap();
    let link = dir.join("lawpack.toml");
    if !create_file_symlink(&temp.path().join("missing.toml"), &link) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }

    let output = run(&format!(":packs {}", temp.path().display()));
    assert_exit(&output, ERROR);

    let out = stdout(&output);
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.len(), 2, "{out:?}");
    assert!(
        lines[0].starts_with(&format!("{}：", escaped_path(&link))),
        "{out:?}"
    );
    assert!(lines[0].contains("符号链接"), "{out:?}");
    assert_eq!(lines[1], LOCK_NOT_RUN);
    assert!(!out.contains("没有找到法律包"), "{out:?}");
}

#[test]
fn packs_escapes_control_characters_in_a_description() {
    let temp = TempDir::new("escape-description");
    let manifest = r#"
[pack]
name = "cn.constitution"
version = "0.1.0"
jurisdiction = "CN"
territory = "CN"
effective_from = "1982-12-04"
description = "x\r\ty\u0007\nfake.pack 9.9.9  XX/XX  1970-01-01..未注明  /fake\u001B[31m"
"#;
    temp.pack("cn.constitution", manifest);

    let output = run(&format!(":packs {}", temp.path().display()));
    assert_exit(&output, PROVED);

    let out = stdout(&output);
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.len(), 3, "{out:?}");
    let pack_line = format!(
        "cn.constitution 0.1.0  CN/CN  1982-12-04 起  community  {}",
        escaped_path(&temp.path().join("cn.constitution"))
    );
    assert_eq!(lines[0], pack_line);
    assert_eq!(
        lines[1],
        "  x\\r\\ty\\u{0007}\\nfake.pack 9.9.9  XX/XX  1970-01-01..未注明  /fake\\u{001B}[31m"
    );
    assert_eq!(lines[2], UNLOCKED);
    assert!(!out.contains('\u{1b}'), "{out:?}");
    assert!(
        !lines.iter().any(|line| line.starts_with("fake.pack")),
        "{out:?}"
    );
}

#[test]
fn packs_escapes_control_characters_in_manifest_errors() {
    let temp = TempDir::new("escape-error");
    let manifest = r#"
[pack]
name = """bad
fake.pack 9.9.9  XX/XX  1970-01-01..未注明  /fake\u001B[31m"""
version = "1.0"
jurisdiction = "CN"
territory = "CN"
"#;
    temp.pack("bad", manifest);

    let output = run(&format!(":packs {}", temp.path().display()));
    assert_exit(&output, ERROR);

    let out = stdout(&output);
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.len(), 2, "{out:?}");
    let path = temp.path().join("bad").join("lawpack.toml");
    assert!(
        lines[0].starts_with(&format!("{}：", escaped_path(&path))),
        "{out:?}"
    );
    assert!(lines[0].contains("bad\\nfake.pack"), "{out:?}");
    assert!(lines[0].contains("\\u{001B}[31m"), "{out:?}");
    assert_eq!(lines[1], LOCK_NOT_RUN);
    assert!(!out.contains('\u{1b}'), "{out:?}");
    assert!(
        !lines.iter().any(|line| line.starts_with("fake.pack")),
        "{out:?}"
    );
}

#[test]
fn packs_escapes_control_characters_in_an_error_path() {
    let temp = TempDir::new("escape-path");
    let weird = temp.path().join("bad\nname\u{1b}[31m");

    let output = run(&format!(":packs {}", weird.display()));
    assert_exit(&output, ERROR);

    let err = stderr(&output);
    assert!(err.contains("bad\\nname\\u{001B}[31m"), "{err:?}");
    assert!(!err.contains('\u{1b}'), "{err:?}");
    assert!(!err.contains("bad\nname"), "{err:?}");
    assert_eq!(err.lines().count(), 1, "{err:?}");
}

#[test]
fn lock_writes_a_lock_that_packs_verifies() {
    let temp = TempDir::new("lock-ok");
    temp.pack("cn.constitution", VALID);
    temp.pack("cn.civil-code", OTHER);
    let root = temp.path();
    let lock_path = root.join("std.lock");

    let output = run(&format!(":lock {}", root.display()));
    assert_exit(&output, PROVED);
    assert_eq!(
        stdout(&output),
        format!("已写入 {}（2 个包）\n", escaped_path(&lock_path))
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
    let lock_text = fs::read_to_string(&lock_path).expect("the lock exists");
    assert!(lock_text.contains("lock_version = 1"), "{lock_text}");
    assert!(lock_text.contains("[[pack]]"), "{lock_text}");
    assert!(
        lock_text.contains("name = \"cn.civil-code\""),
        "{lock_text}"
    );
    assert!(
        lock_text.contains("name = \"cn.constitution\""),
        "{lock_text}"
    );
    assert_eq!(
        lock_text.matches("hash = \"sha256:").count(),
        2,
        "{lock_text}"
    );

    let output = run(&format!(":packs {}", root.display()));
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains("锁定校验：通过（2 个包）"), "{out}");
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn packs_fails_after_a_pack_changes() {
    let temp = TempDir::new("lock-changed");
    temp.pack("cn.constitution", VALID);
    let root = temp.path();

    let output = run(&format!(":lock {}", root.display()));
    assert_exit(&output, PROVED);

    // One changed byte changes the content hash but keeps the manifest valid.
    let manifest_path = root.join("cn.constitution").join("lawpack.toml");
    let changed = VALID.replace("1982-12-04", "1982-12-05");
    assert_eq!(changed.len(), VALID.len());
    assert_ne!(changed, VALID);
    fs::write(&manifest_path, changed).unwrap();

    let output = run(&format!(":packs {}", root.display()));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("哈希不符"), "{out}");
    assert!(!out.contains("锁定校验：通过"), "{out}");
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个锁定校验错误"]
    );
}

#[test]
fn packs_fails_when_the_locked_version_differs() {
    let temp = TempDir::new("lock-version");
    temp.pack("cn.constitution", VALID);
    let root = temp.path();
    let lock_path = root.join("std.lock");

    let output = run(&format!(":lock {}", root.display()));
    assert_exit(&output, PROVED);
    let text = fs::read_to_string(&lock_path).unwrap();
    let changed = text.replace("version = \"0.1.0\"", "version = \"0.2.0\"");
    assert_ne!(changed, text);
    fs::write(&lock_path, changed).unwrap();

    let output = run(&format!(":packs {}", root.display()));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("版本不符"), "{out}");
    assert!(out.contains("0.1.0"), "{out}");
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个锁定校验错误"]
    );
}

#[test]
fn packs_fails_when_a_locked_pack_is_missing() {
    let temp = TempDir::new("lock-missing-pack");
    temp.pack("cn.constitution", VALID);
    let root = temp.path();

    let output = run(&format!(":lock {}", root.display()));
    assert_exit(&output, PROVED);
    fs::remove_dir_all(root.join("cn.constitution")).unwrap();

    let output = run(&format!(":packs {}", root.display()));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("没有找到法律包。"), "{out}");
    assert!(out.contains("在目录中不存在"), "{out}");
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个锁定校验错误"]
    );
}

#[test]
fn packs_fails_when_a_pack_is_not_locked() {
    let temp = TempDir::new("lock-extra-pack");
    temp.pack("cn.constitution", VALID);
    let root = temp.path();

    let output = run(&format!(":lock {}", root.display()));
    assert_exit(&output, PROVED);
    temp.pack("cn.civil-code", OTHER);

    let output = run(&format!(":packs {}", root.display()));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("未锁定"), "{out}");
    assert!(out.contains("cn.civil-code"), "{out}");
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个锁定校验错误"]
    );
}

#[test]
fn lock_fails_and_writes_nothing_with_a_bad_pack() {
    let temp = TempDir::new("lock-bad-pack");
    temp.pack("good", VALID);
    temp.pack("bad", "[pack]\nname = \"bad.pack\"\nversion = \"1.0\"\n");
    let root = temp.path();

    let output = run(&format!(":lock {}", root.display()));
    assert_exit(&output, ERROR);
    assert!(
        !root.join("std.lock").exists(),
        "no partial lock is written"
    );
    let out = stdout(&output);
    assert!(out.contains("jurisdiction"), "{out}");
    assert!(
        stderr(&output).contains("std.lock 未写入"),
        "{}",
        stderr(&output)
    );
}

#[test]
fn lock_defaults_to_lawpacks_in_the_current_directory() {
    let temp = TempDir::new("lock-default");
    temp.pack("lawpacks/cn.constitution", VALID);

    let output = run_in(Some(temp.path()), ":lock");
    assert_exit(&output, PROVED);
    assert!(
        temp.path().join("lawpacks").join("std.lock").is_file(),
        "{}",
        stdout(&output)
    );
}

#[test]
fn lock_reports_a_missing_directory() {
    let temp = TempDir::new("lock-missing-dir");
    let missing = temp.path().join("does-not-exist");

    let output = run(&format!(":lock {}", missing.display()));
    assert_exit(&output, ERROR);
    assert!(stdout(&output).contains("无法读取法律包目录"), "{output:?}");
    assert!(
        stderr(&output).contains("std.lock 未写入"),
        "{}",
        stderr(&output)
    );
}

#[test]
fn packs_skips_lock_verification_when_a_manifest_is_bad() {
    let temp = TempDir::new("lock-skip-bad");
    temp.pack("good", VALID);
    let root = temp.path();
    let output = run(&format!(":lock {}", root.display()));
    assert_exit(&output, PROVED);

    temp.pack("bad", "[pack]\nname = \"bad.pack\"\nversion = \"1.0\"\n");
    let output = run(&format!(":packs {}", root.display()));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    let bad_manifest = root.join("bad").join("lawpack.toml");
    let reported = format!("{}：", escaped_path(&bad_manifest));
    assert_eq!(out.matches(&reported).count(), 1, "{out}");
    assert!(out.contains(LOCK_NOT_RUN), "{out}");
    assert!(!out.contains("锁定校验：通过"), "{out}");
    assert!(!out.contains("未锁定"), "{out}");
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个法律包清单错误"]
    );
}

#[test]
fn packs_fails_on_an_unsupported_lock_version() {
    let temp = TempDir::new("lock-bad-version");
    temp.pack("cn.constitution", VALID);
    let root = temp.path();
    let output = run(&format!(":lock {}", root.display()));
    assert_exit(&output, PROVED);

    let lock_path = root.join("std.lock");
    let text = fs::read_to_string(&lock_path).unwrap();
    let changed = text.replace("lock_version = 1", "lock_version = 2");
    assert_ne!(changed, text);
    fs::write(&lock_path, changed).unwrap();

    let output = run(&format!(":packs {}", root.display()));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("不支持的锁文件版本 2"), "{out}");
    assert!(!out.contains("锁定校验：通过"), "{out}");
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个锁定校验错误"]
    );
}

#[test]
fn packs_fails_on_a_malformed_lock() {
    let temp = TempDir::new("lock-malformed");
    temp.pack("cn.constitution", VALID);
    let root = temp.path();
    fs::write(root.join("std.lock"), "lock_version = \n").unwrap();

    let output = run(&format!(":packs {}", root.display()));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("锁文件解析失败"), "{out}");
    assert!(!out.contains("锁定校验：通过"), "{out}");
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个锁定校验错误"]
    );
}

#[test]
fn packs_displays_the_trust_level() {
    let temp = TempDir::new("trust");
    let manifest = VALID.replace(
        "description = \"示例包\"",
        "description = \"示例包\"\ntrust = \"official\"",
    );
    temp.pack("cn.constitution", &manifest);

    let output = run(&format!(":packs {}", temp.path().display()));
    assert_exit(&output, PROVED);
    let expected = format!(
        "cn.constitution 0.1.0  CN/CN  1982-12-04 起  official  {}",
        escaped_path(&temp.path().join("cn.constitution"))
    );
    assert!(
        stdout(&output).lines().any(|line| line == expected),
        "{}",
        stdout(&output)
    );
}

#[test]
fn packs_reads_a_linked_corpus_and_prints_its_coverage() {
    let temp = TempDir::new("corpus-coverage");
    let manifest = r#"
[pack]
name = "cn.test"
version = "0.1.0"
jurisdiction = "CN"
territory = "CN"
corpus = "cn.test/2018"
"#;
    temp.write_pack_at(&temp.path().join("lawpacks"), "cn.test", manifest);
    temp.corpus("cn.test", "2018", CORPUS_V2);

    let output = run(&format!(
        ":packs {}",
        temp.path().join("lawpacks").display()
    ));
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("cn.test 0.1.0  CN/CN  未注明  community  "),
        "{out}"
    );
    assert!(
        out.contains("  覆盖：形式化 1 / 部分 1 / 仅索引 1 / 待本体 2；开放概念 5"),
        "{out}"
    );
    assert!(
        out.contains("  本体缺口：kinship 1、state_organs 1"),
        "{out}"
    );
    assert!(out.contains(UNLOCKED), "{out}");
}

#[test]
fn packs_fails_when_a_linked_corpus_cannot_be_read() {
    let temp = TempDir::new("corpus-missing");
    let manifest = r#"
[pack]
name = "cn.test"
version = "0.1.0"
jurisdiction = "CN"
territory = "CN"
corpus = "cn.test/2018"
"#;
    temp.write_pack_at(&temp.path().join("lawpacks"), "cn.test", manifest);

    let output = run(&format!(
        ":packs {}",
        temp.path().join("lawpacks").display()
    ));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("无法读取语料文件"), "{out}");
    assert!(
        out.contains("cn.test") && out.contains("2018.json"),
        "{out}"
    );
    assert!(
        stderr(&output).contains("1 个语料读取错误"),
        "{}",
        stderr(&output)
    );
}

#[test]
fn packs_reports_an_invalid_corpus_link_in_the_manifest() {
    let temp = TempDir::new("corpus-invalid");
    let manifest = r#"
[pack]
name = "cn.test"
version = "0.1.0"
jurisdiction = "CN"
territory = "CN"
corpus = "cn.test"
"#;
    temp.pack("cn.test", manifest);

    let output = run(&format!(":packs {}", temp.path().display()));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(out.contains("corpus"), "{out}");
    assert!(out.contains(LOCK_NOT_RUN), "{out}");
}

#[test]
fn packs_fails_on_a_symlinked_lock() {
    let temp = TempDir::new("lock-symlinked");
    temp.pack("cn.constitution", VALID);
    let root = temp.path();
    let output = run(&format!(":lock {}", root.display()));
    assert_exit(&output, PROVED);

    let lock_path = root.join("std.lock");
    let target = root.join("lock-target");
    fs::rename(&lock_path, &target).unwrap();
    if !create_file_symlink(&target, &lock_path) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }

    let output = run(&format!(":packs {}", root.display()));
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    // Discovery already refuses a symbolic link at the root's direct children,
    // so the lock is reported there and verification is skipped. The library's
    // own lock-link refusal is covered by `verify_lock_rejects_a_symlinked_lock`.
    assert!(out.contains("符号链接"), "{out}");
    assert!(!out.contains("锁定校验：通过"), "{out}");
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个法律包清单错误"]
    );
}

#[test]
fn lock_keeps_an_existing_lock_when_a_pack_cannot_be_hashed() {
    let temp = TempDir::new("lock-no-overwrite");
    temp.pack("cn.constitution", VALID);
    let root = temp.path();
    let output = run(&format!(":lock {}", root.display()));
    assert_exit(&output, PROVED);
    let lock_path = root.join("std.lock");
    let original = fs::read(&lock_path).expect("the lock exists");

    let pack_dir = root.join("cn.constitution");
    let link = pack_dir.join("link.txt");
    if !create_file_symlink(&pack_dir.join("lawpack.toml"), &link) {
        eprintln!("skipping: cannot create a symbolic link");
        return;
    }

    let output = run(&format!(":lock {}", root.display()));
    assert_exit(&output, ERROR);
    assert!(stdout(&output).contains("符号链接"), "{output:?}");
    assert!(
        stderr(&output).contains("std.lock 未写入"),
        "{}",
        stderr(&output)
    );
    assert_eq!(fs::read(&lock_path).unwrap(), original);
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

    fn corpus(&self, law: &str, version: &str, text: &str) {
        let dir = self.path.join("law/corpus").join(law);
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
        fs::write(dir.join(format!("{version}.json")), text)
            .unwrap_or_else(|error| panic!("write corpus: {error}"));
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
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
